// Lean compiler output
// Module: Lean.Elab.Tactic.SimpTrace
// Imports: public import Lean.Elab.ElabRules public import Lean.Elab.Tactic.Simp public import Lean.Meta.Tactic.TryThis public import Lean.LibrarySuggestions.Basic
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LibrarySuggestions_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(64, 179, 144, 54, 113, 159, 205, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "locals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(87, 30, 159, 74, 102, 214, 91, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object*, lean_object*);
static const lean_array_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0_value;
static const lean_string_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected identifier"};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value)}};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0 = (const lean_object*)&l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6_value;
static const lean_array_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simp!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 96, 113, 105, 41, 106, 130, 154)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSimpTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpTrace___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 84, 117, 30, 74, 67, 74, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simp_all!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpAllTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpAllTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 138, 193, 72, 181, 178, 244, 77)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSimpAllTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 255, 119, 44, 227, 45, 220, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dsimpAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dsimp!"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dsimpTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dsimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 29, 147, 115, 237, 79, 62, 93)}};
static const lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalDSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 218, 74, 127, 38, 51, 185, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(lean_object* v_as_12_, size_t v_i_13_, size_t v_stop_14_, lean_object* v_b_15_){
_start:
{
lean_object* v___y_17_; uint8_t v___x_21_; 
v___x_21_ = lean_usize_dec_eq(v_i_13_, v_stop_14_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_uget_borrowed(v_as_12_, v_i_13_);
v___x_24_ = l_Lean_Syntax_getArg(v___x_23_, v___x_22_);
lean_inc(v___x_23_);
v___x_25_ = l_Lean_Syntax_getKind(v___x_23_);
if (lean_obj_tag(v___x_25_) == 1)
{
lean_object* v_pre_26_; 
v_pre_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_pre_26_);
if (lean_obj_tag(v_pre_26_) == 1)
{
lean_object* v_pre_27_; 
v_pre_27_ = lean_ctor_get(v_pre_26_, 0);
lean_inc(v_pre_27_);
if (lean_obj_tag(v_pre_27_) == 1)
{
lean_object* v_pre_28_; 
v_pre_28_ = lean_ctor_get(v_pre_27_, 0);
lean_inc(v_pre_28_);
if (lean_obj_tag(v_pre_28_) == 1)
{
lean_object* v_pre_29_; 
v_pre_29_ = lean_ctor_get(v_pre_28_, 0);
if (lean_obj_tag(v_pre_29_) == 0)
{
lean_object* v_str_30_; lean_object* v_str_31_; lean_object* v_str_32_; lean_object* v_str_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_str_30_ = lean_ctor_get(v___x_25_, 1);
lean_inc_ref(v_str_30_);
lean_dec_ref_known(v___x_25_, 2);
v_str_31_ = lean_ctor_get(v_pre_26_, 1);
lean_inc_ref(v_str_31_);
lean_dec_ref_known(v_pre_26_, 2);
v_str_32_ = lean_ctor_get(v_pre_27_, 1);
lean_inc_ref(v_str_32_);
lean_dec_ref_known(v_pre_27_, 2);
v_str_33_ = lean_ctor_get(v_pre_28_, 1);
lean_inc_ref(v_str_33_);
lean_dec_ref_known(v_pre_28_, 2);
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_35_ = lean_string_dec_eq(v_str_33_, v___x_34_);
lean_dec_ref(v_str_33_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
lean_dec_ref(v_str_32_);
lean_dec_ref(v_str_31_);
lean_dec_ref(v_str_30_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_36_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_36_;
goto v___jp_16_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_38_ = lean_string_dec_eq(v_str_32_, v___x_37_);
lean_dec_ref(v_str_32_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v_str_31_);
lean_dec_ref(v_str_30_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_39_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_39_;
goto v___jp_16_;
}
else
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_41_ = lean_string_dec_eq(v_str_31_, v___x_40_);
lean_dec_ref(v_str_31_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v_str_30_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_42_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_42_;
goto v___jp_16_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3));
v___x_44_ = lean_string_dec_eq(v_str_30_, v___x_43_);
lean_dec_ref(v_str_30_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_45_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_45_;
goto v___jp_16_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = l_Lean_Syntax_getArg(v___x_24_, v___x_46_);
v___x_48_ = l_Lean_Syntax_getKind(v___x_24_);
if (lean_obj_tag(v___x_48_) == 1)
{
lean_object* v_pre_49_; 
v_pre_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_pre_49_);
if (lean_obj_tag(v_pre_49_) == 1)
{
lean_object* v_pre_50_; 
v_pre_50_ = lean_ctor_get(v_pre_49_, 0);
lean_inc(v_pre_50_);
if (lean_obj_tag(v_pre_50_) == 1)
{
lean_object* v_pre_51_; 
v_pre_51_ = lean_ctor_get(v_pre_50_, 0);
lean_inc(v_pre_51_);
if (lean_obj_tag(v_pre_51_) == 1)
{
lean_object* v_pre_52_; 
v_pre_52_ = lean_ctor_get(v_pre_51_, 0);
if (lean_obj_tag(v_pre_52_) == 0)
{
lean_object* v_str_53_; lean_object* v_str_54_; lean_object* v_str_55_; lean_object* v_str_56_; uint8_t v___x_57_; 
v_str_53_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_str_53_);
lean_dec_ref_known(v___x_48_, 2);
v_str_54_ = lean_ctor_get(v_pre_49_, 1);
lean_inc_ref(v_str_54_);
lean_dec_ref_known(v_pre_49_, 2);
v_str_55_ = lean_ctor_get(v_pre_50_, 1);
lean_inc_ref(v_str_55_);
lean_dec_ref_known(v_pre_50_, 2);
v_str_56_ = lean_ctor_get(v_pre_51_, 1);
lean_inc_ref(v_str_56_);
lean_dec_ref_known(v_pre_51_, 2);
v___x_57_ = lean_string_dec_eq(v_str_56_, v___x_34_);
lean_dec_ref(v_str_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec_ref(v_str_55_);
lean_dec_ref(v_str_54_);
lean_dec_ref(v_str_53_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_58_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_58_;
goto v___jp_16_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = lean_string_dec_eq(v_str_55_, v___x_37_);
lean_dec_ref(v_str_55_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec_ref(v_str_54_);
lean_dec_ref(v_str_53_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_60_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_60_;
goto v___jp_16_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = lean_string_dec_eq(v_str_54_, v___x_40_);
lean_dec_ref(v_str_54_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec_ref(v_str_53_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_62_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_62_;
goto v___jp_16_;
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4));
v___x_64_ = lean_string_dec_eq(v_str_53_, v___x_63_);
lean_dec_ref(v_str_53_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_65_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_65_;
goto v___jp_16_;
}
else
{
lean_object* v___x_66_; lean_object* v_id_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_66_ = l_Lean_Syntax_getId(v___x_47_);
lean_dec(v___x_47_);
v_id_67_ = l_Lean_Name_eraseMacroScopes(v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6));
v___x_69_ = lean_name_eq(v_id_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8));
v___x_71_ = lean_name_eq(v_id_67_, v___x_70_);
lean_dec(v_id_67_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_inc(v___x_23_);
v___x_72_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_72_;
goto v___jp_16_;
}
else
{
v___y_17_ = v_b_15_;
goto v___jp_16_;
}
}
else
{
lean_dec(v_id_67_);
v___y_17_ = v_b_15_;
goto v___jp_16_;
}
}
}
}
}
}
else
{
lean_object* v___x_73_; 
lean_dec_ref_known(v_pre_51_, 2);
lean_dec_ref_known(v_pre_50_, 2);
lean_dec_ref_known(v_pre_49_, 2);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_73_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_73_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_74_; 
lean_dec_ref_known(v_pre_50_, 2);
lean_dec(v_pre_51_);
lean_dec_ref_known(v_pre_49_, 2);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_74_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_74_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_75_; 
lean_dec(v_pre_50_);
lean_dec_ref_known(v_pre_49_, 2);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_75_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_75_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_76_; 
lean_dec(v_pre_49_);
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_76_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_76_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_77_; 
lean_dec(v___x_48_);
lean_dec(v___x_47_);
lean_inc(v___x_23_);
v___x_77_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_77_;
goto v___jp_16_;
}
}
}
}
}
}
else
{
lean_object* v___x_78_; 
lean_dec_ref_known(v_pre_28_, 2);
lean_dec_ref_known(v_pre_27_, 2);
lean_dec_ref_known(v_pre_26_, 2);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_78_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_78_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec_ref_known(v_pre_27_, 2);
lean_dec(v_pre_28_);
lean_dec_ref_known(v_pre_26_, 2);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_79_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_79_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v_pre_27_);
lean_dec_ref_known(v_pre_26_, 2);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_80_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_80_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v_pre_26_);
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_81_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_81_;
goto v___jp_16_;
}
}
else
{
lean_object* v___x_82_; 
lean_dec(v___x_25_);
lean_dec(v___x_24_);
lean_inc(v___x_23_);
v___x_82_ = lean_array_push(v_b_15_, v___x_23_);
v___y_17_ = v___x_82_;
goto v___jp_16_;
}
}
else
{
return v_b_15_;
}
v___jp_16_:
{
size_t v___x_18_; size_t v___x_19_; 
v___x_18_ = ((size_t)1ULL);
v___x_19_ = lean_usize_add(v_i_13_, v___x_18_);
v_i_13_ = v___x_19_;
v_b_15_ = v___y_17_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_12_ = stack[0].m_obj;
size_t v_i_13_ = stack[1].m_num;
size_t v_stop_14_ = stack[2].m_num;
lean_object* v_b_15_ = stack[3].m_obj;
lean_object* v_res_83_;
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_as_12_, v_i_13_, v_stop_14_, v_b_15_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(lean_object* v_as_84_, lean_object* v_i_85_, lean_object* v_stop_86_, lean_object* v_b_87_){
_start:
{
size_t v_i_boxed_88_; size_t v_stop_boxed_89_; lean_object* v_res_90_; 
v_i_boxed_88_ = lean_unbox_usize(v_i_85_);
lean_dec(v_i_85_);
v_stop_boxed_89_ = lean_unbox_usize(v_stop_86_);
lean_dec(v_stop_86_);
v_res_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_as_84_, v_i_boxed_88_, v_stop_boxed_89_, v_b_87_);
lean_dec_ref(v_as_84_);
return v_res_90_;
}
}
lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(lean_object* v_cfg_93_){
_start:
{
lean_object* v___x_95_; lean_object* v_nullNode_96_; lean_object* v___y_98_; lean_object* v_configItems_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v_nullNode_96_ = l_Lean_Syntax_getArg(v_cfg_93_, v___x_95_);
v_configItems_102_ = l_Lean_Syntax_getArgs(v_nullNode_96_);
v___x_103_ = lean_array_get_size(v_configItems_102_);
v___x_104_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_105_ = lean_nat_dec_lt(v___x_95_, v___x_103_);
if (v___x_105_ == 0)
{
lean_dec_ref(v_configItems_102_);
v___y_98_ = v___x_104_;
goto v___jp_97_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_le(v___x_103_, v___x_103_);
if (v___x_106_ == 0)
{
if (v___x_105_ == 0)
{
lean_dec_ref(v_configItems_102_);
v___y_98_ = v___x_104_;
goto v___jp_97_;
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_103_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_102_, v___x_107_, v___x_108_, v___x_104_);
lean_dec_ref(v_configItems_102_);
v___y_98_ = v___x_109_;
goto v___jp_97_;
}
}
else
{
size_t v___x_110_; size_t v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((size_t)0ULL);
v___x_111_ = lean_usize_of_nat(v___x_103_);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_102_, v___x_110_, v___x_111_, v___x_104_);
lean_dec_ref(v_configItems_102_);
v___y_98_ = v___x_112_;
goto v___jp_97_;
}
}
v___jp_97_:
{
lean_object* v_newNullNode_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_newNullNode_99_ = l_Lean_Syntax_setArgs(v_nullNode_96_, v___y_98_);
v___x_100_ = l_Lean_Syntax_setArg(v_cfg_93_, v___x_95_, v_newNullNode_99_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_93_ = stack[0].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_93_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object* v_cfg_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_114_);
return v_res_116_;
}
}
lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object* v_cfg_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_117_);
return v___x_123_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_117_ = stack[0].m_obj;
lean_object* v_a_118_ = stack[1].m_obj;
lean_object* v_a_119_ = stack[2].m_obj;
lean_object* v_a_120_ = stack[3].m_obj;
lean_object* v_a_121_ = stack[4].m_obj;
lean_object* v_res_124_;
v_res_124_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
stack->m_obj
 = v_res_124_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object* v_cfg_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_131_;
}
}
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* v_stx_132_, lean_object* v_usedSimps_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_stx_139_; lean_object* v___x_140_; 
v_stx_139_ = l_Lean_Syntax_unsetTrailing(v_stx_132_);
v___x_140_ = l_Lean_Elab_Tactic_mkSimpOnly(v_stx_139_, v_usedSimps_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_140_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_140_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_mkSimpCallStx_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_132_ = stack[0].m_obj;
lean_object* v_usedSimps_133_ = stack[1].m_obj;
lean_object* v_a_134_ = stack[2].m_obj;
lean_object* v_a_135_ = stack[3].m_obj;
lean_object* v_a_136_ = stack[4].m_obj;
lean_object* v_a_137_ = stack[5].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_132_, v_usedSimps_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* v_stx_158_, lean_object* v_usedSimps_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_158_, v_usedSimps_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec_ref(v_usedSimps_159_);
return v_res_165_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
return v___x_168_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_172_;
v_res_172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v_res_174_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* v_00_u03b1_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_185_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_176_ = stack[1].m_obj;
lean_object* v___y_177_ = stack[2].m_obj;
lean_object* v___y_178_ = stack[3].m_obj;
lean_object* v___y_179_ = stack[4].m_obj;
lean_object* v___y_180_ = stack[5].m_obj;
lean_object* v___y_181_ = stack[6].m_obj;
lean_object* v___y_182_ = stack[7].m_obj;
lean_object* v___y_183_ = stack[8].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_box(0), v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(v_00_u03b1_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_197_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t v___x_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_box(v___x_198_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpTrace___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_198_ = stack[0].m_num;
lean_object* v_x_199_ = stack[1].m_obj;
lean_object* v___y_200_ = stack[2].m_obj;
lean_object* v___y_201_ = stack[3].m_obj;
lean_object* v___y_202_ = stack[4].m_obj;
lean_object* v___y_203_ = stack[5].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object* v___x_208_, lean_object* v_x_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
uint8_t v___x_33724__boxed_215_; lean_object* v_res_216_; 
v___x_33724__boxed_215_ = lean_unbox(v___x_208_);
v_res_216_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33724__boxed_215_, v_x_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v_x_209_);
return v_res_216_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* v___y_217_, lean_object* v___x_218_, uint8_t v___x_219_, lean_object* v___y_220_, lean_object* v_simprocs_221_, lean_object* v_discharge_x3f_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
if (lean_obj_tag(v___y_217_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_233_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_219_);
v___x_234_ = l_Lean_Elab_Tactic_simpLocation(v___y_220_, v_simprocs_221_, v_discharge_x3f_222_, v___x_233_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_234_;
}
else
{
lean_object* v_val_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_val_235_ = lean_ctor_get(v___y_217_, 0);
v___x_236_ = l_Lean_Elab_Tactic_expandLocation(v_val_235_);
v___x_237_ = l_Lean_Elab_Tactic_simpLocation(v___y_220_, v_simprocs_221_, v_discharge_x3f_222_, v___x_236_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_237_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpTrace___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_217_ = stack[0].m_obj;
lean_object* v___x_218_ = stack[1].m_obj;
uint8_t v___x_219_ = stack[2].m_num;
lean_object* v___y_220_ = stack[3].m_obj;
lean_object* v_simprocs_221_ = stack[4].m_obj;
lean_object* v_discharge_x3f_222_ = stack[5].m_obj;
lean_object* v___y_223_ = stack[6].m_obj;
lean_object* v___y_224_ = stack[7].m_obj;
lean_object* v___y_225_ = stack[8].m_obj;
lean_object* v___y_226_ = stack[9].m_obj;
lean_object* v___y_227_ = stack[10].m_obj;
lean_object* v___y_228_ = stack[11].m_obj;
lean_object* v___y_229_ = stack[12].m_obj;
lean_object* v___y_230_ = stack[13].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_217_, v___x_218_, v___x_219_, v___y_220_, v_simprocs_221_, v_discharge_x3f_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* v___y_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v___y_242_, lean_object* v_simprocs_243_, lean_object* v_discharge_x3f_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
uint8_t v___x_33767__boxed_254_; lean_object* v_res_255_; 
v___x_33767__boxed_254_ = lean_unbox(v___x_241_);
v_res_255_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_239_, v___x_240_, v___x_33767__boxed_254_, v___y_242_, v_simprocs_243_, v_discharge_x3f_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___x_240_);
lean_dec(v___y_239_);
return v_res_255_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Array_mkArray0___redArg();
return v___x_265_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object* v___x_266_, lean_object* v_as_x27_267_, lean_object* v_b_268_, lean_object* v___y_269_){
_start:
{
if (lean_obj_tag(v_as_x27_267_) == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v_b_268_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v_tail_273_; lean_object* v_ref_274_; uint8_t v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_head_272_ = lean_ctor_get(v_as_x27_267_, 0);
v_tail_273_ = lean_ctor_get(v_as_x27_267_, 1);
v_ref_274_ = lean_ctor_get(v___y_269_, 2);
v___x_275_ = 1;
v___x_276_ = 0;
v___x_277_ = l_Lean_SourceInfo_fromRef(v_ref_274_, v___x_276_);
v___x_278_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_279_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_280_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_277_);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_277_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_280_);
lean_inc(v_head_272_);
v___x_282_ = l_Lean_mkCIdentFrom(v___x_266_, v_head_272_, v___x_275_);
lean_inc_ref(v___x_281_);
v___x_283_ = l_Lean_Syntax_node3(v___x_277_, v___x_278_, v___x_281_, v___x_281_, v___x_282_);
v___x_284_ = lean_array_push(v_b_268_, v___x_283_);
v_as_x27_267_ = v_tail_273_;
v_b_268_ = v___x_284_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_266_ = stack[0].m_obj;
lean_object* v_as_x27_267_ = stack[1].m_obj;
lean_object* v_b_268_ = stack[2].m_obj;
lean_object* v___y_269_ = stack[3].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_266_, v_as_x27_267_, v_b_268_, v___y_269_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object* v___x_287_, lean_object* v_as_x27_288_, lean_object* v_b_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_287_, v_as_x27_288_, v_b_289_, v___y_290_);
lean_dec_ref(v___y_290_);
lean_dec(v_as_x27_288_);
lean_dec(v___x_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
return v___x_294_;
}
else
{
lean_object* v_head_295_; lean_object* v_tail_296_; lean_object* v_fst_297_; uint8_t v___x_298_; 
v_head_295_ = lean_ctor_get(v_x_293_, 0);
v_tail_296_ = lean_ctor_get(v_x_293_, 1);
v_fst_297_ = lean_ctor_get(v_head_295_, 0);
v___x_298_ = l_Lean_isPrivateName(v_fst_297_);
if (v___x_298_ == 0)
{
v_x_293_ = v_tail_296_;
goto _start;
}
else
{
lean_object* v___x_300_; 
lean_inc(v_head_295_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_head_295_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_301_);
lean_dec(v_x_301_);
return v_res_302_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object* v_opts_303_, lean_object* v_opt_304_){
_start:
{
lean_object* v_name_305_; lean_object* v_defValue_306_; lean_object* v_map_307_; lean_object* v___x_308_; 
v_name_305_ = lean_ctor_get(v_opt_304_, 0);
v_defValue_306_ = lean_ctor_get(v_opt_304_, 1);
v_map_307_ = lean_ctor_get(v_opts_303_, 0);
v___x_308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_307_, v_name_305_);
if (lean_obj_tag(v___x_308_) == 0)
{
uint8_t v___x_309_; 
v___x_309_ = lean_unbox(v_defValue_306_);
return v___x_309_;
}
else
{
lean_object* v_val_310_; 
v_val_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_308_, 1);
if (lean_obj_tag(v_val_310_) == 1)
{
uint8_t v_v_311_; 
v_v_311_ = lean_ctor_get_uint8(v_val_310_, 0);
lean_dec_ref_known(v_val_310_, 0);
return v_v_311_;
}
else
{
uint8_t v___x_312_; 
lean_dec(v_val_310_);
v___x_312_ = lean_unbox(v_defValue_306_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_303_ = stack[0].m_obj;
lean_object* v_opt_304_ = stack[1].m_obj;
uint8_t v_res_313_;
v_res_313_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_303_, v_opt_304_);
stack->m_num = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object* v_opts_314_, lean_object* v_opt_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_314_, v_opt_315_);
lean_dec_ref(v_opt_315_);
lean_dec_ref(v_opts_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object* v_opt_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_321_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_319_);
v___x_322_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_321_, v_opt_318_);
lean_dec_ref(v___x_321_);
v___x_323_ = lean_box(v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_318_ = stack[0].m_obj;
lean_object* v___y_319_ = stack[1].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_318_, v___y_319_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_326_, v___y_327_);
lean_dec_ref(v___y_327_);
lean_dec_ref(v_opt_326_);
return v_res_329_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; lean_object* v_env_337_; uint8_t v___x_338_; lean_object* v_env_339_; lean_object* v___x_340_; lean_object* v_toCold_341_; lean_object* v_mctx_342_; lean_object* v_lctx_343_; lean_object* v_options_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_336_ = lean_st_ref_get(v___y_334_);
v_env_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_env_337_);
lean_dec(v___x_336_);
v___x_338_ = 0;
v_env_339_ = l_Lean_Environment_setRecordingDeps(v_env_337_, v___x_338_);
v___x_340_ = lean_st_ref_get(v___y_332_);
v_toCold_341_ = lean_ctor_get(v___y_333_, 0);
v_mctx_342_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_mctx_342_);
lean_dec(v___x_340_);
v_lctx_343_ = lean_ctor_get(v___y_331_, 2);
v_options_344_ = lean_ctor_get(v_toCold_341_, 2);
lean_inc_ref(v_options_344_);
lean_inc_ref(v_lctx_343_);
v___x_345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_345_, 0, v_env_339_);
lean_ctor_set(v___x_345_, 1, v_mctx_342_);
lean_ctor_set(v___x_345_, 2, v_lctx_343_);
lean_ctor_set(v___x_345_, 3, v_options_344_);
v___x_346_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v_msgData_330_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_330_ = stack[0].m_obj;
lean_object* v___y_331_ = stack[1].m_obj;
lean_object* v___y_332_ = stack[2].m_obj;
lean_object* v___y_333_ = stack[3].m_obj;
lean_object* v___y_334_ = stack[4].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_355_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_363_, uint8_t v___y_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_365_) == 1)
{
lean_object* v_pre_366_; 
v_pre_366_ = lean_ctor_get(v_x_365_, 0);
switch(lean_obj_tag(v_pre_366_))
{
case 1:
{
lean_object* v_pre_367_; 
v_pre_367_ = lean_ctor_get(v_pre_366_, 0);
switch(lean_obj_tag(v_pre_367_))
{
case 0:
{
lean_object* v_str_368_; lean_object* v_str_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_str_368_ = lean_ctor_get(v_x_365_, 1);
v_str_369_ = lean_ctor_get(v_pre_366_, 1);
v___x_370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_371_ = lean_string_dec_eq(v_str_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_373_ = lean_string_dec_eq(v_str_369_, v___x_372_);
if (v___x_373_ == 0)
{
return v___x_373_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_375_ = lean_string_dec_eq(v_str_368_, v___x_374_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
return v_suppressElabErrors_363_;
}
}
}
else
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_377_ = lean_string_dec_eq(v_str_368_, v___x_376_);
if (v___x_377_ == 0)
{
return v___x_377_;
}
else
{
return v_suppressElabErrors_363_;
}
}
}
case 1:
{
lean_object* v_pre_378_; 
v_pre_378_ = lean_ctor_get(v_pre_367_, 0);
if (lean_obj_tag(v_pre_378_) == 0)
{
lean_object* v_str_379_; lean_object* v_str_380_; lean_object* v_str_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_str_379_ = lean_ctor_get(v_x_365_, 1);
v_str_380_ = lean_ctor_get(v_pre_366_, 1);
v_str_381_ = lean_ctor_get(v_pre_367_, 1);
v___x_382_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_383_ = lean_string_dec_eq(v_str_381_, v___x_382_);
if (v___x_383_ == 0)
{
return v___x_383_;
}
else
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_385_ = lean_string_dec_eq(v_str_380_, v___x_384_);
if (v___x_385_ == 0)
{
return v___x_385_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_387_ = lean_string_dec_eq(v_str_379_, v___x_386_);
if (v___x_387_ == 0)
{
return v___x_387_;
}
else
{
return v_suppressElabErrors_363_;
}
}
}
}
else
{
return v___y_364_;
}
}
default: 
{
return v___y_364_;
}
}
}
case 0:
{
lean_object* v_str_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_str_388_ = lean_ctor_get(v_x_365_, 1);
v___x_389_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_390_ = lean_string_dec_eq(v_str_388_, v___x_389_);
if (v___x_390_ == 0)
{
return v___x_390_;
}
else
{
return v_suppressElabErrors_363_;
}
}
default: 
{
return v___y_364_;
}
}
}
else
{
return v___y_364_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_363_ = stack[0].m_num;
uint8_t v___y_364_ = stack[1].m_num;
lean_object* v_x_365_ = stack[2].m_obj;
uint8_t v_res_391_;
v_res_391_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_363_, v___y_364_, v_x_365_);
stack->m_num = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_392_, lean_object* v___y_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_suppressElabErrors_boxed_395_; uint8_t v___y_34071__boxed_396_; uint8_t v_res_397_; lean_object* v_r_398_; 
v_suppressElabErrors_boxed_395_ = lean_unbox(v_suppressElabErrors_392_);
v___y_34071__boxed_396_ = lean_unbox(v___y_393_);
v_res_397_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_395_, v___y_34071__boxed_396_, v_x_394_);
lean_dec(v_x_394_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_400_, lean_object* v_msgData_401_, uint8_t v_severity_402_, uint8_t v_isSilent_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; uint8_t v___y_415_; uint8_t v___y_416_; lean_object* v_toCold_417_; lean_object* v___y_418_; lean_object* v___y_447_; lean_object* v___y_448_; uint8_t v___y_449_; lean_object* v___y_450_; uint8_t v___y_451_; uint8_t v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; uint8_t v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; uint8_t v___y_479_; lean_object* v___y_480_; uint8_t v___y_484_; uint8_t v___y_485_; uint8_t v___y_486_; uint8_t v___x_497_; uint8_t v___y_499_; uint8_t v___y_500_; uint8_t v___y_501_; uint8_t v___y_503_; uint8_t v___x_511_; 
v___x_497_ = 2;
v___x_511_ = l_Lean_instBEqMessageSeverity_beq(v_severity_402_, v___x_497_);
if (v___x_511_ == 0)
{
v___y_503_ = v___x_511_;
goto v___jp_502_;
}
else
{
uint8_t v___x_512_; 
lean_inc_ref(v_msgData_401_);
v___x_512_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_401_);
v___y_503_ = v___x_512_;
goto v___jp_502_;
}
v___jp_409_:
{
lean_object* v_currNamespace_419_; lean_object* v_openDecls_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_env_425_; lean_object* v_nextMacroScope_426_; lean_object* v_ngen_427_; lean_object* v_auxDeclNGen_428_; lean_object* v_traceState_429_; lean_object* v_cache_430_; lean_object* v_recordedDeps_431_; lean_object* v_messages_432_; lean_object* v_infoState_433_; lean_object* v_snapshotTasks_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
v_currNamespace_419_ = lean_ctor_get(v_toCold_417_, 4);
v_openDecls_420_ = lean_ctor_get(v_toCold_417_, 5);
lean_inc(v_openDecls_420_);
lean_inc(v_currNamespace_419_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_currNamespace_419_);
lean_ctor_set(v___x_421_, 1, v_openDecls_420_);
v___x_422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___y_413_);
lean_inc_ref(v___y_410_);
lean_inc_ref(v___y_414_);
v___x_423_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_423_, 0, v___y_414_);
lean_ctor_set(v___x_423_, 1, v___y_412_);
lean_ctor_set(v___x_423_, 2, v___y_411_);
lean_ctor_set(v___x_423_, 3, v___y_410_);
lean_ctor_set(v___x_423_, 4, v___x_422_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5, v___y_416_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5 + 1, v___y_415_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5 + 2, v_isSilent_403_);
v___x_424_ = lean_st_ref_take(v___y_418_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
v_nextMacroScope_426_ = lean_ctor_get(v___x_424_, 1);
v_ngen_427_ = lean_ctor_get(v___x_424_, 2);
v_auxDeclNGen_428_ = lean_ctor_get(v___x_424_, 3);
v_traceState_429_ = lean_ctor_get(v___x_424_, 4);
v_cache_430_ = lean_ctor_get(v___x_424_, 5);
v_recordedDeps_431_ = lean_ctor_get(v___x_424_, 6);
v_messages_432_ = lean_ctor_get(v___x_424_, 7);
v_infoState_433_ = lean_ctor_get(v___x_424_, 8);
v_snapshotTasks_434_ = lean_ctor_get(v___x_424_, 9);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_445_ == 0)
{
v___x_436_ = v___x_424_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snapshotTasks_434_);
lean_inc(v_infoState_433_);
lean_inc(v_messages_432_);
lean_inc(v_recordedDeps_431_);
lean_inc(v_cache_430_);
lean_inc(v_traceState_429_);
lean_inc(v_auxDeclNGen_428_);
lean_inc(v_ngen_427_);
lean_inc(v_nextMacroScope_426_);
lean_inc(v_env_425_);
lean_dec(v___x_424_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_box(0);
v___x_439_ = l_Lean_MessageLog_add(v___x_423_, v_messages_432_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 7, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_env_425_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_nextMacroScope_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_ngen_427_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_auxDeclNGen_428_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_traceState_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_cache_430_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_recordedDeps_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 7, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_444_, 8, v_infoState_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 9, v_snapshotTasks_434_);
v___x_441_ = v_reuseFailAlloc_444_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_st_ref_put(v___y_418_, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_438_);
return v___x_443_;
}
}
}
v___jp_446_:
{
lean_object* v_fileName_455_; lean_object* v_fileMap_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_472_; 
v_fileName_455_ = lean_ctor_get(v___y_453_, 0);
v_fileMap_456_ = lean_ctor_get(v___y_453_, 1);
v___x_457_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_401_);
v___x_458_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_457_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_472_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_472_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_472_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc_ref_n(v_fileMap_456_, 2);
v___x_463_ = l_Lean_FileMap_toPosition(v_fileMap_456_, v___y_450_);
lean_dec(v___y_450_);
v___x_464_ = l_Lean_FileMap_toPosition(v_fileMap_456_, v___y_454_);
lean_dec(v___y_454_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_449_ == 0)
{
lean_del_object(v___x_461_);
lean_dec_ref(v___y_447_);
v___y_410_ = v___x_466_;
v___y_411_ = v___x_465_;
v___y_412_ = v___x_463_;
v___y_413_ = v_a_459_;
v___y_414_ = v_fileName_455_;
v___y_415_ = v___y_451_;
v___y_416_ = v___y_452_;
v_toCold_417_ = v___y_448_;
v___y_418_ = v___y_407_;
goto v___jp_409_;
}
else
{
uint8_t v___x_467_; 
lean_inc(v_a_459_);
v___x_467_ = l_Lean_MessageData_hasTag(v___y_447_, v_a_459_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec_ref_known(v___x_465_, 1);
lean_dec_ref(v___x_463_);
lean_dec(v_a_459_);
v___x_468_ = lean_box(0);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_468_);
v___x_470_ = v___x_461_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
lean_del_object(v___x_461_);
v___y_410_ = v___x_466_;
v___y_411_ = v___x_465_;
v___y_412_ = v___x_463_;
v___y_413_ = v_a_459_;
v___y_414_ = v_fileName_455_;
v___y_415_ = v___y_451_;
v___y_416_ = v___y_452_;
v_toCold_417_ = v___y_448_;
v___y_418_ = v___y_407_;
goto v___jp_409_;
}
}
}
}
v___jp_473_:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Syntax_getTailPos_x3f(v___y_477_, v___y_479_);
lean_dec(v___y_477_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_inc(v___y_480_);
v___y_447_ = v___y_475_;
v___y_448_ = v___y_476_;
v___y_449_ = v___y_474_;
v___y_450_ = v___y_480_;
v___y_451_ = v___y_478_;
v___y_452_ = v___y_479_;
v___y_453_ = v___y_476_;
v___y_454_ = v___y_480_;
goto v___jp_446_;
}
else
{
lean_object* v_val_482_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v___x_481_, 1);
v___y_447_ = v___y_475_;
v___y_448_ = v___y_476_;
v___y_449_ = v___y_474_;
v___y_450_ = v___y_480_;
v___y_451_ = v___y_478_;
v___y_452_ = v___y_479_;
v___y_453_ = v___y_476_;
v___y_454_ = v_val_482_;
goto v___jp_446_;
}
}
v___jp_483_:
{
lean_object* v_toCold_487_; lean_object* v_ref_488_; uint8_t v_suppressElabErrors_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v_ref_493_; lean_object* v___x_494_; 
v_toCold_487_ = lean_ctor_get(v___y_406_, 0);
v_ref_488_ = lean_ctor_get(v___y_406_, 2);
v_suppressElabErrors_489_ = lean_ctor_get_uint8(v___y_406_, sizeof(void*)*3 + 2);
v___x_490_ = lean_box(v_suppressElabErrors_489_);
v___x_491_ = lean_box(v___y_484_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_492_, 0, v___x_490_);
lean_closure_set(v___f_492_, 1, v___x_491_);
v_ref_493_ = l_Lean_replaceRef(v_ref_400_, v_ref_488_);
v___x_494_ = l_Lean_Syntax_getPos_x3f(v_ref_493_, v___y_485_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___y_474_ = v_suppressElabErrors_489_;
v___y_475_ = v___f_492_;
v___y_476_ = v_toCold_487_;
v___y_477_ = v_ref_493_;
v___y_478_ = v___y_486_;
v___y_479_ = v___y_485_;
v___y_480_ = v___x_495_;
goto v___jp_473_;
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v___x_494_, 1);
v___y_474_ = v_suppressElabErrors_489_;
v___y_475_ = v___f_492_;
v___y_476_ = v_toCold_487_;
v___y_477_ = v_ref_493_;
v___y_478_ = v___y_486_;
v___y_479_ = v___y_485_;
v___y_480_ = v_val_496_;
goto v___jp_473_;
}
}
v___jp_498_:
{
if (v___y_501_ == 0)
{
v___y_484_ = v___y_499_;
v___y_485_ = v___y_500_;
v___y_486_ = v_severity_402_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___y_499_;
v___y_485_ = v___y_500_;
v___y_486_ = v___x_497_;
goto v___jp_483_;
}
}
v___jp_502_:
{
if (v___y_503_ == 0)
{
uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = 1;
v___x_505_ = l_Lean_instBEqMessageSeverity_beq(v_severity_402_, v___x_504_);
if (v___x_505_ == 0)
{
v___y_499_ = v___y_503_;
v___y_500_ = v___y_503_;
v___y_501_ = v___x_505_;
goto v___jp_498_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_406_);
v___x_507_ = l_Lean_warningAsError;
v___x_508_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_506_, v___x_507_);
lean_dec_ref(v___x_506_);
v___y_499_ = v___y_503_;
v___y_500_ = v___y_503_;
v___y_501_ = v___x_508_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref(v_msgData_401_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_400_ = stack[0].m_obj;
lean_object* v_msgData_401_ = stack[1].m_obj;
uint8_t v_severity_402_ = stack[2].m_num;
uint8_t v_isSilent_403_ = stack[3].m_num;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v___y_405_ = stack[5].m_obj;
lean_object* v___y_406_ = stack[6].m_obj;
lean_object* v___y_407_ = stack[7].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_400_, v_msgData_401_, v_severity_402_, v_isSilent_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_514_, lean_object* v_msgData_515_, lean_object* v_severity_516_, lean_object* v_isSilent_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_severity_boxed_523_; uint8_t v_isSilent_boxed_524_; lean_object* v_res_525_; 
v_severity_boxed_523_ = lean_unbox(v_severity_516_);
v_isSilent_boxed_524_ = lean_unbox(v_isSilent_517_);
v_res_525_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_514_, v_msgData_515_, v_severity_boxed_523_, v_isSilent_boxed_524_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v_ref_514_);
return v_res_525_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_526_, uint8_t v_severity_527_, uint8_t v_isSilent_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_ref_538_; lean_object* v___x_539_; 
v_ref_538_ = lean_ctor_get(v___y_535_, 2);
v___x_539_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_538_, v_msgData_526_, v_severity_527_, v_isSilent_528_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
return v___x_539_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_526_ = stack[0].m_obj;
uint8_t v_severity_527_ = stack[1].m_num;
uint8_t v_isSilent_528_ = stack[2].m_num;
lean_object* v___y_529_ = stack[3].m_obj;
lean_object* v___y_530_ = stack[4].m_obj;
lean_object* v___y_531_ = stack[5].m_obj;
lean_object* v___y_532_ = stack[6].m_obj;
lean_object* v___y_533_ = stack[7].m_obj;
lean_object* v___y_534_ = stack[8].m_obj;
lean_object* v___y_535_ = stack[9].m_obj;
lean_object* v___y_536_ = stack[10].m_obj;
lean_object* v_res_540_;
v_res_540_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_526_, v_severity_527_, v_isSilent_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_541_, lean_object* v_severity_542_, lean_object* v_isSilent_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
uint8_t v_severity_boxed_553_; uint8_t v_isSilent_boxed_554_; lean_object* v_res_555_; 
v_severity_boxed_553_ = lean_unbox(v_severity_542_);
v_isSilent_boxed_554_ = lean_unbox(v_isSilent_543_);
v_res_555_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_541_, v_severity_boxed_553_, v_isSilent_boxed_554_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_555_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v___x_566_ = 1;
v___x_567_ = 0;
v___x_568_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_556_, v___x_566_, v___x_567_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_568_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_556_ = stack[0].m_obj;
lean_object* v___y_557_ = stack[1].m_obj;
lean_object* v___y_558_ = stack[2].m_obj;
lean_object* v___y_559_ = stack[3].m_obj;
lean_object* v___y_560_ = stack[4].m_obj;
lean_object* v___y_561_ = stack[5].m_obj;
lean_object* v___y_562_ = stack[6].m_obj;
lean_object* v___y_563_ = stack[7].m_obj;
lean_object* v___y_564_ = stack[8].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_620_; 
v___x_597_ = lean_st_ref_get(v___y_595_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_597_);
v___x_599_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_600_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_599_, v___y_594_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_620_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_620_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_620_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
uint8_t v_isExporting_610_; 
v_isExporting_610_ = lean_ctor_get_uint8(v_env_598_, sizeof(void*)*13);
lean_dec_ref(v_env_598_);
if (v_isExporting_610_ == 0)
{
lean_dec(v_a_601_);
lean_dec(v_id_587_);
goto v___jp_605_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = l_Lean_isPrivateName(v_id_587_);
if (v___x_611_ == 0)
{
lean_dec(v_a_601_);
lean_dec(v_id_587_);
goto v___jp_605_;
}
else
{
uint8_t v___x_612_; 
v___x_612_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
if (v___x_612_ == 0)
{
lean_dec(v_id_587_);
goto v___jp_605_;
}
else
{
lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_del_object(v___x_603_);
v___x_613_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_614_ = 0;
v___x_615_ = l_Lean_MessageData_ofConstName(v_id_587_, v___x_614_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_618_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
return v___x_619_;
}
}
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_box(0);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_606_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_587_ = stack[0].m_obj;
lean_object* v___y_588_ = stack[1].m_obj;
lean_object* v___y_589_ = stack[2].m_obj;
lean_object* v___y_590_ = stack[3].m_obj;
lean_object* v___y_591_ = stack[4].m_obj;
lean_object* v___y_592_ = stack[5].m_obj;
lean_object* v___y_593_ = stack[6].m_obj;
lean_object* v___y_594_ = stack[7].m_obj;
lean_object* v___y_595_ = stack[8].m_obj;
lean_object* v_res_621_;
v_res_621_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_632_;
}
}
lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_633_, uint8_t v_enableLog_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; lean_object* v_toCold_645_; lean_object* v_env_646_; lean_object* v_currNamespace_647_; lean_object* v_openDecls_648_; lean_object* v___x_649_; lean_object* v_res_650_; lean_object* v___x_651_; 
v___x_644_ = lean_st_ref_get(v___y_642_);
v_toCold_645_ = lean_ctor_get(v___y_641_, 0);
v_env_646_ = lean_ctor_get(v___x_644_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_644_);
v_currNamespace_647_ = lean_ctor_get(v_toCold_645_, 4);
v_openDecls_648_ = lean_ctor_get(v_toCold_645_, 5);
v___x_649_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_641_);
lean_inc(v_openDecls_648_);
lean_inc(v_currNamespace_647_);
v_res_650_ = l_Lean_ResolveName_resolveGlobalName(v_env_646_, v___x_649_, v_currNamespace_647_, v_openDecls_648_, v_id_633_);
lean_dec_ref(v___x_649_);
v___x_651_ = lean_st_ref_get(v___y_642_);
if (v_enableLog_634_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_651_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_res_650_);
return v___x_652_;
}
else
{
lean_object* v_env_653_; uint8_t v_isExporting_654_; 
v_env_653_ = lean_ctor_get(v___x_651_, 0);
lean_inc_ref(v_env_653_);
lean_dec(v___x_651_);
v_isExporting_654_ = lean_ctor_get_uint8(v_env_653_, sizeof(void*)*13);
lean_dec_ref(v_env_653_);
if (v_isExporting_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_res_650_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_650_);
if (lean_obj_tag(v___x_656_) == 1)
{
lean_object* v_val_657_; lean_object* v_fst_658_; lean_object* v___x_659_; 
v_val_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v___x_656_, 1);
v_fst_658_ = lean_ctor_get(v_val_657_, 0);
lean_inc(v_fst_658_);
lean_dec(v_val_657_);
v___x_659_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_658_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_659_, 0);
lean_dec(v_unused_667_);
v___x_661_ = v___x_659_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_dec(v___x_659_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_res_650_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_res_650_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec(v_res_650_);
v_a_668_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_659_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v___x_676_; 
lean_dec(v___x_656_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_res_650_);
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_633_ = stack[0].m_obj;
uint8_t v_enableLog_634_ = stack[1].m_num;
lean_object* v___y_635_ = stack[2].m_obj;
lean_object* v___y_636_ = stack[3].m_obj;
lean_object* v___y_637_ = stack[4].m_obj;
lean_object* v___y_638_ = stack[5].m_obj;
lean_object* v___y_639_ = stack[6].m_obj;
lean_object* v___y_640_ = stack[7].m_obj;
lean_object* v___y_641_ = stack[8].m_obj;
lean_object* v___y_642_ = stack[9].m_obj;
lean_object* v_res_677_;
v_res_677_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_633_, v_enableLog_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_678_, lean_object* v_enableLog_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_enableLog_boxed_689_; lean_object* v_res_690_; 
v_enableLog_boxed_689_ = lean_unbox(v_enableLog_679_);
v_res_690_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_678_, v_enableLog_boxed_689_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
if (lean_obj_tag(v_a_691_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = l_List_reverse___redArg(v_a_692_);
return v___x_693_;
}
else
{
lean_object* v_head_694_; lean_object* v_tail_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_706_; 
v_head_694_ = lean_ctor_get(v_a_691_, 0);
v_tail_695_ = lean_ctor_get(v_a_691_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_a_691_);
if (v_isSharedCheck_706_ == 0)
{
v___x_697_ = v_a_691_;
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_tail_695_);
lean_inc(v_head_694_);
lean_dec(v_a_691_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_snd_699_; uint8_t v___x_700_; 
v_snd_699_ = lean_ctor_get(v_head_694_, 1);
v___x_700_ = l_List_isEmpty___redArg(v_snd_699_);
if (v___x_700_ == 0)
{
lean_del_object(v___x_697_);
lean_dec(v_head_694_);
v_a_691_ = v_tail_695_;
goto _start;
}
else
{
lean_object* v___x_703_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_a_692_);
v___x_703_ = v___x_697_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_head_694_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_a_692_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_a_691_ = v_tail_695_;
v_a_692_ = v___x_703_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
if (lean_obj_tag(v_a_707_) == 0)
{
lean_object* v___x_709_; 
v___x_709_ = l_List_reverse___redArg(v_a_708_);
return v___x_709_;
}
else
{
lean_object* v_head_710_; lean_object* v_tail_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_720_; 
v_head_710_ = lean_ctor_get(v_a_707_, 0);
v_tail_711_ = lean_ctor_get(v_a_707_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_707_);
if (v_isSharedCheck_720_ == 0)
{
v___x_713_ = v_a_707_;
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_tail_711_);
lean_inc(v_head_710_);
lean_dec(v_a_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_fst_715_; lean_object* v___x_717_; 
v_fst_715_ = lean_ctor_get(v_head_710_, 0);
lean_inc(v_fst_715_);
lean_dec(v_head_710_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v_a_708_);
lean_ctor_set(v___x_713_, 0, v_fst_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_a_708_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_a_707_ = v_tail_711_;
v_a_708_ = v___x_717_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_ref_727_; lean_object* v___x_728_; lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
v_ref_727_ = lean_ctor_get(v___y_724_, 2);
v___x_728_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_737_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_inc(v_ref_727_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_ref_727_);
lean_ctor_set(v___x_733_, 1, v_a_729_);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 1);
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_721_ = stack[0].m_obj;
lean_object* v___y_722_ = stack[1].m_obj;
lean_object* v___y_723_ = stack[2].m_obj;
lean_object* v___y_724_ = stack[3].m_obj;
lean_object* v___y_725_ = stack[4].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_toCold_757_; lean_object* v_currRecDepth_758_; lean_object* v_ref_759_; uint16_t v_optionFlags_760_; uint8_t v_suppressElabErrors_761_; uint8_t v_isRecordingDeps_762_; lean_object* v_ref_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_toCold_757_ = lean_ctor_get(v___y_754_, 0);
v_currRecDepth_758_ = lean_ctor_get(v___y_754_, 1);
v_ref_759_ = lean_ctor_get(v___y_754_, 2);
v_optionFlags_760_ = lean_ctor_get_uint16(v___y_754_, sizeof(void*)*3);
v_suppressElabErrors_761_ = lean_ctor_get_uint8(v___y_754_, sizeof(void*)*3 + 2);
v_isRecordingDeps_762_ = lean_ctor_get_uint8(v___y_754_, sizeof(void*)*3 + 3);
v_ref_763_ = l_Lean_replaceRef(v_ref_746_, v_ref_759_);
lean_inc(v_currRecDepth_758_);
lean_inc_ref(v_toCold_757_);
v___x_764_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_764_, 0, v_toCold_757_);
lean_ctor_set(v___x_764_, 1, v_currRecDepth_758_);
lean_ctor_set(v___x_764_, 2, v_ref_763_);
lean_ctor_set_uint16(v___x_764_, sizeof(void*)*3, v_optionFlags_760_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*3 + 2, v_suppressElabErrors_761_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*3 + 3, v_isRecordingDeps_762_);
v___x_765_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_747_, v___y_752_, v___y_753_, v___x_764_, v___y_755_);
lean_dec_ref_known(v___x_764_, 3);
return v___x_765_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_746_ = stack[0].m_obj;
lean_object* v_msg_747_ = stack[1].m_obj;
lean_object* v___y_748_ = stack[2].m_obj;
lean_object* v___y_749_ = stack[3].m_obj;
lean_object* v___y_750_ = stack[4].m_obj;
lean_object* v___y_751_ = stack[5].m_obj;
lean_object* v___y_752_ = stack[6].m_obj;
lean_object* v___y_753_ = stack[7].m_obj;
lean_object* v___y_754_ = stack[8].m_obj;
lean_object* v___y_755_ = stack[9].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_746_, v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_767_, lean_object* v_msg_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_767_, v_msg_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v_ref_767_);
return v_res_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
lean_ctor_set(v___x_785_, 3, v___x_784_);
lean_ctor_set(v___x_785_, 4, v___x_783_);
lean_ctor_set(v___x_785_, 5, v___x_783_);
lean_ctor_set(v___x_785_, 6, v___x_783_);
lean_ctor_set(v___x_785_, 7, v___x_783_);
lean_ctor_set(v___x_785_, 8, v___x_783_);
lean_ctor_set(v___x_785_, 9, v___x_783_);
lean_ctor_set(v___x_785_, 10, v___x_783_);
lean_ctor_set(v___x_785_, 11, v___x_782_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_unsigned_to_nat(32u);
v___x_787_ = lean_mk_empty_array_with_capacity(v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_789_ = ((size_t)5ULL);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_unsigned_to_nat(32u);
v___x_792_ = lean_mk_empty_array_with_capacity(v___x_791_);
v___x_793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_794_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_792_);
lean_ctor_set(v___x_794_, 2, v___x_790_);
lean_ctor_set(v___x_794_, 3, v___x_790_);
lean_ctor_set_usize(v___x_794_, 4, v___x_789_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = lean_box(1);
v___x_796_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
lean_ctor_set(v___x_798_, 2, v___x_795_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20));
v___x_822_ = l_Lean_stringToMessageData(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_832_, lean_object* v_declHint_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_env_838_; uint8_t v___x_839_; 
v___x_836_ = lean_box(0);
v___x_837_ = lean_st_ref_get(v___y_834_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = l_Lean_Name_isAnonymous(v_declHint_833_);
if (v___x_839_ == 0)
{
uint8_t v_isExporting_840_; 
v_isExporting_840_ = lean_ctor_get_uint8(v_env_838_, sizeof(void*)*13);
if (v_isExporting_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec_ref(v_env_838_);
lean_dec(v_declHint_833_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_msg_832_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; uint8_t v___x_843_; 
lean_inc_ref(v_env_838_);
v___x_842_ = l_Lean_Environment_setExporting(v_env_838_, v___x_839_);
lean_inc(v_declHint_833_);
lean_inc_ref(v___x_842_);
v___x_843_ = l_Lean_Environment_contains(v___x_842_, v_declHint_833_, v_isExporting_840_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v___x_842_);
lean_dec_ref(v_env_838_);
lean_dec(v_declHint_833_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_msg_832_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_c_850_; lean_object* v___x_851_; 
v___x_845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_847_ = l_Lean_Options_empty;
v___x_848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_848_, 0, v___x_842_);
lean_ctor_set(v___x_848_, 1, v___x_845_);
lean_ctor_set(v___x_848_, 2, v___x_846_);
lean_ctor_set(v___x_848_, 3, v___x_847_);
lean_inc(v_declHint_833_);
v___x_849_ = l_Lean_MessageData_ofConstName(v_declHint_833_, v___x_839_);
v_c_850_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_850_, 0, v___x_848_);
lean_ctor_set(v_c_850_, 1, v___x_849_);
v___x_851_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_838_, v_declHint_833_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_env_838_);
lean_dec(v_declHint_833_);
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_c_850_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_note(v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v_msg_832_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_915_; 
v_val_859_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_915_ == 0)
{
v___x_861_ = v___x_851_;
v_isShared_862_ = v_isSharedCheck_915_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_val_859_);
lean_dec(v___x_851_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_915_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v_modules_864_; lean_object* v_moduleNames_865_; lean_object* v_mod_866_; uint8_t v___y_868_; uint8_t v___x_898_; 
v___x_863_ = l_Lean_Environment_header(v_env_838_);
lean_dec_ref(v_env_838_);
v_modules_864_ = lean_ctor_get(v___x_863_, 3);
lean_inc_ref(v_modules_864_);
v_moduleNames_865_ = lean_ctor_get(v___x_863_, 4);
lean_inc_ref(v_moduleNames_865_);
lean_dec_ref(v___x_863_);
v_mod_866_ = lean_array_get(v___x_836_, v_moduleNames_865_, v_val_859_);
lean_dec_ref(v_moduleNames_865_);
v___x_898_ = l_Lean_isPrivateName(v_declHint_833_);
lean_dec(v_declHint_833_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_array_get_size(v_modules_864_);
v___x_900_ = lean_nat_dec_lt(v_val_859_, v___x_899_);
if (v___x_900_ == 0)
{
lean_dec_ref(v_modules_864_);
lean_dec(v_val_859_);
v___y_868_ = v___x_898_;
goto v___jp_867_;
}
else
{
lean_object* v___x_901_; lean_object* v_toImport_902_; uint8_t v_isExported_903_; 
v___x_901_ = lean_array_fget(v_modules_864_, v_val_859_);
lean_dec(v_val_859_);
lean_dec_ref(v_modules_864_);
v_toImport_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref(v_toImport_902_);
lean_dec(v___x_901_);
v_isExported_903_ = lean_ctor_get_uint8(v_toImport_902_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_902_);
v___y_868_ = v_isExported_903_;
goto v___jp_867_;
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v_modules_864_);
lean_del_object(v___x_861_);
lean_dec(v_val_859_);
v___x_904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_c_850_);
v___x_906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_MessageData_ofName(v_mod_866_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_MessageData_note(v___x_911_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v_msg_832_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
v___jp_867_:
{
if (v___y_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_c_850_);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_MessageData_ofName(v_mod_866_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_MessageData_note(v___x_876_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v_msg_832_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 0);
lean_ctor_set(v___x_861_, 0, v___x_878_);
v___x_880_ = v___x_861_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_c_850_);
v___x_884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_MessageData_ofName(v_mod_866_);
lean_inc_ref(v___x_886_);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_886_);
v___x_891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_MessageData_note(v___x_892_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v_msg_832_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 0);
lean_ctor_set(v___x_861_, 0, v___x_894_);
v___x_896_ = v___x_861_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
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
lean_object* v___x_916_; 
lean_dec_ref(v_env_838_);
lean_dec(v_declHint_833_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v_msg_832_);
return v___x_916_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_832_ = stack[0].m_obj;
lean_object* v_declHint_833_ = stack[1].m_obj;
lean_object* v___y_834_ = stack[2].m_obj;
lean_object* v_res_917_;
v_res_917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_832_, v_declHint_833_, v___y_834_);
stack->m_obj
 = v_res_917_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_918_, lean_object* v_declHint_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_918_, v_declHint_919_, v___y_920_);
lean_dec(v___y_920_);
return v_res_922_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_923_, lean_object* v_declHint_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_944_; 
v___x_934_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_923_, v_declHint_924_, v___y_932_);
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_944_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_944_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_944_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_939_ = l_Lean_unknownIdentifierMessageTag;
v___x_940_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_923_ = stack[0].m_obj;
lean_object* v_declHint_924_ = stack[1].m_obj;
lean_object* v___y_925_ = stack[2].m_obj;
lean_object* v___y_926_ = stack[3].m_obj;
lean_object* v___y_927_ = stack[4].m_obj;
lean_object* v___y_928_ = stack[5].m_obj;
lean_object* v___y_929_ = stack[6].m_obj;
lean_object* v___y_930_ = stack[7].m_obj;
lean_object* v___y_931_ = stack[8].m_obj;
lean_object* v___y_932_ = stack[9].m_obj;
lean_object* v_res_945_;
v_res_945_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_923_, v_declHint_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
stack->m_obj
 = v_res_945_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_946_, lean_object* v_declHint_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_946_, v_declHint_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_957_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_958_, lean_object* v_msg_959_, lean_object* v_declHint_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_a_971_; lean_object* v___x_972_; 
v___x_970_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_959_, v_declHint_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_958_, v_a_971_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_972_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_958_ = stack[0].m_obj;
lean_object* v_msg_959_ = stack[1].m_obj;
lean_object* v_declHint_960_ = stack[2].m_obj;
lean_object* v___y_961_ = stack[3].m_obj;
lean_object* v___y_962_ = stack[4].m_obj;
lean_object* v___y_963_ = stack[5].m_obj;
lean_object* v___y_964_ = stack[6].m_obj;
lean_object* v___y_965_ = stack[7].m_obj;
lean_object* v___y_966_ = stack[8].m_obj;
lean_object* v___y_967_ = stack[9].m_obj;
lean_object* v___y_968_ = stack[10].m_obj;
lean_object* v_res_973_;
v_res_973_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_958_, v_msg_959_, v_declHint_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_974_, lean_object* v_msg_975_, lean_object* v_declHint_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_974_, v_msg_975_, v_declHint_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_ref_974_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_993_, lean_object* v_constName_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1004_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_1005_ = 0;
lean_inc(v_constName_994_);
v___x_1006_ = l_Lean_MessageData_ofConstName(v_constName_994_, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1004_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_993_, v___x_1009_, v_constName_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1010_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_993_ = stack[0].m_obj;
lean_object* v_constName_994_ = stack[1].m_obj;
lean_object* v___y_995_ = stack[2].m_obj;
lean_object* v___y_996_ = stack[3].m_obj;
lean_object* v___y_997_ = stack[4].m_obj;
lean_object* v___y_998_ = stack[5].m_obj;
lean_object* v___y_999_ = stack[6].m_obj;
lean_object* v___y_1000_ = stack[7].m_obj;
lean_object* v___y_1001_ = stack[8].m_obj;
lean_object* v___y_1002_ = stack[9].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_993_, v_constName_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_1012_, lean_object* v_constName_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_1012_, v_constName_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v_ref_1012_);
return v_res_1023_;
}
}
lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_1024_, lean_object* v_cs_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; lean_object* v_cs_1036_; uint8_t v___x_1040_; 
v___x_1035_ = lean_box(0);
v_cs_1036_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_1025_, v___x_1035_);
v___x_1040_ = l_List_isEmpty___redArg(v_cs_1036_);
if (v___x_1040_ == 0)
{
lean_dec(v_n_1024_);
goto v___jp_1037_;
}
else
{
lean_object* v_ref_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_cs_1036_);
v_ref_1041_ = lean_ctor_get(v___y_1032_, 2);
v___x_1042_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_1041_, v_n_1024_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
v___jp_1037_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_1036_, v___x_1035_);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
LEAN_EXPORT void l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1024_ = stack[0].m_obj;
lean_object* v_cs_1025_ = stack[1].m_obj;
lean_object* v___y_1026_ = stack[2].m_obj;
lean_object* v___y_1027_ = stack[3].m_obj;
lean_object* v___y_1028_ = stack[4].m_obj;
lean_object* v___y_1029_ = stack[5].m_obj;
lean_object* v___y_1030_ = stack[6].m_obj;
lean_object* v___y_1031_ = stack[7].m_obj;
lean_object* v___y_1032_ = stack[8].m_obj;
lean_object* v___y_1033_ = stack[9].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1024_, v_cs_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1052_, lean_object* v_cs_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1052_, v_cs_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1063_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = 1;
lean_inc(v_n_1064_);
v___x_1075_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1064_, v___x_1074_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1064_, v_a_1076_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1077_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_n_1064_);
v_a_1078_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1075_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1064_ = stack[0].m_obj;
lean_object* v___y_1065_ = stack[1].m_obj;
lean_object* v___y_1066_ = stack[2].m_obj;
lean_object* v___y_1067_ = stack[3].m_obj;
lean_object* v___y_1068_ = stack[4].m_obj;
lean_object* v___y_1069_ = stack[5].m_obj;
lean_object* v___y_1070_ = stack[6].m_obj;
lean_object* v___y_1071_ = stack[7].m_obj;
lean_object* v___y_1072_ = stack[8].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
if (lean_obj_tag(v_a_1098_) == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_array_to_list(v_a_1099_);
return v___x_1100_;
}
else
{
lean_object* v_head_1101_; 
v_head_1101_ = lean_ctor_get(v_a_1098_, 0);
if (lean_obj_tag(v_head_1101_) == 1)
{
lean_object* v_fields_1102_; 
v_fields_1102_ = lean_ctor_get(v_head_1101_, 1);
if (lean_obj_tag(v_fields_1102_) == 0)
{
lean_object* v_tail_1103_; lean_object* v_n_1104_; lean_object* v___x_1105_; 
lean_inc_ref(v_head_1101_);
v_tail_1103_ = lean_ctor_get(v_a_1098_, 1);
lean_inc(v_tail_1103_);
lean_dec_ref_known(v_a_1098_, 2);
v_n_1104_ = lean_ctor_get(v_head_1101_, 0);
lean_inc(v_n_1104_);
lean_dec_ref_known(v_head_1101_, 2);
v___x_1105_ = lean_array_push(v_a_1099_, v_n_1104_);
v_a_1098_ = v_tail_1103_;
v_a_1099_ = v___x_1105_;
goto _start;
}
else
{
lean_object* v_tail_1107_; 
v_tail_1107_ = lean_ctor_get(v_a_1098_, 1);
lean_inc(v_tail_1107_);
lean_dec_ref_known(v_a_1098_, 2);
v_a_1098_ = v_tail_1107_;
goto _start;
}
}
else
{
lean_object* v_tail_1109_; 
v_tail_1109_ = lean_ctor_get(v_a_1098_, 1);
lean_inc(v_tail_1109_);
lean_dec_ref_known(v_a_1098_, 2);
v_a_1098_ = v_tail_1109_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1117_ = l_Lean_MessageData_ofFormat(v___x_1116_);
return v___x_1117_;
}
}
lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1118_, lean_object* v_k_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
if (lean_obj_tag(v_stx_1118_) == 3)
{
lean_object* v_val_1129_; lean_object* v_preresolved_1130_; lean_object* v___x_1131_; lean_object* v_pre_1132_; uint8_t v___x_1133_; 
v_val_1129_ = lean_ctor_get(v_stx_1118_, 2);
lean_inc(v_val_1129_);
v_preresolved_1130_ = lean_ctor_get(v_stx_1118_, 3);
v___x_1131_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1130_);
v_pre_1132_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1130_, v___x_1131_);
v___x_1133_ = l_List_isEmpty___redArg(v_pre_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_val_1129_);
lean_dec_ref_known(v_stx_1118_, 4);
lean_dec_ref(v_k_1119_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_pre_1132_);
return v___x_1134_;
}
else
{
lean_object* v_toCold_1135_; lean_object* v_currRecDepth_1136_; lean_object* v_ref_1137_; uint16_t v_optionFlags_1138_; uint8_t v_suppressElabErrors_1139_; uint8_t v_isRecordingDeps_1140_; lean_object* v_ref_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_pre_1132_);
v_toCold_1135_ = lean_ctor_get(v___y_1126_, 0);
v_currRecDepth_1136_ = lean_ctor_get(v___y_1126_, 1);
v_ref_1137_ = lean_ctor_get(v___y_1126_, 2);
v_optionFlags_1138_ = lean_ctor_get_uint16(v___y_1126_, sizeof(void*)*3);
v_suppressElabErrors_1139_ = lean_ctor_get_uint8(v___y_1126_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1140_ = lean_ctor_get_uint8(v___y_1126_, sizeof(void*)*3 + 3);
v_ref_1141_ = l_Lean_replaceRef(v_stx_1118_, v_ref_1137_);
lean_dec_ref_known(v_stx_1118_, 4);
lean_inc(v_currRecDepth_1136_);
lean_inc_ref(v_toCold_1135_);
v___x_1142_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1142_, 0, v_toCold_1135_);
lean_ctor_set(v___x_1142_, 1, v_currRecDepth_1136_);
lean_ctor_set(v___x_1142_, 2, v_ref_1141_);
lean_ctor_set_uint16(v___x_1142_, sizeof(void*)*3, v_optionFlags_1138_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*3 + 2, v_suppressElabErrors_1139_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*3 + 3, v_isRecordingDeps_1140_);
lean_inc(v___y_1127_);
lean_inc(v___y_1125_);
lean_inc_ref(v___y_1124_);
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
v___x_1143_ = lean_apply_10(v_k_1119_, v_val_1129_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___x_1142_, v___y_1127_, lean_box(0));
return v___x_1143_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_k_1119_);
v___x_1144_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1145_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1118_, v___x_1144_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v_stx_1118_);
return v___x_1145_;
}
}
}
LEAN_EXPORT void l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1118_ = stack[0].m_obj;
lean_object* v_k_1119_ = stack[1].m_obj;
lean_object* v___y_1120_ = stack[2].m_obj;
lean_object* v___y_1121_ = stack[3].m_obj;
lean_object* v___y_1122_ = stack[4].m_obj;
lean_object* v___y_1123_ = stack[5].m_obj;
lean_object* v___y_1124_ = stack[6].m_obj;
lean_object* v___y_1125_ = stack[7].m_obj;
lean_object* v___y_1126_ = stack[8].m_obj;
lean_object* v___y_1127_ = stack[9].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1118_, v_k_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1147_, lean_object* v_k_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1147_, v_k_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1158_;
}
}
lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1171_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1160_, v___x_1170_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1171_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1160_ = stack[0].m_obj;
lean_object* v___y_1161_ = stack[1].m_obj;
lean_object* v___y_1162_ = stack[2].m_obj;
lean_object* v___y_1163_ = stack[3].m_obj;
lean_object* v___y_1164_ = stack[4].m_obj;
lean_object* v___y_1165_ = stack[5].m_obj;
lean_object* v___y_1166_ = stack[6].m_obj;
lean_object* v___y_1167_ = stack[7].m_obj;
lean_object* v___y_1168_ = stack[8].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1183_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1184_, size_t v_sz_1185_, size_t v_i_1186_, lean_object* v_b_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_usize_dec_lt(v_i_1186_, v_sz_1185_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_b_1187_);
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v_name_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_a_1199_ = lean_array_uget_borrowed(v_as_1184_, v_i_1186_);
v_name_1200_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_name_1200_);
v___x_1201_ = l_Lean_mkIdent(v_name_1200_);
lean_inc(v___x_1201_);
v___x_1202_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1201_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1201_, v_a_1203_, v_b_1187_, v___y_1194_);
lean_dec(v_a_1203_);
lean_dec(v___x_1201_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; size_t v___x_1206_; size_t v___x_1207_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1186_, v___x_1206_);
v_i_1186_ = v___x_1207_;
v_b_1187_ = v_a_1205_;
goto _start;
}
else
{
return v___x_1204_;
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v___x_1201_);
lean_dec_ref(v_b_1187_);
v_a_1209_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1202_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1202_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1184_ = stack[0].m_obj;
size_t v_sz_1185_ = stack[1].m_num;
size_t v_i_1186_ = stack[2].m_num;
lean_object* v_b_1187_ = stack[3].m_obj;
lean_object* v___y_1188_ = stack[4].m_obj;
lean_object* v___y_1189_ = stack[5].m_obj;
lean_object* v___y_1190_ = stack[6].m_obj;
lean_object* v___y_1191_ = stack[7].m_obj;
lean_object* v___y_1192_ = stack[8].m_obj;
lean_object* v___y_1193_ = stack[9].m_obj;
lean_object* v___y_1194_ = stack[10].m_obj;
lean_object* v___y_1195_ = stack[11].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1184_, v_sz_1185_, v_i_1186_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1218_, lean_object* v_sz_1219_, lean_object* v_i_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
size_t v_sz_boxed_1231_; size_t v_i_boxed_1232_; lean_object* v_res_1233_; 
v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1219_);
lean_dec(v_sz_1219_);
v_i_boxed_1232_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1218_, v_sz_boxed_1231_, v_i_boxed_1232_, v_b_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v_as_1218_);
return v_res_1233_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1253_, lean_object* v_stx_1254_, uint8_t v___x_1255_, lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v___f_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
if (v___x_1253_ == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_1269_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v_tk_1271_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1343_; uint8_t v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v_stxForSuggestion_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; uint8_t v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; uint8_t v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; uint8_t v___y_1551_; lean_object* v___y_1552_; uint8_t v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; uint8_t v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; uint8_t v___y_1592_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v_stxForExecution_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; uint8_t v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1686_; uint8_t v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; uint8_t v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; uint8_t v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; uint8_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; uint8_t v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; uint8_t v___y_1786_; uint8_t v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1881_; lean_object* v_argsArray_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; uint8_t v___y_1966_; lean_object* v___y_1967_; uint8_t v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; uint8_t v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v_args_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___x_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v_o_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v_bang_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v_tk_1271_ = l_Lean_Syntax_getArg(v_stx_1254_, v___x_1270_);
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2128_ = l_Lean_Syntax_getArg(v_stx_1254_, v___x_2069_);
v___x_2129_ = l_Lean_Syntax_isNone(v___x_2128_);
if (v___x_2129_ == 0)
{
uint8_t v___x_2130_; 
lean_inc(v___x_2128_);
v___x_2130_ = l_Lean_Syntax_matchesNull(v___x_2128_, v___x_2069_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec(v___x_2128_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_2131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2131_;
}
else
{
lean_object* v_bang_2132_; lean_object* v___x_2133_; 
v_bang_2132_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_1270_);
lean_dec(v___x_2128_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_bang_2132_);
v_bang_2100_ = v___x_2133_;
v___y_2101_ = v___y_1260_;
v___y_2102_ = v___y_1261_;
v___y_2103_ = v___y_1262_;
v___y_2104_ = v___y_1263_;
v___y_2105_ = v___y_1264_;
v___y_2106_ = v___y_1265_;
v___y_2107_ = v___y_1266_;
v___y_2108_ = v___y_1267_;
goto v___jp_2099_;
}
}
else
{
lean_object* v___x_2134_; 
lean_dec(v___x_2128_);
v___x_2134_ = lean_box(0);
v_bang_2100_ = v___x_2134_;
v___y_2101_ = v___y_1260_;
v___y_2102_ = v___y_1261_;
v___y_2103_ = v___y_1262_;
v___y_2104_ = v___y_1263_;
v___y_2105_ = v___y_1264_;
v___y_2106_ = v___y_1265_;
v___y_2107_ = v___y_1266_;
v___y_2108_ = v___y_1267_;
goto v___jp_2099_;
}
v___jp_1272_:
{
lean_object* v___x_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_box(v___x_1255_);
v___f_1287_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1287_, 0, v___y_1275_);
lean_closure_set(v___f_1287_, 1, v___x_1270_);
lean_closure_set(v___f_1287_, 2, v___x_1286_);
lean_closure_set(v___f_1287_, 3, v___y_1285_);
lean_closure_set(v___f_1287_, 4, v___y_1274_);
v___x_1288_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1273_, v___f_1287_, v___y_1282_, v___y_1277_, v___y_1280_, v___y_1281_, v___y_1279_, v___y_1276_, v___y_1278_, v___y_1283_);
lean_dec(v___y_1273_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_usedTheorems_1290_; lean_object* v_diag_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1333_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_usedTheorems_1290_ = lean_ctor_get(v_a_1289_, 0);
v_diag_1291_ = lean_ctor_get(v_a_1289_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1293_ = v_a_1289_;
v_isShared_1294_ = v_isSharedCheck_1333_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_diag_1291_);
lean_inc(v_usedTheorems_1290_);
lean_dec(v_a_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1333_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1284_, v_usedTheorems_1290_, v___y_1279_, v___y_1276_, v___y_1278_, v___y_1283_);
lean_dec_ref(v_usedTheorems_1290_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v_ref_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v_ref_1297_ = lean_ctor_get(v___y_1278_, 2);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_a_1296_);
lean_ctor_set(v___x_1293_, 0, v___x_1298_);
v___x_1300_ = v___x_1293_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_a_1296_);
v___x_1300_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_ctor_set(v___x_1302_, 2, v___x_1301_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
lean_ctor_set(v___x_1302_, 4, v___x_1301_);
lean_ctor_set(v___x_1302_, 5, v___x_1301_);
lean_inc(v_ref_1297_);
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_ref_1297_);
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1305_ = 4;
v___x_1306_ = l_Lean_MessageData_nil;
v___x_1307_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1271_, v___x_1302_, v___x_1303_, v___x_1304_, v___x_1301_, v___x_1305_, v___x_1306_, v___y_1278_, v___y_1283_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1315_);
v___x_1309_ = v___x_1307_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v___x_1307_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v_diag_1291_);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_diag_1291_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_diag_1291_);
v_a_1316_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1307_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1307_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_del_object(v___x_1293_);
lean_dec_ref(v_diag_1291_);
lean_dec(v_tk_1271_);
v_a_1325_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1295_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1295_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v___y_1284_);
lean_dec(v_tk_1271_);
v_a_1334_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1288_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1288_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
v___jp_1342_:
{
uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = 0;
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1359_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1345_, v___x_1357_, v___y_1344_, v___x_1357_, v___x_1358_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1345_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
if (lean_obj_tag(v___y_1346_) == 0)
{
lean_object* v_ctx_1361_; lean_object* v_simprocs_1362_; lean_object* v_dischargeWrapper_1363_; 
v_ctx_1361_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_ctx_1361_);
v_simprocs_1362_ = lean_ctor_get(v_a_1360_, 1);
lean_inc_ref(v_simprocs_1362_);
v_dischargeWrapper_1363_ = lean_ctor_get(v_a_1360_, 2);
lean_inc(v_dischargeWrapper_1363_);
lean_dec(v_a_1360_);
v___y_1273_ = v_dischargeWrapper_1363_;
v___y_1274_ = v_simprocs_1362_;
v___y_1275_ = v___y_1343_;
v___y_1276_ = v___y_1354_;
v___y_1277_ = v___y_1350_;
v___y_1278_ = v___y_1355_;
v___y_1279_ = v___y_1353_;
v___y_1280_ = v___y_1351_;
v___y_1281_ = v___y_1352_;
v___y_1282_ = v___y_1349_;
v___y_1283_ = v___y_1356_;
v___y_1284_ = v_stxForSuggestion_1348_;
v___y_1285_ = v_ctx_1361_;
goto v___jp_1272_;
}
else
{
lean_dec_ref_known(v___y_1346_, 1);
if (v___y_1347_ == 0)
{
lean_object* v_ctx_1364_; lean_object* v_simprocs_1365_; lean_object* v_dischargeWrapper_1366_; 
v_ctx_1364_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_ctx_1364_);
v_simprocs_1365_ = lean_ctor_get(v_a_1360_, 1);
lean_inc_ref(v_simprocs_1365_);
v_dischargeWrapper_1366_ = lean_ctor_get(v_a_1360_, 2);
lean_inc(v_dischargeWrapper_1366_);
lean_dec(v_a_1360_);
v___y_1273_ = v_dischargeWrapper_1366_;
v___y_1274_ = v_simprocs_1365_;
v___y_1275_ = v___y_1343_;
v___y_1276_ = v___y_1354_;
v___y_1277_ = v___y_1350_;
v___y_1278_ = v___y_1355_;
v___y_1279_ = v___y_1353_;
v___y_1280_ = v___y_1351_;
v___y_1281_ = v___y_1352_;
v___y_1282_ = v___y_1349_;
v___y_1283_ = v___y_1356_;
v___y_1284_ = v_stxForSuggestion_1348_;
v___y_1285_ = v_ctx_1364_;
goto v___jp_1272_;
}
else
{
lean_object* v_ctx_1367_; lean_object* v_simprocs_1368_; lean_object* v_dischargeWrapper_1369_; lean_object* v___x_1370_; 
v_ctx_1367_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_ctx_1367_);
v_simprocs_1368_ = lean_ctor_get(v_a_1360_, 1);
lean_inc_ref(v_simprocs_1368_);
v_dischargeWrapper_1369_ = lean_ctor_get(v_a_1360_, 2);
lean_inc(v_dischargeWrapper_1369_);
lean_dec(v_a_1360_);
v___x_1370_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1367_);
v___y_1273_ = v_dischargeWrapper_1369_;
v___y_1274_ = v_simprocs_1368_;
v___y_1275_ = v___y_1343_;
v___y_1276_ = v___y_1354_;
v___y_1277_ = v___y_1350_;
v___y_1278_ = v___y_1355_;
v___y_1279_ = v___y_1353_;
v___y_1280_ = v___y_1351_;
v___y_1281_ = v___y_1352_;
v___y_1282_ = v___y_1349_;
v___y_1283_ = v___y_1356_;
v___y_1284_ = v_stxForSuggestion_1348_;
v___y_1285_ = v___x_1370_;
goto v___jp_1272_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_stxForSuggestion_1348_);
lean_dec(v___y_1346_);
lean_dec(v___y_1343_);
lean_dec(v_tk_1271_);
v_a_1371_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1359_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1359_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
v___jp_1379_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v___y_1401_);
v___x_1403_ = l_Array_append___redArg(v___y_1401_, v___y_1402_);
lean_dec_ref(v___y_1402_);
lean_inc(v___y_1387_);
lean_inc(v___y_1384_);
v___x_1404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1404_, 0, v___y_1384_);
lean_ctor_set(v___x_1404_, 1, v___y_1387_);
lean_ctor_set(v___x_1404_, 2, v___x_1403_);
v___x_1405_ = l_Lean_Syntax_node6(v___y_1384_, v___y_1390_, v___y_1400_, v___y_1399_, v___y_1395_, v___y_1396_, v___y_1388_, v___x_1404_);
v___y_1343_ = v___y_1380_;
v___y_1344_ = v___y_1393_;
v___y_1345_ = v___y_1392_;
v___y_1346_ = v___y_1397_;
v___y_1347_ = v___y_1391_;
v_stxForSuggestion_1348_ = v___x_1405_;
v___y_1349_ = v___y_1383_;
v___y_1350_ = v___y_1398_;
v___y_1351_ = v___y_1386_;
v___y_1352_ = v___y_1382_;
v___y_1353_ = v___y_1394_;
v___y_1354_ = v___y_1385_;
v___y_1355_ = v___y_1381_;
v___y_1356_ = v___y_1389_;
goto v___jp_1342_;
}
v___jp_1406_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_inc_ref_n(v___y_1428_, 2);
v___x_1430_ = l_Array_append___redArg(v___y_1428_, v___y_1429_);
lean_dec_ref(v___y_1429_);
lean_inc_n(v___y_1414_, 3);
lean_inc_n(v___y_1411_, 5);
v___x_1431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1411_);
lean_ctor_set(v___x_1431_, 1, v___y_1414_);
lean_ctor_set(v___x_1431_, 2, v___x_1430_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1411_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1435_ = l_Lean_Syntax_SepArray_ofElems(v___x_1434_, v___y_1426_);
lean_dec_ref(v___y_1426_);
v___x_1436_ = l_Array_append___redArg(v___y_1428_, v___x_1435_);
lean_dec_ref(v___x_1435_);
v___x_1437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1411_);
lean_ctor_set(v___x_1437_, 1, v___y_1414_);
lean_ctor_set(v___x_1437_, 2, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1411_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_Syntax_node3(v___y_1411_, v___y_1414_, v___x_1433_, v___x_1437_, v___x_1439_);
if (lean_obj_tag(v___y_1423_) == 1)
{
lean_object* v_val_1441_; lean_object* v___x_1442_; 
v_val_1441_ = lean_ctor_get(v___y_1423_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___y_1423_, 1);
v___x_1442_ = l_Array_mkArray1___redArg(v_val_1441_);
v___y_1380_ = v___y_1407_;
v___y_1381_ = v___y_1408_;
v___y_1382_ = v___y_1409_;
v___y_1383_ = v___y_1410_;
v___y_1384_ = v___y_1411_;
v___y_1385_ = v___y_1412_;
v___y_1386_ = v___y_1413_;
v___y_1387_ = v___y_1414_;
v___y_1388_ = v___x_1440_;
v___y_1389_ = v___y_1415_;
v___y_1390_ = v___y_1416_;
v___y_1391_ = v___y_1417_;
v___y_1392_ = v___y_1421_;
v___y_1393_ = v___y_1420_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1418_;
v___y_1396_ = v___x_1431_;
v___y_1397_ = v___y_1422_;
v___y_1398_ = v___y_1424_;
v___y_1399_ = v___y_1425_;
v___y_1400_ = v___y_1427_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___x_1442_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1443_; 
lean_dec(v___y_1423_);
v___x_1443_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1380_ = v___y_1407_;
v___y_1381_ = v___y_1408_;
v___y_1382_ = v___y_1409_;
v___y_1383_ = v___y_1410_;
v___y_1384_ = v___y_1411_;
v___y_1385_ = v___y_1412_;
v___y_1386_ = v___y_1413_;
v___y_1387_ = v___y_1414_;
v___y_1388_ = v___x_1440_;
v___y_1389_ = v___y_1415_;
v___y_1390_ = v___y_1416_;
v___y_1391_ = v___y_1417_;
v___y_1392_ = v___y_1421_;
v___y_1393_ = v___y_1420_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1418_;
v___y_1396_ = v___x_1431_;
v___y_1397_ = v___y_1422_;
v___y_1398_ = v___y_1424_;
v___y_1399_ = v___y_1425_;
v___y_1400_ = v___y_1427_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___x_1443_;
goto v___jp_1379_;
}
}
v___jp_1444_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_inc_ref(v___y_1466_);
v___x_1468_ = l_Array_append___redArg(v___y_1466_, v___y_1467_);
lean_dec_ref(v___y_1467_);
lean_inc(v___y_1452_);
lean_inc(v___y_1449_);
v___x_1469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1469_, 0, v___y_1449_);
lean_ctor_set(v___x_1469_, 1, v___y_1452_);
lean_ctor_set(v___x_1469_, 2, v___x_1468_);
if (lean_obj_tag(v___y_1461_) == 1)
{
lean_object* v_val_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_val_1470_ = lean_ctor_get(v___y_1461_, 0);
lean_inc(v_val_1470_);
lean_dec_ref_known(v___y_1461_, 1);
v___x_1471_ = l_Lean_SourceInfo_fromRef(v_val_1470_, v___x_1255_);
lean_dec(v_val_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Array_mkArray1___redArg(v___x_1473_);
v___y_1407_ = v___y_1445_;
v___y_1408_ = v___y_1446_;
v___y_1409_ = v___y_1447_;
v___y_1410_ = v___y_1448_;
v___y_1411_ = v___y_1449_;
v___y_1412_ = v___y_1450_;
v___y_1413_ = v___y_1451_;
v___y_1414_ = v___y_1452_;
v___y_1415_ = v___y_1453_;
v___y_1416_ = v___y_1454_;
v___y_1417_ = v___y_1455_;
v___y_1418_ = v___x_1469_;
v___y_1419_ = v___y_1458_;
v___y_1420_ = v___y_1457_;
v___y_1421_ = v___y_1456_;
v___y_1422_ = v___y_1459_;
v___y_1423_ = v___y_1460_;
v___y_1424_ = v___y_1462_;
v___y_1425_ = v___y_1464_;
v___y_1426_ = v___y_1463_;
v___y_1427_ = v___y_1465_;
v___y_1428_ = v___y_1466_;
v___y_1429_ = v___x_1474_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1475_; 
lean_dec(v___y_1461_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1407_ = v___y_1445_;
v___y_1408_ = v___y_1446_;
v___y_1409_ = v___y_1447_;
v___y_1410_ = v___y_1448_;
v___y_1411_ = v___y_1449_;
v___y_1412_ = v___y_1450_;
v___y_1413_ = v___y_1451_;
v___y_1414_ = v___y_1452_;
v___y_1415_ = v___y_1453_;
v___y_1416_ = v___y_1454_;
v___y_1417_ = v___y_1455_;
v___y_1418_ = v___x_1469_;
v___y_1419_ = v___y_1458_;
v___y_1420_ = v___y_1457_;
v___y_1421_ = v___y_1456_;
v___y_1422_ = v___y_1459_;
v___y_1423_ = v___y_1460_;
v___y_1424_ = v___y_1462_;
v___y_1425_ = v___y_1464_;
v___y_1426_ = v___y_1463_;
v___y_1427_ = v___y_1465_;
v___y_1428_ = v___y_1466_;
v___y_1429_ = v___x_1475_;
goto v___jp_1406_;
}
}
v___jp_1476_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_inc_ref(v___y_1492_);
v___x_1500_ = l_Array_append___redArg(v___y_1492_, v___y_1499_);
lean_dec_ref(v___y_1499_);
lean_inc(v___y_1484_);
lean_inc(v___y_1493_);
v___x_1501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1501_, 0, v___y_1493_);
lean_ctor_set(v___x_1501_, 1, v___y_1484_);
lean_ctor_set(v___x_1501_, 2, v___x_1500_);
v___x_1502_ = l_Lean_Syntax_node6(v___y_1493_, v___y_1485_, v___y_1498_, v___y_1497_, v___y_1488_, v___y_1482_, v___y_1495_, v___x_1501_);
v___y_1343_ = v___y_1477_;
v___y_1344_ = v___y_1490_;
v___y_1345_ = v___y_1489_;
v___y_1346_ = v___y_1494_;
v___y_1347_ = v___y_1487_;
v_stxForSuggestion_1348_ = v___x_1502_;
v___y_1349_ = v___y_1480_;
v___y_1350_ = v___y_1496_;
v___y_1351_ = v___y_1483_;
v___y_1352_ = v___y_1479_;
v___y_1353_ = v___y_1491_;
v___y_1354_ = v___y_1481_;
v___y_1355_ = v___y_1478_;
v___y_1356_ = v___y_1486_;
goto v___jp_1342_;
}
v___jp_1503_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc_ref_n(v___y_1518_, 2);
v___x_1527_ = l_Array_append___redArg(v___y_1518_, v___y_1526_);
lean_dec_ref(v___y_1526_);
lean_inc_n(v___y_1510_, 3);
lean_inc_n(v___y_1519_, 5);
v___x_1528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1528_, 0, v___y_1519_);
lean_ctor_set(v___x_1528_, 1, v___y_1510_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___y_1519_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1532_ = l_Lean_Syntax_SepArray_ofElems(v___x_1531_, v___y_1524_);
lean_dec_ref(v___y_1524_);
v___x_1533_ = l_Array_append___redArg(v___y_1518_, v___x_1532_);
lean_dec_ref(v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1519_);
lean_ctor_set(v___x_1534_, 1, v___y_1510_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___y_1519_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_Syntax_node3(v___y_1519_, v___y_1510_, v___x_1530_, v___x_1534_, v___x_1536_);
if (lean_obj_tag(v___y_1521_) == 1)
{
lean_object* v_val_1538_; lean_object* v___x_1539_; 
v_val_1538_ = lean_ctor_get(v___y_1521_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v___y_1521_, 1);
v___x_1539_ = l_Array_mkArray1___redArg(v_val_1538_);
v___y_1477_ = v___y_1504_;
v___y_1478_ = v___y_1505_;
v___y_1479_ = v___y_1506_;
v___y_1480_ = v___y_1507_;
v___y_1481_ = v___y_1508_;
v___y_1482_ = v___x_1528_;
v___y_1483_ = v___y_1509_;
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___y_1511_;
v___y_1486_ = v___y_1512_;
v___y_1487_ = v___y_1513_;
v___y_1488_ = v___y_1514_;
v___y_1489_ = v___y_1517_;
v___y_1490_ = v___y_1516_;
v___y_1491_ = v___y_1515_;
v___y_1492_ = v___y_1518_;
v___y_1493_ = v___y_1519_;
v___y_1494_ = v___y_1520_;
v___y_1495_ = v___x_1537_;
v___y_1496_ = v___y_1522_;
v___y_1497_ = v___y_1523_;
v___y_1498_ = v___y_1525_;
v___y_1499_ = v___x_1539_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v___y_1521_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1477_ = v___y_1504_;
v___y_1478_ = v___y_1505_;
v___y_1479_ = v___y_1506_;
v___y_1480_ = v___y_1507_;
v___y_1481_ = v___y_1508_;
v___y_1482_ = v___x_1528_;
v___y_1483_ = v___y_1509_;
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___y_1511_;
v___y_1486_ = v___y_1512_;
v___y_1487_ = v___y_1513_;
v___y_1488_ = v___y_1514_;
v___y_1489_ = v___y_1517_;
v___y_1490_ = v___y_1516_;
v___y_1491_ = v___y_1515_;
v___y_1492_ = v___y_1518_;
v___y_1493_ = v___y_1519_;
v___y_1494_ = v___y_1520_;
v___y_1495_ = v___x_1537_;
v___y_1496_ = v___y_1522_;
v___y_1497_ = v___y_1523_;
v___y_1498_ = v___y_1525_;
v___y_1499_ = v___x_1540_;
goto v___jp_1476_;
}
}
v___jp_1541_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_inc_ref(v___y_1554_);
v___x_1565_ = l_Array_append___redArg(v___y_1554_, v___y_1564_);
lean_dec_ref(v___y_1564_);
lean_inc(v___y_1548_);
lean_inc(v___y_1555_);
v___x_1566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1566_, 0, v___y_1555_);
lean_ctor_set(v___x_1566_, 1, v___y_1548_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
if (lean_obj_tag(v___y_1559_) == 1)
{
lean_object* v_val_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_val_1567_ = lean_ctor_get(v___y_1559_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___y_1559_, 1);
v___x_1568_ = l_Lean_SourceInfo_fromRef(v_val_1567_, v___x_1255_);
lean_dec(v_val_1567_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Array_mkArray1___redArg(v___x_1570_);
v___y_1504_ = v___y_1542_;
v___y_1505_ = v___y_1543_;
v___y_1506_ = v___y_1544_;
v___y_1507_ = v___y_1545_;
v___y_1508_ = v___y_1546_;
v___y_1509_ = v___y_1547_;
v___y_1510_ = v___y_1548_;
v___y_1511_ = v___y_1549_;
v___y_1512_ = v___y_1550_;
v___y_1513_ = v___y_1551_;
v___y_1514_ = v___x_1566_;
v___y_1515_ = v___y_1556_;
v___y_1516_ = v___y_1553_;
v___y_1517_ = v___y_1552_;
v___y_1518_ = v___y_1554_;
v___y_1519_ = v___y_1555_;
v___y_1520_ = v___y_1557_;
v___y_1521_ = v___y_1558_;
v___y_1522_ = v___y_1560_;
v___y_1523_ = v___y_1562_;
v___y_1524_ = v___y_1561_;
v___y_1525_ = v___y_1563_;
v___y_1526_ = v___x_1571_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1572_; 
lean_dec(v___y_1559_);
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1504_ = v___y_1542_;
v___y_1505_ = v___y_1543_;
v___y_1506_ = v___y_1544_;
v___y_1507_ = v___y_1545_;
v___y_1508_ = v___y_1546_;
v___y_1509_ = v___y_1547_;
v___y_1510_ = v___y_1548_;
v___y_1511_ = v___y_1549_;
v___y_1512_ = v___y_1550_;
v___y_1513_ = v___y_1551_;
v___y_1514_ = v___x_1566_;
v___y_1515_ = v___y_1556_;
v___y_1516_ = v___y_1553_;
v___y_1517_ = v___y_1552_;
v___y_1518_ = v___y_1554_;
v___y_1519_ = v___y_1555_;
v___y_1520_ = v___y_1557_;
v___y_1521_ = v___y_1558_;
v___y_1522_ = v___y_1560_;
v___y_1523_ = v___y_1562_;
v___y_1524_ = v___y_1561_;
v___y_1525_ = v___y_1563_;
v___y_1526_ = v___x_1572_;
goto v___jp_1503_;
}
}
v___jp_1573_:
{
lean_object* v_ref_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_ref_1593_ = lean_ctor_get(v___y_1575_, 2);
v___x_1594_ = l_Lean_SourceInfo_fromRef(v_ref_1593_, v___y_1592_);
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1596_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_1595_);
v___x_1597_ = l_Lean_SourceInfo_fromRef(v_tk_1271_, v___x_1255_);
v___x_1598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1595_);
v___x_1599_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1600_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1581_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1602_; 
v_val_1601_ = lean_ctor_get(v___y_1581_, 0);
lean_inc(v_val_1601_);
lean_dec_ref_known(v___y_1581_, 1);
v___x_1602_ = l_Array_mkArray1___redArg(v_val_1601_);
v___y_1542_ = v___y_1574_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v___y_1576_;
v___y_1545_ = v___y_1577_;
v___y_1546_ = v___y_1578_;
v___y_1547_ = v___y_1579_;
v___y_1548_ = v___x_1599_;
v___y_1549_ = v___x_1596_;
v___y_1550_ = v___y_1580_;
v___y_1551_ = v___y_1582_;
v___y_1552_ = v___y_1583_;
v___y_1553_ = v___y_1584_;
v___y_1554_ = v___x_1600_;
v___y_1555_ = v___x_1594_;
v___y_1556_ = v___y_1585_;
v___y_1557_ = v___y_1586_;
v___y_1558_ = v___y_1587_;
v___y_1559_ = v___y_1588_;
v___y_1560_ = v___y_1589_;
v___y_1561_ = v___y_1591_;
v___y_1562_ = v___y_1590_;
v___y_1563_ = v___x_1598_;
v___y_1564_ = v___x_1602_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1603_; 
lean_dec(v___y_1581_);
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1542_ = v___y_1574_;
v___y_1543_ = v___y_1575_;
v___y_1544_ = v___y_1576_;
v___y_1545_ = v___y_1577_;
v___y_1546_ = v___y_1578_;
v___y_1547_ = v___y_1579_;
v___y_1548_ = v___x_1599_;
v___y_1549_ = v___x_1596_;
v___y_1550_ = v___y_1580_;
v___y_1551_ = v___y_1582_;
v___y_1552_ = v___y_1583_;
v___y_1553_ = v___y_1584_;
v___y_1554_ = v___x_1600_;
v___y_1555_ = v___x_1594_;
v___y_1556_ = v___y_1585_;
v___y_1557_ = v___y_1586_;
v___y_1558_ = v___y_1587_;
v___y_1559_ = v___y_1588_;
v___y_1560_ = v___y_1589_;
v___y_1561_ = v___y_1591_;
v___y_1562_ = v___y_1590_;
v___y_1563_ = v___x_1598_;
v___y_1564_ = v___x_1603_;
goto v___jp_1541_;
}
}
v___jp_1604_:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1607_);
if (lean_obj_tag(v___y_1608_) == 0)
{
lean_object* v_a_1624_; uint8_t v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref(v___x_1623_);
v___x_1625_ = 0;
v___y_1574_ = v___y_1605_;
v___y_1575_ = v___y_1621_;
v___y_1576_ = v___y_1618_;
v___y_1577_ = v___y_1615_;
v___y_1578_ = v___y_1620_;
v___y_1579_ = v___y_1617_;
v___y_1580_ = v___y_1622_;
v___y_1581_ = v___y_1612_;
v___y_1582_ = v___y_1613_;
v___y_1583_ = v_stxForExecution_1614_;
v___y_1584_ = v___y_1606_;
v___y_1585_ = v___y_1619_;
v___y_1586_ = v___y_1608_;
v___y_1587_ = v___y_1609_;
v___y_1588_ = v___y_1610_;
v___y_1589_ = v___y_1616_;
v___y_1590_ = v_a_1624_;
v___y_1591_ = v___y_1611_;
v___y_1592_ = v___x_1625_;
goto v___jp_1573_;
}
else
{
if (v___y_1613_ == 0)
{
lean_object* v_a_1626_; 
v_a_1626_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1623_);
v___y_1574_ = v___y_1605_;
v___y_1575_ = v___y_1621_;
v___y_1576_ = v___y_1618_;
v___y_1577_ = v___y_1615_;
v___y_1578_ = v___y_1620_;
v___y_1579_ = v___y_1617_;
v___y_1580_ = v___y_1622_;
v___y_1581_ = v___y_1612_;
v___y_1582_ = v___y_1613_;
v___y_1583_ = v_stxForExecution_1614_;
v___y_1584_ = v___y_1606_;
v___y_1585_ = v___y_1619_;
v___y_1586_ = v___y_1608_;
v___y_1587_ = v___y_1609_;
v___y_1588_ = v___y_1610_;
v___y_1589_ = v___y_1616_;
v___y_1590_ = v_a_1626_;
v___y_1591_ = v___y_1611_;
v___y_1592_ = v___y_1613_;
goto v___jp_1573_;
}
else
{
lean_object* v_a_1627_; lean_object* v_ref_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_a_1627_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1623_);
v_ref_1628_ = lean_ctor_get(v___y_1621_, 2);
v___x_1629_ = 0;
v___x_1630_ = l_Lean_SourceInfo_fromRef(v_ref_1628_, v___x_1629_);
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1632_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_1631_);
v___x_1633_ = l_Lean_SourceInfo_fromRef(v_tk_1271_, v___x_1255_);
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1637_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1612_) == 1)
{
lean_object* v_val_1638_; lean_object* v___x_1639_; 
v_val_1638_ = lean_ctor_get(v___y_1612_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v___y_1612_, 1);
v___x_1639_ = l_Array_mkArray1___redArg(v_val_1638_);
v___y_1445_ = v___y_1605_;
v___y_1446_ = v___y_1621_;
v___y_1447_ = v___y_1618_;
v___y_1448_ = v___y_1615_;
v___y_1449_ = v___x_1630_;
v___y_1450_ = v___y_1620_;
v___y_1451_ = v___y_1617_;
v___y_1452_ = v___x_1636_;
v___y_1453_ = v___y_1622_;
v___y_1454_ = v___x_1632_;
v___y_1455_ = v___y_1613_;
v___y_1456_ = v_stxForExecution_1614_;
v___y_1457_ = v___y_1606_;
v___y_1458_ = v___y_1619_;
v___y_1459_ = v___y_1608_;
v___y_1460_ = v___y_1609_;
v___y_1461_ = v___y_1610_;
v___y_1462_ = v___y_1616_;
v___y_1463_ = v___y_1611_;
v___y_1464_ = v_a_1627_;
v___y_1465_ = v___x_1635_;
v___y_1466_ = v___x_1637_;
v___y_1467_ = v___x_1639_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1640_; 
lean_dec(v___y_1612_);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1445_ = v___y_1605_;
v___y_1446_ = v___y_1621_;
v___y_1447_ = v___y_1618_;
v___y_1448_ = v___y_1615_;
v___y_1449_ = v___x_1630_;
v___y_1450_ = v___y_1620_;
v___y_1451_ = v___y_1617_;
v___y_1452_ = v___x_1636_;
v___y_1453_ = v___y_1622_;
v___y_1454_ = v___x_1632_;
v___y_1455_ = v___y_1613_;
v___y_1456_ = v_stxForExecution_1614_;
v___y_1457_ = v___y_1606_;
v___y_1458_ = v___y_1619_;
v___y_1459_ = v___y_1608_;
v___y_1460_ = v___y_1609_;
v___y_1461_ = v___y_1610_;
v___y_1462_ = v___y_1616_;
v___y_1463_ = v___y_1611_;
v___y_1464_ = v_a_1627_;
v___y_1465_ = v___x_1635_;
v___y_1466_ = v___x_1637_;
v___y_1467_ = v___x_1640_;
goto v___jp_1444_;
}
}
}
}
v___jp_1641_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_inc_ref(v___y_1666_);
v___x_1668_ = l_Array_append___redArg(v___y_1666_, v___y_1667_);
lean_dec_ref(v___y_1667_);
lean_inc(v___y_1643_);
lean_inc(v___y_1659_);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1659_);
lean_ctor_set(v___x_1669_, 1, v___y_1643_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_inc(v___y_1652_);
v___x_1670_ = l_Lean_Syntax_node6(v___y_1659_, v___y_1645_, v___y_1649_, v___y_1652_, v___y_1647_, v___y_1663_, v___y_1662_, v___x_1669_);
v___y_1605_ = v___y_1642_;
v___y_1606_ = v___y_1660_;
v___y_1607_ = v___y_1652_;
v___y_1608_ = v___y_1650_;
v___y_1609_ = v___y_1661_;
v___y_1610_ = v___y_1651_;
v___y_1611_ = v___y_1665_;
v___y_1612_ = v___y_1658_;
v___y_1613_ = v___y_1648_;
v_stxForExecution_1614_ = v___x_1670_;
v___y_1615_ = v___y_1655_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1653_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1646_;
v___y_1620_ = v___y_1664_;
v___y_1621_ = v___y_1656_;
v___y_1622_ = v___y_1644_;
goto v___jp_1604_;
}
v___jp_1671_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_inc_ref_n(v___y_1694_, 2);
v___x_1696_ = l_Array_append___redArg(v___y_1694_, v___y_1695_);
lean_dec_ref(v___y_1695_);
lean_inc_n(v___y_1674_, 3);
lean_inc_n(v___y_1686_, 5);
v___x_1697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1686_);
lean_ctor_set(v___x_1697_, 1, v___y_1674_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1686_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1701_ = l_Lean_Syntax_SepArray_ofElems(v___x_1700_, v___y_1693_);
v___x_1702_ = l_Array_append___redArg(v___y_1694_, v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1686_);
lean_ctor_set(v___x_1703_, 1, v___y_1674_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___y_1686_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_Syntax_node3(v___y_1686_, v___y_1674_, v___x_1699_, v___x_1703_, v___x_1705_);
if (lean_obj_tag(v___y_1690_) == 1)
{
lean_object* v_val_1707_; lean_object* v___x_1708_; 
v_val_1707_ = lean_ctor_get(v___y_1690_, 0);
lean_inc(v_val_1707_);
v___x_1708_ = l_Array_mkArray1___redArg(v_val_1707_);
v___y_1642_ = v___y_1672_;
v___y_1643_ = v___y_1674_;
v___y_1644_ = v___y_1675_;
v___y_1645_ = v___y_1676_;
v___y_1646_ = v___y_1677_;
v___y_1647_ = v___y_1682_;
v___y_1648_ = v___y_1685_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1691_;
v___y_1652_ = v___y_1673_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1679_;
v___y_1655_ = v___y_1678_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1687_;
v___y_1661_ = v___y_1690_;
v___y_1662_ = v___x_1706_;
v___y_1663_ = v___x_1697_;
v___y_1664_ = v___y_1692_;
v___y_1665_ = v___y_1693_;
v___y_1666_ = v___y_1694_;
v___y_1667_ = v___x_1708_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1642_ = v___y_1672_;
v___y_1643_ = v___y_1674_;
v___y_1644_ = v___y_1675_;
v___y_1645_ = v___y_1676_;
v___y_1646_ = v___y_1677_;
v___y_1647_ = v___y_1682_;
v___y_1648_ = v___y_1685_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1691_;
v___y_1652_ = v___y_1673_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1679_;
v___y_1655_ = v___y_1678_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1687_;
v___y_1661_ = v___y_1690_;
v___y_1662_ = v___x_1706_;
v___y_1663_ = v___x_1697_;
v___y_1664_ = v___y_1692_;
v___y_1665_ = v___y_1693_;
v___y_1666_ = v___y_1694_;
v___y_1667_ = v___x_1709_;
goto v___jp_1641_;
}
}
v___jp_1710_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_inc_ref(v___y_1732_);
v___x_1734_ = l_Array_append___redArg(v___y_1732_, v___y_1733_);
lean_dec_ref(v___y_1733_);
lean_inc(v___y_1712_);
lean_inc(v___y_1724_);
v___x_1735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1735_, 0, v___y_1724_);
lean_ctor_set(v___x_1735_, 1, v___y_1712_);
lean_ctor_set(v___x_1735_, 2, v___x_1734_);
if (lean_obj_tag(v___y_1729_) == 1)
{
lean_object* v_val_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_val_1736_ = lean_ctor_get(v___y_1729_, 0);
v___x_1737_ = l_Lean_SourceInfo_fromRef(v_val_1736_, v___x_1255_);
v___x_1738_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Array_mkArray1___redArg(v___x_1739_);
v___y_1672_ = v___y_1711_;
v___y_1673_ = v___y_1713_;
v___y_1674_ = v___y_1712_;
v___y_1675_ = v___y_1714_;
v___y_1676_ = v___y_1715_;
v___y_1677_ = v___y_1716_;
v___y_1678_ = v___y_1717_;
v___y_1679_ = v___y_1718_;
v___y_1680_ = v___y_1719_;
v___y_1681_ = v___y_1720_;
v___y_1682_ = v___x_1735_;
v___y_1683_ = v___y_1722_;
v___y_1684_ = v___y_1723_;
v___y_1685_ = v___y_1721_;
v___y_1686_ = v___y_1724_;
v___y_1687_ = v___y_1725_;
v___y_1688_ = v___y_1727_;
v___y_1689_ = v___y_1726_;
v___y_1690_ = v___y_1728_;
v___y_1691_ = v___y_1729_;
v___y_1692_ = v___y_1731_;
v___y_1693_ = v___y_1730_;
v___y_1694_ = v___y_1732_;
v___y_1695_ = v___x_1740_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1672_ = v___y_1711_;
v___y_1673_ = v___y_1713_;
v___y_1674_ = v___y_1712_;
v___y_1675_ = v___y_1714_;
v___y_1676_ = v___y_1715_;
v___y_1677_ = v___y_1716_;
v___y_1678_ = v___y_1717_;
v___y_1679_ = v___y_1718_;
v___y_1680_ = v___y_1719_;
v___y_1681_ = v___y_1720_;
v___y_1682_ = v___x_1735_;
v___y_1683_ = v___y_1722_;
v___y_1684_ = v___y_1723_;
v___y_1685_ = v___y_1721_;
v___y_1686_ = v___y_1724_;
v___y_1687_ = v___y_1725_;
v___y_1688_ = v___y_1727_;
v___y_1689_ = v___y_1726_;
v___y_1690_ = v___y_1728_;
v___y_1691_ = v___y_1729_;
v___y_1692_ = v___y_1731_;
v___y_1693_ = v___y_1730_;
v___y_1694_ = v___y_1732_;
v___y_1695_ = v___x_1741_;
goto v___jp_1671_;
}
}
v___jp_1742_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_inc_ref(v___y_1749_);
v___x_1769_ = l_Array_append___redArg(v___y_1749_, v___y_1768_);
lean_dec_ref(v___y_1768_);
lean_inc(v___y_1753_);
lean_inc(v___y_1763_);
v___x_1770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1763_);
lean_ctor_set(v___x_1770_, 1, v___y_1753_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
lean_inc(v___y_1751_);
v___x_1771_ = l_Lean_Syntax_node6(v___y_1763_, v___y_1750_, v___y_1752_, v___y_1751_, v___y_1762_, v___y_1759_, v___y_1767_, v___x_1770_);
v___y_1605_ = v___y_1743_;
v___y_1606_ = v___y_1761_;
v___y_1607_ = v___y_1751_;
v___y_1608_ = v___y_1747_;
v___y_1609_ = v___y_1764_;
v___y_1610_ = v___y_1748_;
v___y_1611_ = v___y_1766_;
v___y_1612_ = v___y_1760_;
v___y_1613_ = v___y_1746_;
v_stxForExecution_1614_ = v___x_1771_;
v___y_1615_ = v___y_1756_;
v___y_1616_ = v___y_1755_;
v___y_1617_ = v___y_1754_;
v___y_1618_ = v___y_1758_;
v___y_1619_ = v___y_1745_;
v___y_1620_ = v___y_1765_;
v___y_1621_ = v___y_1757_;
v___y_1622_ = v___y_1744_;
goto v___jp_1604_;
}
v___jp_1772_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_inc_ref_n(v___y_1795_, 2);
v___x_1797_ = l_Array_append___redArg(v___y_1795_, v___y_1796_);
lean_dec_ref(v___y_1796_);
lean_inc_n(v___y_1776_, 3);
lean_inc_n(v___y_1789_, 5);
v___x_1798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1798_, 0, v___y_1789_);
lean_ctor_set(v___x_1798_, 1, v___y_1776_);
lean_ctor_set(v___x_1798_, 2, v___x_1797_);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___y_1789_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1802_ = l_Lean_Syntax_SepArray_ofElems(v___x_1801_, v___y_1794_);
v___x_1803_ = l_Array_append___redArg(v___y_1795_, v___x_1802_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1789_);
lean_ctor_set(v___x_1804_, 1, v___y_1776_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___y_1789_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Lean_Syntax_node3(v___y_1789_, v___y_1776_, v___x_1800_, v___x_1804_, v___x_1806_);
if (lean_obj_tag(v___y_1791_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; 
v_val_1808_ = lean_ctor_get(v___y_1791_, 0);
lean_inc(v_val_1808_);
v___x_1809_ = l_Array_mkArray1___redArg(v_val_1808_);
v___y_1743_ = v___y_1773_;
v___y_1744_ = v___y_1777_;
v___y_1745_ = v___y_1779_;
v___y_1746_ = v___y_1786_;
v___y_1747_ = v___y_1790_;
v___y_1748_ = v___y_1792_;
v___y_1749_ = v___y_1795_;
v___y_1750_ = v___y_1774_;
v___y_1751_ = v___y_1775_;
v___y_1752_ = v___y_1778_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1782_;
v___y_1755_ = v___y_1781_;
v___y_1756_ = v___y_1780_;
v___y_1757_ = v___y_1783_;
v___y_1758_ = v___y_1785_;
v___y_1759_ = v___x_1798_;
v___y_1760_ = v___y_1784_;
v___y_1761_ = v___y_1787_;
v___y_1762_ = v___y_1788_;
v___y_1763_ = v___y_1789_;
v___y_1764_ = v___y_1791_;
v___y_1765_ = v___y_1793_;
v___y_1766_ = v___y_1794_;
v___y_1767_ = v___x_1807_;
v___y_1768_ = v___x_1809_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1743_ = v___y_1773_;
v___y_1744_ = v___y_1777_;
v___y_1745_ = v___y_1779_;
v___y_1746_ = v___y_1786_;
v___y_1747_ = v___y_1790_;
v___y_1748_ = v___y_1792_;
v___y_1749_ = v___y_1795_;
v___y_1750_ = v___y_1774_;
v___y_1751_ = v___y_1775_;
v___y_1752_ = v___y_1778_;
v___y_1753_ = v___y_1776_;
v___y_1754_ = v___y_1782_;
v___y_1755_ = v___y_1781_;
v___y_1756_ = v___y_1780_;
v___y_1757_ = v___y_1783_;
v___y_1758_ = v___y_1785_;
v___y_1759_ = v___x_1798_;
v___y_1760_ = v___y_1784_;
v___y_1761_ = v___y_1787_;
v___y_1762_ = v___y_1788_;
v___y_1763_ = v___y_1789_;
v___y_1764_ = v___y_1791_;
v___y_1765_ = v___y_1793_;
v___y_1766_ = v___y_1794_;
v___y_1767_ = v___x_1807_;
v___y_1768_ = v___x_1810_;
goto v___jp_1742_;
}
}
v___jp_1811_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_inc_ref(v___y_1833_);
v___x_1835_ = l_Array_append___redArg(v___y_1833_, v___y_1834_);
lean_dec_ref(v___y_1834_);
lean_inc(v___y_1815_);
lean_inc(v___y_1827_);
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___y_1827_);
lean_ctor_set(v___x_1836_, 1, v___y_1815_);
lean_ctor_set(v___x_1836_, 2, v___x_1835_);
if (lean_obj_tag(v___y_1830_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_val_1837_ = lean_ctor_get(v___y_1830_, 0);
v___x_1838_ = l_Lean_SourceInfo_fromRef(v_val_1837_, v___x_1255_);
v___x_1839_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Array_mkArray1___redArg(v___x_1840_);
v___y_1773_ = v___y_1812_;
v___y_1774_ = v___y_1813_;
v___y_1775_ = v___y_1814_;
v___y_1776_ = v___y_1815_;
v___y_1777_ = v___y_1816_;
v___y_1778_ = v___y_1817_;
v___y_1779_ = v___y_1818_;
v___y_1780_ = v___y_1819_;
v___y_1781_ = v___y_1820_;
v___y_1782_ = v___y_1821_;
v___y_1783_ = v___y_1822_;
v___y_1784_ = v___y_1825_;
v___y_1785_ = v___y_1824_;
v___y_1786_ = v___y_1823_;
v___y_1787_ = v___y_1826_;
v___y_1788_ = v___x_1836_;
v___y_1789_ = v___y_1827_;
v___y_1790_ = v___y_1828_;
v___y_1791_ = v___y_1829_;
v___y_1792_ = v___y_1830_;
v___y_1793_ = v___y_1832_;
v___y_1794_ = v___y_1831_;
v___y_1795_ = v___y_1833_;
v___y_1796_ = v___x_1841_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1773_ = v___y_1812_;
v___y_1774_ = v___y_1813_;
v___y_1775_ = v___y_1814_;
v___y_1776_ = v___y_1815_;
v___y_1777_ = v___y_1816_;
v___y_1778_ = v___y_1817_;
v___y_1779_ = v___y_1818_;
v___y_1780_ = v___y_1819_;
v___y_1781_ = v___y_1820_;
v___y_1782_ = v___y_1821_;
v___y_1783_ = v___y_1822_;
v___y_1784_ = v___y_1825_;
v___y_1785_ = v___y_1824_;
v___y_1786_ = v___y_1823_;
v___y_1787_ = v___y_1826_;
v___y_1788_ = v___x_1836_;
v___y_1789_ = v___y_1827_;
v___y_1790_ = v___y_1828_;
v___y_1791_ = v___y_1829_;
v___y_1792_ = v___y_1830_;
v___y_1793_ = v___y_1832_;
v___y_1794_ = v___y_1831_;
v___y_1795_ = v___y_1833_;
v___y_1796_ = v___x_1842_;
goto v___jp_1772_;
}
}
v___jp_1843_:
{
lean_object* v_ref_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_ref_1862_ = lean_ctor_get(v___y_1851_, 2);
v___x_1863_ = l_Lean_SourceInfo_fromRef(v_ref_1862_, v___y_1861_);
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
lean_inc_ref(v___x_1256_);
v___x_1865_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_1864_);
v___x_1866_ = l_Lean_SourceInfo_fromRef(v_tk_1271_, v___x_1255_);
v___x_1867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v___x_1864_);
v___x_1868_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1869_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1854_) == 1)
{
lean_object* v_val_1870_; lean_object* v___x_1871_; 
v_val_1870_ = lean_ctor_get(v___y_1854_, 0);
lean_inc(v_val_1870_);
v___x_1871_ = l_Array_mkArray1___redArg(v_val_1870_);
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___x_1865_;
v___y_1814_ = v___y_1845_;
v___y_1815_ = v___x_1868_;
v___y_1816_ = v___y_1846_;
v___y_1817_ = v___x_1867_;
v___y_1818_ = v___y_1847_;
v___y_1819_ = v___y_1848_;
v___y_1820_ = v___y_1849_;
v___y_1821_ = v___y_1850_;
v___y_1822_ = v___y_1851_;
v___y_1823_ = v___y_1852_;
v___y_1824_ = v___y_1853_;
v___y_1825_ = v___y_1854_;
v___y_1826_ = v___y_1855_;
v___y_1827_ = v___x_1863_;
v___y_1828_ = v___y_1856_;
v___y_1829_ = v___y_1857_;
v___y_1830_ = v___y_1858_;
v___y_1831_ = v___y_1860_;
v___y_1832_ = v___y_1859_;
v___y_1833_ = v___x_1869_;
v___y_1834_ = v___x_1871_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___x_1865_;
v___y_1814_ = v___y_1845_;
v___y_1815_ = v___x_1868_;
v___y_1816_ = v___y_1846_;
v___y_1817_ = v___x_1867_;
v___y_1818_ = v___y_1847_;
v___y_1819_ = v___y_1848_;
v___y_1820_ = v___y_1849_;
v___y_1821_ = v___y_1850_;
v___y_1822_ = v___y_1851_;
v___y_1823_ = v___y_1852_;
v___y_1824_ = v___y_1853_;
v___y_1825_ = v___y_1854_;
v___y_1826_ = v___y_1855_;
v___y_1827_ = v___x_1863_;
v___y_1828_ = v___y_1856_;
v___y_1829_ = v___y_1857_;
v___y_1830_ = v___y_1858_;
v___y_1831_ = v___y_1860_;
v___y_1832_ = v___y_1859_;
v___y_1833_ = v___x_1869_;
v___y_1834_ = v___x_1872_;
goto v___jp_1811_;
}
}
v___jp_1873_:
{
if (lean_obj_tag(v___y_1877_) == 0)
{
uint8_t v___x_1891_; 
v___x_1891_ = 0;
v___y_1844_ = v___y_1874_;
v___y_1845_ = v___y_1876_;
v___y_1846_ = v___y_1890_;
v___y_1847_ = v___y_1887_;
v___y_1848_ = v___y_1883_;
v___y_1849_ = v___y_1884_;
v___y_1850_ = v___y_1885_;
v___y_1851_ = v___y_1889_;
v___y_1852_ = v___y_1880_;
v___y_1853_ = v___y_1886_;
v___y_1854_ = v___y_1881_;
v___y_1855_ = v___y_1875_;
v___y_1856_ = v___y_1877_;
v___y_1857_ = v___y_1878_;
v___y_1858_ = v___y_1879_;
v___y_1859_ = v___y_1888_;
v___y_1860_ = v_argsArray_1882_;
v___y_1861_ = v___x_1891_;
goto v___jp_1843_;
}
else
{
if (v___y_1880_ == 0)
{
v___y_1844_ = v___y_1874_;
v___y_1845_ = v___y_1876_;
v___y_1846_ = v___y_1890_;
v___y_1847_ = v___y_1887_;
v___y_1848_ = v___y_1883_;
v___y_1849_ = v___y_1884_;
v___y_1850_ = v___y_1885_;
v___y_1851_ = v___y_1889_;
v___y_1852_ = v___y_1880_;
v___y_1853_ = v___y_1886_;
v___y_1854_ = v___y_1881_;
v___y_1855_ = v___y_1875_;
v___y_1856_ = v___y_1877_;
v___y_1857_ = v___y_1878_;
v___y_1858_ = v___y_1879_;
v___y_1859_ = v___y_1888_;
v___y_1860_ = v_argsArray_1882_;
v___y_1861_ = v___y_1880_;
goto v___jp_1843_;
}
else
{
lean_object* v_ref_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_ref_1892_ = lean_ctor_get(v___y_1889_, 2);
v___x_1893_ = 0;
v___x_1894_ = l_Lean_SourceInfo_fromRef(v_ref_1892_, v___x_1893_);
v___x_1895_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
lean_inc_ref(v___x_1256_);
v___x_1896_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_1895_);
v___x_1897_ = l_Lean_SourceInfo_fromRef(v_tk_1271_, v___x_1255_);
v___x_1898_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1901_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1881_) == 1)
{
lean_object* v_val_1902_; lean_object* v___x_1903_; 
v_val_1902_ = lean_ctor_get(v___y_1881_, 0);
lean_inc(v_val_1902_);
v___x_1903_ = l_Array_mkArray1___redArg(v_val_1902_);
v___y_1711_ = v___y_1874_;
v___y_1712_ = v___x_1900_;
v___y_1713_ = v___y_1876_;
v___y_1714_ = v___y_1890_;
v___y_1715_ = v___x_1896_;
v___y_1716_ = v___y_1887_;
v___y_1717_ = v___y_1883_;
v___y_1718_ = v___y_1884_;
v___y_1719_ = v___y_1885_;
v___y_1720_ = v___y_1889_;
v___y_1721_ = v___y_1880_;
v___y_1722_ = v___y_1881_;
v___y_1723_ = v___y_1886_;
v___y_1724_ = v___x_1894_;
v___y_1725_ = v___y_1875_;
v___y_1726_ = v___y_1877_;
v___y_1727_ = v___x_1899_;
v___y_1728_ = v___y_1878_;
v___y_1729_ = v___y_1879_;
v___y_1730_ = v_argsArray_1882_;
v___y_1731_ = v___y_1888_;
v___y_1732_ = v___x_1901_;
v___y_1733_ = v___x_1903_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1904_; 
v___x_1904_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1711_ = v___y_1874_;
v___y_1712_ = v___x_1900_;
v___y_1713_ = v___y_1876_;
v___y_1714_ = v___y_1890_;
v___y_1715_ = v___x_1896_;
v___y_1716_ = v___y_1887_;
v___y_1717_ = v___y_1883_;
v___y_1718_ = v___y_1884_;
v___y_1719_ = v___y_1885_;
v___y_1720_ = v___y_1889_;
v___y_1721_ = v___y_1880_;
v___y_1722_ = v___y_1881_;
v___y_1723_ = v___y_1886_;
v___y_1724_ = v___x_1894_;
v___y_1725_ = v___y_1875_;
v___y_1726_ = v___y_1877_;
v___y_1727_ = v___x_1899_;
v___y_1728_ = v___y_1878_;
v___y_1729_ = v___y_1879_;
v___y_1730_ = v_argsArray_1882_;
v___y_1731_ = v___y_1888_;
v___y_1732_ = v___x_1901_;
v___y_1733_ = v___x_1904_;
goto v___jp_1710_;
}
}
}
}
v___jp_1905_:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1913_, v___y_1921_, v___y_1907_, v___y_1909_, v___y_1912_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l_Lean_LibrarySuggestions_select(v_a_1925_, v___y_1923_, v___y_1921_, v___y_1907_, v___y_1909_, v___y_1912_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; size_t v_sz_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v_sz_1928_ = lean_array_size(v_a_1927_);
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1927_, v_sz_1928_, v___x_1929_, v___y_1920_, v___y_1916_, v___y_1913_, v___y_1910_, v___y_1911_, v___y_1921_, v___y_1907_, v___y_1909_, v___y_1912_);
lean_dec(v_a_1927_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___y_1874_ = v___y_1906_;
v___y_1875_ = v___y_1917_;
v___y_1876_ = v___y_1908_;
v___y_1877_ = v___y_1918_;
v___y_1878_ = v___y_1919_;
v___y_1879_ = v___y_1922_;
v___y_1880_ = v___y_1915_;
v___y_1881_ = v___y_1914_;
v_argsArray_1882_ = v_a_1931_;
v___y_1883_ = v___y_1916_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___y_1910_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1921_;
v___y_1888_ = v___y_1907_;
v___y_1889_ = v___y_1909_;
v___y_1890_ = v___y_1912_;
goto v___jp_1873_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v___y_1922_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec(v___y_1914_);
lean_dec(v___y_1908_);
lean_dec(v___y_1906_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v_a_1932_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1930_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1930_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec(v___y_1914_);
lean_dec(v___y_1908_);
lean_dec(v___y_1906_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v_a_1940_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1926_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1926_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec(v___y_1914_);
lean_dec(v___y_1908_);
lean_dec(v___y_1906_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v_a_1948_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1924_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1924_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
v___jp_1956_:
{
lean_object* v_config_1975_; uint8_t v_suggestions_1976_; 
v_config_1975_ = lean_ctor_get(v___y_1973_, 0);
lean_inc_ref(v_config_1975_);
lean_dec_ref(v___y_1973_);
v_suggestions_1976_ = lean_ctor_get_uint8(v_config_1975_, sizeof(void*)*3 + 26);
if (v_suggestions_1976_ == 0)
{
lean_dec_ref(v_config_1975_);
lean_dec_ref(v___f_1259_);
v___y_1874_ = v___y_1957_;
v___y_1875_ = v___y_1968_;
v___y_1876_ = v___y_1959_;
v___y_1877_ = v___y_1969_;
v___y_1878_ = v___y_1970_;
v___y_1879_ = v___y_1972_;
v___y_1880_ = v___y_1966_;
v___y_1881_ = v___y_1965_;
v_argsArray_1882_ = v___y_1974_;
v___y_1883_ = v___y_1967_;
v___y_1884_ = v___y_1964_;
v___y_1885_ = v___y_1961_;
v___y_1886_ = v___y_1962_;
v___y_1887_ = v___y_1971_;
v___y_1888_ = v___y_1958_;
v___y_1889_ = v___y_1960_;
v___y_1890_ = v___y_1963_;
goto v___jp_1873_;
}
else
{
lean_object* v_maxSuggestions_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_maxSuggestions_1977_ = lean_ctor_get(v_config_1975_, 2);
lean_inc(v_maxSuggestions_1977_);
lean_dec_ref(v_config_1975_);
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1979_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1977_) == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_unsigned_to_nat(100u);
v___x_1981_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1978_);
lean_ctor_set(v___x_1981_, 2, v___f_1259_);
lean_ctor_set(v___x_1981_, 3, v___x_1979_);
v___y_1906_ = v___y_1957_;
v___y_1907_ = v___y_1958_;
v___y_1908_ = v___y_1959_;
v___y_1909_ = v___y_1960_;
v___y_1910_ = v___y_1961_;
v___y_1911_ = v___y_1962_;
v___y_1912_ = v___y_1963_;
v___y_1913_ = v___y_1964_;
v___y_1914_ = v___y_1965_;
v___y_1915_ = v___y_1966_;
v___y_1916_ = v___y_1967_;
v___y_1917_ = v___y_1968_;
v___y_1918_ = v___y_1969_;
v___y_1919_ = v___y_1970_;
v___y_1920_ = v___y_1974_;
v___y_1921_ = v___y_1971_;
v___y_1922_ = v___y_1972_;
v___y_1923_ = v___x_1981_;
goto v___jp_1905_;
}
else
{
lean_object* v_val_1982_; lean_object* v___x_1983_; 
v_val_1982_ = lean_ctor_get(v_maxSuggestions_1977_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v_maxSuggestions_1977_, 1);
v___x_1983_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1983_, 0, v_val_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1978_);
lean_ctor_set(v___x_1983_, 2, v___f_1259_);
lean_ctor_set(v___x_1983_, 3, v___x_1979_);
v___y_1906_ = v___y_1957_;
v___y_1907_ = v___y_1958_;
v___y_1908_ = v___y_1959_;
v___y_1909_ = v___y_1960_;
v___y_1910_ = v___y_1961_;
v___y_1911_ = v___y_1962_;
v___y_1912_ = v___y_1963_;
v___y_1913_ = v___y_1964_;
v___y_1914_ = v___y_1965_;
v___y_1915_ = v___y_1966_;
v___y_1916_ = v___y_1967_;
v___y_1917_ = v___y_1968_;
v___y_1918_ = v___y_1969_;
v___y_1919_ = v___y_1970_;
v___y_1920_ = v___y_1974_;
v___y_1921_ = v___y_1971_;
v___y_1922_ = v___y_1972_;
v___y_1923_ = v___x_1983_;
goto v___jp_1905_;
}
}
}
v___jp_1984_:
{
uint8_t v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = 0;
lean_inc(v___y_1985_);
v___x_2001_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1985_, v___x_2000_, v___y_1995_, v___y_1987_, v___y_1993_);
if (lean_obj_tag(v___x_2001_) == 0)
{
if (lean_obj_tag(v___y_1991_) == 1)
{
lean_object* v_a_2002_; lean_object* v_val_2003_; lean_object* v___x_2004_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v_val_2003_ = lean_ctor_get(v___y_1991_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v___y_1991_, 1);
v___x_2004_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_2003_);
lean_dec(v_val_2003_);
lean_inc(v___y_1990_);
v___y_1957_ = v___y_1990_;
v___y_1958_ = v___y_1986_;
v___y_1959_ = v___y_1985_;
v___y_1960_ = v___y_1987_;
v___y_1961_ = v___y_1994_;
v___y_1962_ = v___y_1988_;
v___y_1963_ = v___y_1993_;
v___y_1964_ = v___y_1996_;
v___y_1965_ = v___y_1999_;
v___y_1966_ = v___y_1989_;
v___y_1967_ = v___y_1995_;
v___y_1968_ = v___x_2000_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_1990_;
v___y_1971_ = v___y_1992_;
v___y_1972_ = v___y_1997_;
v___y_1973_ = v_a_2002_;
v___y_1974_ = v___x_2004_;
goto v___jp_1956_;
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
lean_dec(v___y_1991_);
v_a_2005_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1990_);
v___y_1957_ = v___y_1990_;
v___y_1958_ = v___y_1986_;
v___y_1959_ = v___y_1985_;
v___y_1960_ = v___y_1987_;
v___y_1961_ = v___y_1994_;
v___y_1962_ = v___y_1988_;
v___y_1963_ = v___y_1993_;
v___y_1964_ = v___y_1996_;
v___y_1965_ = v___y_1999_;
v___y_1966_ = v___y_1989_;
v___y_1967_ = v___y_1995_;
v___y_1968_ = v___x_2000_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_1990_;
v___y_1971_ = v___y_1992_;
v___y_1972_ = v___y_1997_;
v___y_1973_ = v_a_2005_;
v___y_1974_ = v___x_2006_;
goto v___jp_1956_;
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v___y_1985_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v_a_2007_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_2001_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2001_);
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
v___jp_2015_:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Syntax_getOptional_x3f(v___y_2023_);
lean_dec(v___y_2023_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_box(0);
v___y_1985_ = v___y_2017_;
v___y_1986_ = v___y_2016_;
v___y_1987_ = v___y_2018_;
v___y_1988_ = v___y_2020_;
v___y_1989_ = v___y_2024_;
v___y_1990_ = v___y_2030_;
v___y_1991_ = v___y_2029_;
v___y_1992_ = v___y_2027_;
v___y_1993_ = v___y_2021_;
v___y_1994_ = v___y_2019_;
v___y_1995_ = v___y_2025_;
v___y_1996_ = v___y_2022_;
v___y_1997_ = v___y_2028_;
v___y_1998_ = v___y_2026_;
v___y_1999_ = v___x_2032_;
goto v___jp_1984_;
}
else
{
lean_object* v_val_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_val_2033_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2031_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_val_2033_);
lean_dec(v___x_2031_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_val_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
v___y_1985_ = v___y_2017_;
v___y_1986_ = v___y_2016_;
v___y_1987_ = v___y_2018_;
v___y_1988_ = v___y_2020_;
v___y_1989_ = v___y_2024_;
v___y_1990_ = v___y_2030_;
v___y_1991_ = v___y_2029_;
v___y_1992_ = v___y_2027_;
v___y_1993_ = v___y_2021_;
v___y_1994_ = v___y_2019_;
v___y_1995_ = v___y_2025_;
v___y_1996_ = v___y_2022_;
v___y_1997_ = v___y_2028_;
v___y_1998_ = v___y_2026_;
v___y_1999_ = v___x_2038_;
goto v___jp_1984_;
}
}
}
}
v___jp_2041_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_unsigned_to_nat(4u);
v___x_2058_ = l_Lean_Syntax_getArg(v___y_2043_, v___x_2057_);
lean_dec(v___y_2043_);
v___x_2059_ = l_Lean_Syntax_getOptional_x3f(v___x_2058_);
lean_dec(v___x_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_box(0);
v___y_2016_ = v___y_2054_;
v___y_2017_ = v___y_2042_;
v___y_2018_ = v___y_2055_;
v___y_2019_ = v___y_2051_;
v___y_2020_ = v___y_2052_;
v___y_2021_ = v___y_2056_;
v___y_2022_ = v___y_2050_;
v___y_2023_ = v___y_2046_;
v___y_2024_ = v___y_2047_;
v___y_2025_ = v___y_2049_;
v___y_2026_ = v___y_2044_;
v___y_2027_ = v___y_2053_;
v___y_2028_ = v___y_2045_;
v___y_2029_ = v_args_2048_;
v___y_2030_ = v___x_2060_;
goto v___jp_2015_;
}
else
{
lean_object* v_val_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_val_2061_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2059_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_val_2061_);
lean_dec(v___x_2059_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_val_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v___y_2016_ = v___y_2054_;
v___y_2017_ = v___y_2042_;
v___y_2018_ = v___y_2055_;
v___y_2019_ = v___y_2051_;
v___y_2020_ = v___y_2052_;
v___y_2021_ = v___y_2056_;
v___y_2022_ = v___y_2050_;
v___y_2023_ = v___y_2046_;
v___y_2024_ = v___y_2047_;
v___y_2025_ = v___y_2049_;
v___y_2026_ = v___y_2044_;
v___y_2027_ = v___y_2053_;
v___y_2028_ = v___y_2045_;
v___y_2029_ = v_args_2048_;
v___y_2030_ = v___x_2066_;
goto v___jp_2015_;
}
}
}
}
v___jp_2070_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2085_ = lean_unsigned_to_nat(3u);
v___x_2086_ = l_Lean_Syntax_getArg(v___y_2072_, v___x_2085_);
v___x_2087_ = l_Lean_Syntax_isNone(v___x_2086_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; 
lean_inc(v___x_2086_);
v___x_2088_ = l_Lean_Syntax_matchesNull(v___x_2086_, v___x_2069_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v___x_2086_);
lean_dec(v_o_2076_);
lean_dec(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_2089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2090_ = l_Lean_Syntax_getArg(v___x_2086_, v___x_1270_);
lean_dec(v___x_2086_);
v___x_2091_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
lean_inc_ref(v___x_1256_);
v___x_2092_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_2091_);
lean_inc(v___x_2090_);
v___x_2093_ = l_Lean_Syntax_isOfKind(v___x_2090_, v___x_2092_);
lean_dec(v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec(v___x_2090_);
lean_dec(v_o_2076_);
lean_dec(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_2094_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; lean_object* v_args_2096_; lean_object* v___x_2097_; 
v___x_2095_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2069_);
lean_dec(v___x_2090_);
v_args_2096_ = l_Lean_Syntax_getArgs(v___x_2095_);
lean_dec(v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_args_2096_);
v___y_2042_ = v___y_2071_;
v___y_2043_ = v___y_2072_;
v___y_2044_ = v___y_2073_;
v___y_2045_ = v_o_2076_;
v___y_2046_ = v___y_2074_;
v___y_2047_ = v___y_2075_;
v_args_2048_ = v___x_2097_;
v___y_2049_ = v___y_2077_;
v___y_2050_ = v___y_2078_;
v___y_2051_ = v___y_2079_;
v___y_2052_ = v___y_2080_;
v___y_2053_ = v___y_2081_;
v___y_2054_ = v___y_2082_;
v___y_2055_ = v___y_2083_;
v___y_2056_ = v___y_2084_;
goto v___jp_2041_;
}
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v___x_2086_);
v___x_2098_ = lean_box(0);
v___y_2042_ = v___y_2071_;
v___y_2043_ = v___y_2072_;
v___y_2044_ = v___y_2073_;
v___y_2045_ = v_o_2076_;
v___y_2046_ = v___y_2074_;
v___y_2047_ = v___y_2075_;
v_args_2048_ = v___x_2098_;
v___y_2049_ = v___y_2077_;
v___y_2050_ = v___y_2078_;
v___y_2051_ = v___y_2079_;
v___y_2052_ = v___y_2080_;
v___y_2053_ = v___y_2081_;
v___y_2054_ = v___y_2082_;
v___y_2055_ = v___y_2083_;
v___y_2056_ = v___y_2084_;
goto v___jp_2041_;
}
}
v___jp_2099_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2109_ = lean_unsigned_to_nat(2u);
v___x_2110_ = l_Lean_Syntax_getArg(v_stx_1254_, v___x_2109_);
v___x_2111_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
lean_inc_ref(v___x_1256_);
v___x_2112_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_2111_);
lean_inc(v___x_2110_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v___x_2110_, v___x_2112_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v___x_2110_);
lean_dec(v_bang_2100_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_2114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2114_;
}
else
{
lean_object* v_cfg_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v_cfg_2115_ = l_Lean_Syntax_getArg(v___x_2110_, v___x_1270_);
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
lean_inc_ref(v___x_1256_);
v___x_2117_ = l_Lean_Name_mkStr4(v___x_1256_, v___x_1257_, v___x_1258_, v___x_2116_);
lean_inc(v_cfg_2115_);
v___x_2118_ = l_Lean_Syntax_isOfKind(v_cfg_2115_, v___x_2117_);
lean_dec(v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec(v_cfg_2115_);
lean_dec(v___x_2110_);
lean_dec(v_bang_2100_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_2119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = l_Lean_Syntax_getArg(v___x_2110_, v___x_2069_);
v___x_2121_ = l_Lean_Syntax_getArg(v___x_2110_, v___x_2109_);
v___x_2122_ = l_Lean_Syntax_isNone(v___x_2121_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; 
lean_inc(v___x_2121_);
v___x_2123_ = l_Lean_Syntax_matchesNull(v___x_2121_, v___x_2069_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec(v___x_2121_);
lean_dec(v___x_2120_);
lean_dec(v_cfg_2115_);
lean_dec(v___x_2110_);
lean_dec(v_bang_2100_);
lean_dec(v_tk_1271_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1256_);
v___x_2124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2124_;
}
else
{
lean_object* v_o_2125_; lean_object* v___x_2126_; 
v_o_2125_ = l_Lean_Syntax_getArg(v___x_2121_, v___x_1270_);
lean_dec(v___x_2121_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_o_2125_);
v___y_2071_ = v_cfg_2115_;
v___y_2072_ = v___x_2110_;
v___y_2073_ = v_bang_2100_;
v___y_2074_ = v___x_2120_;
v___y_2075_ = v___x_2113_;
v_o_2076_ = v___x_2126_;
v___y_2077_ = v___y_2101_;
v___y_2078_ = v___y_2102_;
v___y_2079_ = v___y_2103_;
v___y_2080_ = v___y_2104_;
v___y_2081_ = v___y_2105_;
v___y_2082_ = v___y_2106_;
v___y_2083_ = v___y_2107_;
v___y_2084_ = v___y_2108_;
goto v___jp_2070_;
}
}
else
{
lean_object* v___x_2127_; 
lean_dec(v___x_2121_);
v___x_2127_ = lean_box(0);
v___y_2071_ = v_cfg_2115_;
v___y_2072_ = v___x_2110_;
v___y_2073_ = v_bang_2100_;
v___y_2074_ = v___x_2120_;
v___y_2075_ = v___x_2113_;
v_o_2076_ = v___x_2127_;
v___y_2077_ = v___y_2101_;
v___y_2078_ = v___y_2102_;
v___y_2079_ = v___y_2103_;
v___y_2080_ = v___y_2104_;
v___y_2081_ = v___y_2105_;
v___y_2082_ = v___y_2106_;
v___y_2083_ = v___y_2107_;
v___y_2084_ = v___y_2108_;
goto v___jp_2070_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpTrace___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1253_ = stack[0].m_num;
lean_object* v_stx_1254_ = stack[1].m_obj;
uint8_t v___x_1255_ = stack[2].m_num;
lean_object* v___x_1256_ = stack[3].m_obj;
lean_object* v___x_1257_ = stack[4].m_obj;
lean_object* v___x_1258_ = stack[5].m_obj;
lean_object* v___f_1259_ = stack[6].m_obj;
lean_object* v___y_1260_ = stack[7].m_obj;
lean_object* v___y_1261_ = stack[8].m_obj;
lean_object* v___y_1262_ = stack[9].m_obj;
lean_object* v___y_1263_ = stack[10].m_obj;
lean_object* v___y_1264_ = stack[11].m_obj;
lean_object* v___y_1265_ = stack[12].m_obj;
lean_object* v___y_1266_ = stack[13].m_obj;
lean_object* v___y_1267_ = stack[14].m_obj;
lean_object* v_res_2135_;
v_res_2135_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_1253_, v_stx_1254_, v___x_1255_, v___x_1256_, v___x_1257_, v___x_1258_, v___f_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
stack->m_obj
 = v_res_2135_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2136_, lean_object* v_stx_2137_, lean_object* v___x_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v___f_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
uint8_t v___x_36300__boxed_2152_; uint8_t v___x_36301__boxed_2153_; lean_object* v_res_2154_; 
v___x_36300__boxed_2152_ = lean_unbox(v___x_2136_);
v___x_36301__boxed_2153_ = lean_unbox(v___x_2138_);
v_res_2154_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_36300__boxed_2152_, v_stx_2137_, v___x_36301__boxed_2153_, v___x_2139_, v___x_2140_, v___x_2141_, v___f_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v_stx_2137_);
return v_res_2154_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; uint8_t v___x_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___y_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2164_);
v___x_2178_ = l_Lean_Syntax_isOfKind(v_stx_2164_, v___x_2177_);
v___x_2179_ = 1;
v___f_2180_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2181_ = lean_box(v___x_2178_);
v___x_2182_ = lean_box(v___x_2179_);
v___y_2183_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2183_, 0, v___x_2181_);
lean_closure_set(v___y_2183_, 1, v_stx_2164_);
lean_closure_set(v___y_2183_, 2, v___x_2182_);
lean_closure_set(v___y_2183_, 3, v___x_2174_);
lean_closure_set(v___y_2183_, 4, v___x_2175_);
lean_closure_set(v___y_2183_, 5, v___x_2176_);
lean_closure_set(v___y_2183_, 6, v___f_2180_);
v___x_2184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2184_, 0, v___y_2183_);
v___x_2185_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2184_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2185_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2164_ = stack[0].m_obj;
lean_object* v_a_2165_ = stack[1].m_obj;
lean_object* v_a_2166_ = stack[2].m_obj;
lean_object* v_a_2167_ = stack[3].m_obj;
lean_object* v_a_2168_ = stack[4].m_obj;
lean_object* v_a_2169_ = stack[5].m_obj;
lean_object* v_a_2170_ = stack[6].m_obj;
lean_object* v_a_2171_ = stack[7].m_obj;
lean_object* v_a_2172_ = stack[8].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
return v_res_2197_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2198_, lean_object* v_as_2199_, lean_object* v_as_x27_2200_, lean_object* v_b_2201_, lean_object* v_a_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2198_, v_as_x27_2200_, v_b_2201_, v___y_2209_);
return v___x_2212_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2198_ = stack[0].m_obj;
lean_object* v_as_2199_ = stack[1].m_obj;
lean_object* v_as_x27_2200_ = stack[2].m_obj;
lean_object* v_b_2201_ = stack[3].m_obj;
lean_object* v___y_2203_ = stack[5].m_obj;
lean_object* v___y_2204_ = stack[6].m_obj;
lean_object* v___y_2205_ = stack[7].m_obj;
lean_object* v___y_2206_ = stack[8].m_obj;
lean_object* v___y_2207_ = stack[9].m_obj;
lean_object* v___y_2208_ = stack[10].m_obj;
lean_object* v___y_2209_ = stack[11].m_obj;
lean_object* v___y_2210_ = stack[12].m_obj;
lean_object* v_res_2213_;
v_res_2213_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2198_, v_as_2199_, v_as_x27_2200_, v_b_2201_, lean_box(0), v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
stack->m_obj
 = v_res_2213_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2214_, lean_object* v_as_2215_, lean_object* v_as_x27_2216_, lean_object* v_b_2217_, lean_object* v_a_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2214_, v_as_2215_, v_as_x27_2216_, v_b_2217_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v_as_x27_2216_);
lean_dec(v_as_2215_);
lean_dec(v___x_2214_);
return v_res_2228_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2229_, lean_object* v_ref_2230_, lean_object* v_msg_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2230_, v_msg_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2230_ = stack[1].m_obj;
lean_object* v_msg_2231_ = stack[2].m_obj;
lean_object* v___y_2232_ = stack[3].m_obj;
lean_object* v___y_2233_ = stack[4].m_obj;
lean_object* v___y_2234_ = stack[5].m_obj;
lean_object* v___y_2235_ = stack[6].m_obj;
lean_object* v___y_2236_ = stack[7].m_obj;
lean_object* v___y_2237_ = stack[8].m_obj;
lean_object* v___y_2238_ = stack[9].m_obj;
lean_object* v___y_2239_ = stack[10].m_obj;
lean_object* v_res_2242_;
v_res_2242_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_box(0), v_ref_2230_, v_msg_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
stack->m_obj
 = v_res_2242_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_ref_2244_, lean_object* v_msg_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2243_, v_ref_2244_, v_msg_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v_ref_2244_);
return v_res_2255_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2256_, lean_object* v_ref_2257_, lean_object* v_constName_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2257_, v_constName_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2257_ = stack[1].m_obj;
lean_object* v_constName_2258_ = stack[2].m_obj;
lean_object* v___y_2259_ = stack[3].m_obj;
lean_object* v___y_2260_ = stack[4].m_obj;
lean_object* v___y_2261_ = stack[5].m_obj;
lean_object* v___y_2262_ = stack[6].m_obj;
lean_object* v___y_2263_ = stack[7].m_obj;
lean_object* v___y_2264_ = stack[8].m_obj;
lean_object* v___y_2265_ = stack[9].m_obj;
lean_object* v___y_2266_ = stack[10].m_obj;
lean_object* v_res_2269_;
v_res_2269_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_box(0), v_ref_2257_, v_constName_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
stack->m_obj
 = v_res_2269_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_ref_2271_, lean_object* v_constName_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2270_, v_ref_2271_, v_constName_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v_ref_2271_);
return v_res_2282_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2284_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2284_ = stack[1].m_obj;
lean_object* v___y_2285_ = stack[2].m_obj;
lean_object* v___y_2286_ = stack[3].m_obj;
lean_object* v___y_2287_ = stack[4].m_obj;
lean_object* v___y_2288_ = stack[5].m_obj;
lean_object* v___y_2289_ = stack[6].m_obj;
lean_object* v___y_2290_ = stack[7].m_obj;
lean_object* v___y_2291_ = stack[8].m_obj;
lean_object* v___y_2292_ = stack[9].m_obj;
lean_object* v_res_2295_;
v_res_2295_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_box(0), v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
stack->m_obj
 = v_res_2295_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_msg_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2296_, v_msg_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2307_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2308_, v___y_2315_);
return v___x_2318_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_2308_ = stack[0].m_obj;
lean_object* v___y_2309_ = stack[1].m_obj;
lean_object* v___y_2310_ = stack[2].m_obj;
lean_object* v___y_2311_ = stack[3].m_obj;
lean_object* v___y_2312_ = stack[4].m_obj;
lean_object* v___y_2313_ = stack[5].m_obj;
lean_object* v___y_2314_ = stack[6].m_obj;
lean_object* v___y_2315_ = stack[7].m_obj;
lean_object* v___y_2316_ = stack[8].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v_opt_2320_);
return v_res_2330_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2331_, lean_object* v_ref_2332_, lean_object* v_msg_2333_, lean_object* v_declHint_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2332_, v_msg_2333_, v_declHint_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2332_ = stack[1].m_obj;
lean_object* v_msg_2333_ = stack[2].m_obj;
lean_object* v_declHint_2334_ = stack[3].m_obj;
lean_object* v___y_2335_ = stack[4].m_obj;
lean_object* v___y_2336_ = stack[5].m_obj;
lean_object* v___y_2337_ = stack[6].m_obj;
lean_object* v___y_2338_ = stack[7].m_obj;
lean_object* v___y_2339_ = stack[8].m_obj;
lean_object* v___y_2340_ = stack[9].m_obj;
lean_object* v___y_2341_ = stack[10].m_obj;
lean_object* v___y_2342_ = stack[11].m_obj;
lean_object* v_res_2345_;
v_res_2345_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_box(0), v_ref_2332_, v_msg_2333_, v_declHint_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
stack->m_obj
 = v_res_2345_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_ref_2347_, lean_object* v_msg_2348_, lean_object* v_declHint_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2346_, v_ref_2347_, v_msg_2348_, v_declHint_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v_ref_2347_);
return v_res_2359_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2360_, lean_object* v_declHint_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2360_, v_declHint_2361_, v___y_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2360_ = stack[0].m_obj;
lean_object* v_declHint_2361_ = stack[1].m_obj;
lean_object* v___y_2362_ = stack[2].m_obj;
lean_object* v___y_2363_ = stack[3].m_obj;
lean_object* v___y_2364_ = stack[4].m_obj;
lean_object* v___y_2365_ = stack[5].m_obj;
lean_object* v___y_2366_ = stack[6].m_obj;
lean_object* v___y_2367_ = stack[7].m_obj;
lean_object* v___y_2368_ = stack[8].m_obj;
lean_object* v___y_2369_ = stack[9].m_obj;
lean_object* v_res_2372_;
v_res_2372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2360_, v_declHint_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
stack->m_obj
 = v_res_2372_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2373_, lean_object* v_declHint_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2373_, v_declHint_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2384_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2385_, lean_object* v_msgData_2386_, uint8_t v_severity_2387_, uint8_t v_isSilent_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2385_, v_msgData_2386_, v_severity_2387_, v_isSilent_2388_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2385_ = stack[0].m_obj;
lean_object* v_msgData_2386_ = stack[1].m_obj;
uint8_t v_severity_2387_ = stack[2].m_num;
uint8_t v_isSilent_2388_ = stack[3].m_num;
lean_object* v___y_2389_ = stack[4].m_obj;
lean_object* v___y_2390_ = stack[5].m_obj;
lean_object* v___y_2391_ = stack[6].m_obj;
lean_object* v___y_2392_ = stack[7].m_obj;
lean_object* v___y_2393_ = stack[8].m_obj;
lean_object* v___y_2394_ = stack[9].m_obj;
lean_object* v___y_2395_ = stack[10].m_obj;
lean_object* v___y_2396_ = stack[11].m_obj;
lean_object* v_res_2399_;
v_res_2399_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2385_, v_msgData_2386_, v_severity_2387_, v_isSilent_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
stack->m_obj
 = v_res_2399_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2400_, lean_object* v_msgData_2401_, lean_object* v_severity_2402_, lean_object* v_isSilent_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_severity_boxed_2413_; uint8_t v_isSilent_boxed_2414_; lean_object* v_res_2415_; 
v_severity_boxed_2413_ = lean_unbox(v_severity_2402_);
v_isSilent_boxed_2414_ = lean_unbox(v_isSilent_2403_);
v_res_2415_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2400_, v_msgData_2401_, v_severity_boxed_2413_, v_isSilent_boxed_2414_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v_ref_2400_);
return v_res_2415_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2423_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2424_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2426_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2427_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2423_, v___x_2424_, v___x_2425_, v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2428_;
v_res_2428_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
stack->m_obj
 = v_res_2428_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2430_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2459_ = l_Lean_addBuiltinDeclarationRanges(v___x_2457_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2460_;
v_res_2460_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
stack->m_obj
 = v_res_2460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2462_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2463_, lean_object* v_as_x27_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_){
_start:
{
if (lean_obj_tag(v_as_x27_2464_) == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v_b_2465_);
return v___x_2468_;
}
else
{
lean_object* v_head_2469_; lean_object* v_tail_2470_; lean_object* v_ref_2471_; uint8_t v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_head_2469_ = lean_ctor_get(v_as_x27_2464_, 0);
v_tail_2470_ = lean_ctor_get(v_as_x27_2464_, 1);
v_ref_2471_ = lean_ctor_get(v___y_2466_, 2);
v___x_2472_ = 1;
v___x_2473_ = 0;
v___x_2474_ = l_Lean_SourceInfo_fromRef(v_ref_2471_, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2476_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2477_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2474_);
v___x_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2474_);
lean_ctor_set(v___x_2478_, 1, v___x_2476_);
lean_ctor_set(v___x_2478_, 2, v___x_2477_);
lean_inc(v_head_2469_);
v___x_2479_ = l_Lean_mkCIdentFrom(v___x_2463_, v_head_2469_, v___x_2472_);
lean_inc_ref(v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node3(v___x_2474_, v___x_2475_, v___x_2478_, v___x_2478_, v___x_2479_);
v___x_2481_ = lean_array_push(v_b_2465_, v___x_2480_);
v_as_x27_2464_ = v_tail_2470_;
v_b_2465_ = v___x_2481_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2463_ = stack[0].m_obj;
lean_object* v_as_x27_2464_ = stack[1].m_obj;
lean_object* v_b_2465_ = stack[2].m_obj;
lean_object* v___y_2466_ = stack[3].m_obj;
lean_object* v_res_2483_;
v_res_2483_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2463_, v_as_x27_2464_, v_b_2465_, v___y_2466_);
stack->m_obj
 = v_res_2483_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2484_, lean_object* v_as_x27_2485_, lean_object* v_b_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2484_, v_as_x27_2485_, v_b_2486_, v___y_2487_);
lean_dec_ref(v___y_2487_);
lean_dec(v_as_x27_2485_);
lean_dec(v___x_2484_);
return v_res_2489_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2490_, size_t v_sz_2491_, size_t v_i_2492_, lean_object* v_b_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_lt(v_i_2492_, v_sz_2491_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_b_2493_);
return v___x_2504_;
}
else
{
lean_object* v_a_2505_; lean_object* v_name_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_a_2505_ = lean_array_uget_borrowed(v_as_2490_, v_i_2492_);
v_name_2506_ = lean_ctor_get(v_a_2505_, 0);
lean_inc(v_name_2506_);
v___x_2507_ = l_Lean_mkIdent(v_name_2506_);
lean_inc(v___x_2507_);
v___x_2508_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2507_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2510_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2507_, v_a_2509_, v_b_2493_, v___y_2500_);
lean_dec(v_a_2509_);
lean_dec(v___x_2507_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; size_t v___x_2512_; size_t v___x_2513_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v___x_2512_ = ((size_t)1ULL);
v___x_2513_ = lean_usize_add(v_i_2492_, v___x_2512_);
v_i_2492_ = v___x_2513_;
v_b_2493_ = v_a_2511_;
goto _start;
}
else
{
return v___x_2510_;
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v___x_2507_);
lean_dec_ref(v_b_2493_);
v_a_2515_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2508_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2508_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2490_ = stack[0].m_obj;
size_t v_sz_2491_ = stack[1].m_num;
size_t v_i_2492_ = stack[2].m_num;
lean_object* v_b_2493_ = stack[3].m_obj;
lean_object* v___y_2494_ = stack[4].m_obj;
lean_object* v___y_2495_ = stack[5].m_obj;
lean_object* v___y_2496_ = stack[6].m_obj;
lean_object* v___y_2497_ = stack[7].m_obj;
lean_object* v___y_2498_ = stack[8].m_obj;
lean_object* v___y_2499_ = stack[9].m_obj;
lean_object* v___y_2500_ = stack[10].m_obj;
lean_object* v___y_2501_ = stack[11].m_obj;
lean_object* v_res_2523_;
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2490_, v_sz_2491_, v_i_2492_, v_b_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
stack->m_obj
 = v_res_2523_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2524_, lean_object* v_sz_2525_, lean_object* v_i_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
size_t v_sz_boxed_2537_; size_t v_i_boxed_2538_; lean_object* v_res_2539_; 
v_sz_boxed_2537_ = lean_unbox_usize(v_sz_2525_);
lean_dec(v_sz_2525_);
v_i_boxed_2538_ = lean_unbox_usize(v_i_2526_);
lean_dec(v_i_2526_);
v_res_2539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2524_, v_sz_boxed_2537_, v_i_boxed_2538_, v_b_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v_as_2524_);
return v_res_2539_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(32u);
v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2548_ = ((size_t)5ULL);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_unsigned_to_nat(32u);
v___x_2551_ = lean_mk_empty_array_with_capacity(v___x_2550_);
v___x_2552_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2553_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___x_2551_);
lean_ctor_set(v___x_2553_, 2, v___x_2549_);
lean_ctor_set(v___x_2553_, 3, v___x_2549_);
lean_ctor_set_usize(v___x_2553_, 4, v___x_2548_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2555_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
lean_ctor_set(v___x_2556_, 2, v___x_2555_);
lean_ctor_set(v___x_2556_, 3, v___x_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2558_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2557_);
return v___x_2559_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2568_, lean_object* v_stx_2569_, uint8_t v___x_2570_, lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v___x_2573_, lean_object* v___f_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
if (v___x_2568_ == 0)
{
lean_object* v___x_2584_; 
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_2584_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v_tk_2586_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2701_; uint8_t v___y_2702_; lean_object* v___y_2703_; uint8_t v___y_2704_; lean_object* v_stxForSuggestion_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2733_; uint8_t v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; uint8_t v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; uint8_t v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; uint8_t v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; uint8_t v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; uint8_t v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; uint8_t v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; uint8_t v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2940_; lean_object* v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2969_; lean_object* v___y_2970_; uint8_t v___y_2971_; lean_object* v___y_2972_; uint8_t v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___y_2985_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; uint8_t v___y_3002_; uint8_t v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v_stxForExecution_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; uint8_t v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; uint8_t v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; uint8_t v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; uint8_t v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; uint8_t v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; uint8_t v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; uint8_t v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; uint8_t v___y_3317_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; lean_object* v_argsArray_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; uint8_t v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; uint8_t v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; uint8_t v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v_args_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___x_3516_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; lean_object* v_o_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v_bang_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_2585_ = lean_unsigned_to_nat(0u);
v_tk_2586_ = l_Lean_Syntax_getArg(v_stx_2569_, v___x_2585_);
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3575_ = l_Lean_Syntax_getArg(v_stx_2569_, v___x_3516_);
v___x_3576_ = l_Lean_Syntax_isNone(v___x_3575_);
if (v___x_3576_ == 0)
{
uint8_t v___x_3577_; 
lean_inc(v___x_3575_);
v___x_3577_ = l_Lean_Syntax_matchesNull(v___x_3575_, v___x_3516_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; 
lean_dec(v___x_3575_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_3578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3578_;
}
else
{
lean_object* v_bang_3579_; lean_object* v___x_3580_; 
v_bang_3579_ = l_Lean_Syntax_getArg(v___x_3575_, v___x_2585_);
lean_dec(v___x_3575_);
v___x_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3580_, 0, v_bang_3579_);
v_bang_3547_ = v___x_3580_;
v___y_3548_ = v___y_2575_;
v___y_3549_ = v___y_2576_;
v___y_3550_ = v___y_2577_;
v___y_3551_ = v___y_2578_;
v___y_3552_ = v___y_2579_;
v___y_3553_ = v___y_2580_;
v___y_3554_ = v___y_2581_;
v___y_3555_ = v___y_2582_;
goto v___jp_3546_;
}
}
else
{
lean_object* v___x_3581_; 
lean_dec(v___x_3575_);
v___x_3581_ = lean_box(0);
v_bang_3547_ = v___x_3581_;
v___y_3548_ = v___y_2575_;
v___y_3549_ = v___y_2576_;
v___y_3550_ = v___y_2577_;
v___y_3551_ = v___y_2578_;
v___y_3552_ = v___y_2579_;
v___y_3553_ = v___y_2580_;
v___y_3554_ = v___y_2581_;
v___y_3555_ = v___y_2582_;
goto v___jp_3546_;
}
v___jp_2587_:
{
lean_object* v_usedTheorems_2594_; lean_object* v_diag_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2637_; 
v_usedTheorems_2594_ = lean_ctor_get(v___y_2588_, 0);
v_diag_2595_ = lean_ctor_get(v___y_2588_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___y_2588_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2597_ = v___y_2588_;
v_isShared_2598_ = v_isSharedCheck_2637_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_diag_2595_);
lean_inc(v_usedTheorems_2594_);
lean_dec(v___y_2588_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2637_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2589_, v_usedTheorems_2594_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec_ref(v_usedTheorems_2594_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_ref_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_ref_2601_ = lean_ctor_get(v___y_2592_, 2);
v___x_2602_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 1, v_a_2600_);
lean_ctor_set(v___x_2597_, 0, v___x_2602_);
v___x_2604_ = v___x_2597_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_a_2600_);
v___x_2604_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_ctor_set(v___x_2606_, 2, v___x_2605_);
lean_ctor_set(v___x_2606_, 3, v___x_2605_);
lean_ctor_set(v___x_2606_, 4, v___x_2605_);
lean_ctor_set(v___x_2606_, 5, v___x_2605_);
lean_inc(v_ref_2601_);
v___x_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_ref_2601_);
v___x_2608_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2609_ = 4;
v___x_2610_ = l_Lean_MessageData_nil;
v___x_2611_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2586_, v___x_2606_, v___x_2607_, v___x_2608_, v___x_2605_, v___x_2609_, v___x_2610_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v___x_2611_, 0);
lean_dec(v_unused_2619_);
v___x_2613_ = v___x_2611_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_dec(v___x_2611_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v_diag_2595_);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_diag_2595_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_diag_2595_);
v_a_2620_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2611_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2611_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2597_);
lean_dec_ref(v_diag_2595_);
lean_dec(v_tk_2586_);
v_a_2629_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2599_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2599_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
v___jp_2638_:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2639_, v___y_2644_, v___y_2645_, v___y_2640_, v___y_2642_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2650_ = l_Lean_Meta_simpAll(v_a_2648_, v___y_2646_, v___y_2641_, v___x_2649_, v___y_2644_, v___y_2645_, v___y_2640_, v___y_2642_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_fst_2652_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_fst_2652_ = lean_ctor_get(v_a_2651_, 0);
if (lean_obj_tag(v_fst_2652_) == 0)
{
lean_object* v_snd_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v_snd_2653_ = lean_ctor_get(v_a_2651_, 1);
lean_inc(v_snd_2653_);
lean_dec(v_a_2651_);
v___x_2654_ = lean_box(0);
v___x_2655_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2654_, v___y_2639_, v___y_2644_, v___y_2645_, v___y_2640_, v___y_2642_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_dec_ref_known(v___x_2655_, 1);
v___y_2588_ = v_snd_2653_;
v___y_2589_ = v___y_2643_;
v___y_2590_ = v___y_2644_;
v___y_2591_ = v___y_2645_;
v___y_2592_ = v___y_2640_;
v___y_2593_ = v___y_2642_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_snd_2653_);
lean_dec(v___y_2643_);
lean_dec(v_tk_2586_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_snd_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2682_; 
lean_inc_ref(v_fst_2652_);
v_snd_2664_ = lean_ctor_get(v_a_2651_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v_a_2651_, 0);
lean_dec(v_unused_2683_);
v___x_2666_ = v_a_2651_;
v_isShared_2667_ = v_isSharedCheck_2682_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_snd_2664_);
lean_dec(v_a_2651_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2682_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_val_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v_val_2668_ = lean_ctor_get(v_fst_2652_, 0);
lean_inc(v_val_2668_);
lean_dec_ref_known(v_fst_2652_, 1);
v___x_2669_ = lean_box(0);
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 1);
lean_ctor_set(v___x_2666_, 1, v___x_2669_);
lean_ctor_set(v___x_2666_, 0, v_val_2668_);
v___x_2671_ = v___x_2666_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_val_2668_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2671_, v___y_2639_, v___y_2644_, v___y_2645_, v___y_2640_, v___y_2642_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_dec_ref_known(v___x_2672_, 1);
v___y_2588_ = v_snd_2664_;
v___y_2589_ = v___y_2643_;
v___y_2590_ = v___y_2644_;
v___y_2591_ = v___y_2645_;
v___y_2592_ = v___y_2640_;
v___y_2593_ = v___y_2642_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_snd_2664_);
lean_dec(v___y_2643_);
lean_dec(v_tk_2586_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v___y_2643_);
lean_dec(v_tk_2586_);
v_a_2684_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2650_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2650_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2641_);
lean_dec(v_tk_2586_);
v_a_2692_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2647_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2647_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2715_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2703_, v___x_2570_, v___y_2702_, v___x_2570_, v___x_2714_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2703_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
if (lean_obj_tag(v___y_2701_) == 0)
{
lean_object* v_ctx_2717_; lean_object* v_simprocs_2718_; 
v_ctx_2717_ = lean_ctor_get(v_a_2716_, 0);
lean_inc_ref(v_ctx_2717_);
v_simprocs_2718_ = lean_ctor_get(v_a_2716_, 1);
lean_inc_ref(v_simprocs_2718_);
lean_dec(v_a_2716_);
v___y_2639_ = v___y_2707_;
v___y_2640_ = v___y_2712_;
v___y_2641_ = v_simprocs_2718_;
v___y_2642_ = v___y_2713_;
v___y_2643_ = v_stxForSuggestion_2705_;
v___y_2644_ = v___y_2710_;
v___y_2645_ = v___y_2711_;
v___y_2646_ = v_ctx_2717_;
goto v___jp_2638_;
}
else
{
lean_dec_ref_known(v___y_2701_, 1);
if (v___y_2704_ == 0)
{
lean_object* v_ctx_2719_; lean_object* v_simprocs_2720_; 
v_ctx_2719_ = lean_ctor_get(v_a_2716_, 0);
lean_inc_ref(v_ctx_2719_);
v_simprocs_2720_ = lean_ctor_get(v_a_2716_, 1);
lean_inc_ref(v_simprocs_2720_);
lean_dec(v_a_2716_);
v___y_2639_ = v___y_2707_;
v___y_2640_ = v___y_2712_;
v___y_2641_ = v_simprocs_2720_;
v___y_2642_ = v___y_2713_;
v___y_2643_ = v_stxForSuggestion_2705_;
v___y_2644_ = v___y_2710_;
v___y_2645_ = v___y_2711_;
v___y_2646_ = v_ctx_2719_;
goto v___jp_2638_;
}
else
{
lean_object* v_ctx_2721_; lean_object* v_simprocs_2722_; lean_object* v___x_2723_; 
v_ctx_2721_ = lean_ctor_get(v_a_2716_, 0);
lean_inc_ref(v_ctx_2721_);
v_simprocs_2722_ = lean_ctor_get(v_a_2716_, 1);
lean_inc_ref(v_simprocs_2722_);
lean_dec(v_a_2716_);
v___x_2723_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2721_);
v___y_2639_ = v___y_2707_;
v___y_2640_ = v___y_2712_;
v___y_2641_ = v_simprocs_2722_;
v___y_2642_ = v___y_2713_;
v___y_2643_ = v_stxForSuggestion_2705_;
v___y_2644_ = v___y_2710_;
v___y_2645_ = v___y_2711_;
v___y_2646_ = v___x_2723_;
goto v___jp_2638_;
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_stxForSuggestion_2705_);
lean_dec(v___y_2701_);
lean_dec(v_tk_2586_);
v_a_2724_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2715_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2715_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
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
v___jp_2732_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_inc_ref_n(v___y_2742_, 2);
v___x_2754_ = l_Array_append___redArg(v___y_2742_, v___y_2753_);
lean_dec_ref(v___y_2753_);
lean_inc_n(v___y_2733_, 3);
lean_inc_n(v___y_2750_, 5);
v___x_2755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___y_2750_);
lean_ctor_set(v___x_2755_, 1, v___y_2733_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2750_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2759_ = l_Lean_Syntax_SepArray_ofElems(v___x_2758_, v___y_2752_);
lean_dec_ref(v___y_2752_);
v___x_2760_ = l_Array_append___redArg(v___y_2742_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___y_2750_);
lean_ctor_set(v___x_2761_, 1, v___y_2733_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2750_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_Syntax_node3(v___y_2750_, v___y_2733_, v___x_2757_, v___x_2761_, v___x_2763_);
v___x_2765_ = l_Lean_Syntax_node5(v___y_2750_, v___y_2736_, v___y_2739_, v___y_2741_, v___y_2737_, v___x_2755_, v___x_2764_);
v___y_2701_ = v___y_2745_;
v___y_2702_ = v___y_2734_;
v___y_2703_ = v___y_2751_;
v___y_2704_ = v___y_2740_;
v_stxForSuggestion_2705_ = v___x_2765_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2744_;
v___y_2708_ = v___y_2738_;
v___y_2709_ = v___y_2743_;
v___y_2710_ = v___y_2749_;
v___y_2711_ = v___y_2747_;
v___y_2712_ = v___y_2735_;
v___y_2713_ = v___y_2746_;
goto v___jp_2700_;
}
v___jp_2766_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc_ref(v___y_2776_);
v___x_2788_ = l_Array_append___redArg(v___y_2776_, v___y_2787_);
lean_dec_ref(v___y_2787_);
lean_inc(v___y_2767_);
lean_inc(v___y_2784_);
v___x_2789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2789_, 0, v___y_2784_);
lean_ctor_set(v___x_2789_, 1, v___y_2767_);
lean_ctor_set(v___x_2789_, 2, v___x_2788_);
if (lean_obj_tag(v___y_2768_) == 1)
{
lean_object* v_val_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_val_2790_ = lean_ctor_get(v___y_2768_, 0);
lean_inc(v_val_2790_);
lean_dec_ref_known(v___y_2768_, 1);
v___x_2791_ = l_Lean_SourceInfo_fromRef(v_val_2790_, v___x_2570_);
lean_dec(v_val_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Array_mkArray1___redArg(v___x_2793_);
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2769_;
v___y_2735_ = v___y_2770_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___x_2789_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2783_;
v___y_2746_ = v___y_2782_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___y_2780_;
v___y_2749_ = v___y_2779_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___x_2794_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2795_; 
lean_dec(v___y_2768_);
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2769_;
v___y_2735_ = v___y_2770_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___x_2789_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2783_;
v___y_2746_ = v___y_2782_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___y_2780_;
v___y_2749_ = v___y_2779_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___x_2795_;
goto v___jp_2732_;
}
}
v___jp_2796_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_inc_ref_n(v___y_2801_, 2);
v___x_2818_ = l_Array_append___redArg(v___y_2801_, v___y_2817_);
lean_dec_ref(v___y_2817_);
lean_inc_n(v___y_2798_, 3);
lean_inc_n(v___y_2797_, 5);
v___x_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___y_2797_);
lean_ctor_set(v___x_2819_, 1, v___y_2798_);
lean_ctor_set(v___x_2819_, 2, v___x_2818_);
v___x_2820_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___y_2797_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2823_ = l_Lean_Syntax_SepArray_ofElems(v___x_2822_, v___y_2815_);
lean_dec_ref(v___y_2815_);
v___x_2824_ = l_Array_append___redArg(v___y_2801_, v___x_2823_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2825_, 0, v___y_2797_);
lean_ctor_set(v___x_2825_, 1, v___y_2798_);
lean_ctor_set(v___x_2825_, 2, v___x_2824_);
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___y_2797_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_Syntax_node3(v___y_2797_, v___y_2798_, v___x_2821_, v___x_2825_, v___x_2827_);
v___x_2829_ = l_Lean_Syntax_node5(v___y_2797_, v___y_2808_, v___y_2802_, v___y_2805_, v___y_2816_, v___x_2819_, v___x_2828_);
v___y_2701_ = v___y_2809_;
v___y_2702_ = v___y_2799_;
v___y_2703_ = v___y_2814_;
v___y_2704_ = v___y_2804_;
v_stxForSuggestion_2705_ = v___x_2829_;
v___y_2706_ = v___y_2812_;
v___y_2707_ = v___y_2807_;
v___y_2708_ = v___y_2803_;
v___y_2709_ = v___y_2806_;
v___y_2710_ = v___y_2813_;
v___y_2711_ = v___y_2811_;
v___y_2712_ = v___y_2800_;
v___y_2713_ = v___y_2810_;
goto v___jp_2700_;
}
v___jp_2830_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_inc_ref(v___y_2836_);
v___x_2852_ = l_Array_append___redArg(v___y_2836_, v___y_2851_);
lean_dec_ref(v___y_2851_);
lean_inc(v___y_2833_);
lean_inc(v___y_2831_);
v___x_2853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2853_, 0, v___y_2831_);
lean_ctor_set(v___x_2853_, 1, v___y_2833_);
lean_ctor_set(v___x_2853_, 2, v___x_2852_);
if (lean_obj_tag(v___y_2832_) == 1)
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_val_2854_ = lean_ctor_get(v___y_2832_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v___y_2832_, 1);
v___x_2855_ = l_Lean_SourceInfo_fromRef(v_val_2854_, v___x_2570_);
lean_dec(v_val_2854_);
v___x_2856_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Array_mkArray1___redArg(v___x_2857_);
v___y_2797_ = v___y_2831_;
v___y_2798_ = v___y_2833_;
v___y_2799_ = v___y_2834_;
v___y_2800_ = v___y_2835_;
v___y_2801_ = v___y_2836_;
v___y_2802_ = v___y_2837_;
v___y_2803_ = v___y_2838_;
v___y_2804_ = v___y_2839_;
v___y_2805_ = v___y_2840_;
v___y_2806_ = v___y_2841_;
v___y_2807_ = v___y_2842_;
v___y_2808_ = v___y_2843_;
v___y_2809_ = v___y_2848_;
v___y_2810_ = v___y_2847_;
v___y_2811_ = v___y_2846_;
v___y_2812_ = v___y_2845_;
v___y_2813_ = v___y_2844_;
v___y_2814_ = v___y_2849_;
v___y_2815_ = v___y_2850_;
v___y_2816_ = v___x_2853_;
v___y_2817_ = v___x_2858_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v___y_2832_);
v___x_2859_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2797_ = v___y_2831_;
v___y_2798_ = v___y_2833_;
v___y_2799_ = v___y_2834_;
v___y_2800_ = v___y_2835_;
v___y_2801_ = v___y_2836_;
v___y_2802_ = v___y_2837_;
v___y_2803_ = v___y_2838_;
v___y_2804_ = v___y_2839_;
v___y_2805_ = v___y_2840_;
v___y_2806_ = v___y_2841_;
v___y_2807_ = v___y_2842_;
v___y_2808_ = v___y_2843_;
v___y_2809_ = v___y_2848_;
v___y_2810_ = v___y_2847_;
v___y_2811_ = v___y_2846_;
v___y_2812_ = v___y_2845_;
v___y_2813_ = v___y_2844_;
v___y_2814_ = v___y_2849_;
v___y_2815_ = v___y_2850_;
v___y_2816_ = v___x_2853_;
v___y_2817_ = v___x_2859_;
goto v___jp_2796_;
}
}
v___jp_2860_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref_n(v___y_2869_, 2);
v___x_2881_ = l_Array_append___redArg(v___y_2869_, v___y_2880_);
lean_dec_ref(v___y_2880_);
lean_inc_n(v___y_2875_, 2);
lean_inc_n(v___y_2863_, 2);
v___x_2882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2882_, 0, v___y_2863_);
lean_ctor_set(v___x_2882_, 1, v___y_2875_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2883_, 0, v___y_2863_);
lean_ctor_set(v___x_2883_, 1, v___y_2875_);
lean_ctor_set(v___x_2883_, 2, v___y_2869_);
v___x_2884_ = l_Lean_Syntax_node5(v___y_2863_, v___y_2877_, v___y_2876_, v___y_2866_, v___y_2879_, v___x_2882_, v___x_2883_);
v___y_2701_ = v___y_2870_;
v___y_2702_ = v___y_2861_;
v___y_2703_ = v___y_2878_;
v___y_2704_ = v___y_2865_;
v_stxForSuggestion_2705_ = v___x_2884_;
v___y_2706_ = v___y_2872_;
v___y_2707_ = v___y_2868_;
v___y_2708_ = v___y_2864_;
v___y_2709_ = v___y_2867_;
v___y_2710_ = v___y_2873_;
v___y_2711_ = v___y_2874_;
v___y_2712_ = v___y_2862_;
v___y_2713_ = v___y_2871_;
goto v___jp_2700_;
}
v___jp_2885_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_inc_ref(v___y_2895_);
v___x_2906_ = l_Array_append___redArg(v___y_2895_, v___y_2905_);
lean_dec_ref(v___y_2905_);
lean_inc(v___y_2902_);
lean_inc(v___y_2889_);
v___x_2907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2907_, 0, v___y_2889_);
lean_ctor_set(v___x_2907_, 1, v___y_2902_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
if (lean_obj_tag(v___y_2886_) == 1)
{
lean_object* v_val_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_val_2908_ = lean_ctor_get(v___y_2886_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v___y_2886_, 1);
v___x_2909_ = l_Lean_SourceInfo_fromRef(v_val_2908_, v___x_2570_);
lean_dec(v_val_2908_);
v___x_2910_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Array_mkArray1___redArg(v___x_2911_);
v___y_2861_ = v___y_2887_;
v___y_2862_ = v___y_2888_;
v___y_2863_ = v___y_2889_;
v___y_2864_ = v___y_2890_;
v___y_2865_ = v___y_2891_;
v___y_2866_ = v___y_2892_;
v___y_2867_ = v___y_2893_;
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2895_;
v___y_2870_ = v___y_2899_;
v___y_2871_ = v___y_2900_;
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2896_;
v___y_2875_ = v___y_2902_;
v___y_2876_ = v___y_2901_;
v___y_2877_ = v___y_2903_;
v___y_2878_ = v___y_2904_;
v___y_2879_ = v___x_2907_;
v___y_2880_ = v___x_2912_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v___y_2886_);
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2861_ = v___y_2887_;
v___y_2862_ = v___y_2888_;
v___y_2863_ = v___y_2889_;
v___y_2864_ = v___y_2890_;
v___y_2865_ = v___y_2891_;
v___y_2866_ = v___y_2892_;
v___y_2867_ = v___y_2893_;
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2895_;
v___y_2870_ = v___y_2899_;
v___y_2871_ = v___y_2900_;
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2896_;
v___y_2875_ = v___y_2902_;
v___y_2876_ = v___y_2901_;
v___y_2877_ = v___y_2903_;
v___y_2878_ = v___y_2904_;
v___y_2879_ = v___x_2907_;
v___y_2880_ = v___x_2913_;
goto v___jp_2860_;
}
}
v___jp_2914_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_inc_ref_n(v___y_2930_, 2);
v___x_2935_ = l_Array_append___redArg(v___y_2930_, v___y_2934_);
lean_dec_ref(v___y_2934_);
lean_inc_n(v___y_2924_, 2);
lean_inc_n(v___y_2915_, 2);
v___x_2936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2936_, 0, v___y_2915_);
lean_ctor_set(v___x_2936_, 1, v___y_2924_);
lean_ctor_set(v___x_2936_, 2, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2937_, 0, v___y_2915_);
lean_ctor_set(v___x_2937_, 1, v___y_2924_);
lean_ctor_set(v___x_2937_, 2, v___y_2930_);
v___x_2938_ = l_Lean_Syntax_node5(v___y_2915_, v___y_2932_, v___y_2920_, v___y_2921_, v___y_2933_, v___x_2936_, v___x_2937_);
v___y_2701_ = v___y_2925_;
v___y_2702_ = v___y_2916_;
v___y_2703_ = v___y_2931_;
v___y_2704_ = v___y_2919_;
v_stxForSuggestion_2705_ = v___x_2938_;
v___y_2706_ = v___y_2927_;
v___y_2707_ = v___y_2923_;
v___y_2708_ = v___y_2918_;
v___y_2709_ = v___y_2922_;
v___y_2710_ = v___y_2928_;
v___y_2711_ = v___y_2929_;
v___y_2712_ = v___y_2917_;
v___y_2713_ = v___y_2926_;
goto v___jp_2700_;
}
v___jp_2939_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_inc_ref(v___y_2956_);
v___x_2960_ = l_Array_append___redArg(v___y_2956_, v___y_2959_);
lean_dec_ref(v___y_2959_);
lean_inc(v___y_2950_);
lean_inc(v___y_2941_);
v___x_2961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2941_);
lean_ctor_set(v___x_2961_, 1, v___y_2950_);
lean_ctor_set(v___x_2961_, 2, v___x_2960_);
if (lean_obj_tag(v___y_2940_) == 1)
{
lean_object* v_val_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_val_2962_ = lean_ctor_get(v___y_2940_, 0);
lean_inc(v_val_2962_);
lean_dec_ref_known(v___y_2940_, 1);
v___x_2963_ = l_Lean_SourceInfo_fromRef(v_val_2962_, v___x_2570_);
lean_dec(v_val_2962_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Array_mkArray1___redArg(v___x_2965_);
v___y_2915_ = v___y_2941_;
v___y_2916_ = v___y_2942_;
v___y_2917_ = v___y_2943_;
v___y_2918_ = v___y_2944_;
v___y_2919_ = v___y_2945_;
v___y_2920_ = v___y_2946_;
v___y_2921_ = v___y_2947_;
v___y_2922_ = v___y_2948_;
v___y_2923_ = v___y_2949_;
v___y_2924_ = v___y_2950_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2954_;
v___y_2927_ = v___y_2953_;
v___y_2928_ = v___y_2952_;
v___y_2929_ = v___y_2951_;
v___y_2930_ = v___y_2956_;
v___y_2931_ = v___y_2957_;
v___y_2932_ = v___y_2958_;
v___y_2933_ = v___x_2961_;
v___y_2934_ = v___x_2966_;
goto v___jp_2914_;
}
else
{
lean_object* v___x_2967_; 
lean_dec(v___y_2940_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2915_ = v___y_2941_;
v___y_2916_ = v___y_2942_;
v___y_2917_ = v___y_2943_;
v___y_2918_ = v___y_2944_;
v___y_2919_ = v___y_2945_;
v___y_2920_ = v___y_2946_;
v___y_2921_ = v___y_2947_;
v___y_2922_ = v___y_2948_;
v___y_2923_ = v___y_2949_;
v___y_2924_ = v___y_2950_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2954_;
v___y_2927_ = v___y_2953_;
v___y_2928_ = v___y_2952_;
v___y_2929_ = v___y_2951_;
v___y_2930_ = v___y_2956_;
v___y_2931_ = v___y_2957_;
v___y_2932_ = v___y_2958_;
v___y_2933_ = v___x_2961_;
v___y_2934_ = v___x_2967_;
goto v___jp_2914_;
}
}
v___jp_2968_:
{
lean_object* v_ref_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_ref_2986_ = lean_ctor_get(v___y_2970_, 2);
v___x_2987_ = l_Lean_SourceInfo_fromRef(v_ref_2986_, v___y_2985_);
v___x_2988_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2989_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_2988_);
v___x_2990_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_2991_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2994_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2976_) == 1)
{
lean_object* v_val_2995_; lean_object* v___x_2996_; 
v_val_2995_ = lean_ctor_get(v___y_2976_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v___y_2976_, 1);
v___x_2996_ = l_Array_mkArray1___redArg(v_val_2995_);
v___y_2767_ = v___x_2993_;
v___y_2768_ = v___y_2969_;
v___y_2769_ = v___y_2971_;
v___y_2770_ = v___y_2970_;
v___y_2771_ = v___x_2989_;
v___y_2772_ = v___y_2972_;
v___y_2773_ = v___x_2992_;
v___y_2774_ = v___y_2973_;
v___y_2775_ = v___y_2974_;
v___y_2776_ = v___x_2994_;
v___y_2777_ = v___y_2975_;
v___y_2778_ = v___y_2977_;
v___y_2779_ = v___y_2979_;
v___y_2780_ = v___y_2980_;
v___y_2781_ = v___y_2981_;
v___y_2782_ = v___y_2982_;
v___y_2783_ = v___y_2978_;
v___y_2784_ = v___x_2987_;
v___y_2785_ = v___y_2983_;
v___y_2786_ = v___y_2984_;
v___y_2787_ = v___x_2996_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2997_; 
lean_dec(v___y_2976_);
v___x_2997_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2767_ = v___x_2993_;
v___y_2768_ = v___y_2969_;
v___y_2769_ = v___y_2971_;
v___y_2770_ = v___y_2970_;
v___y_2771_ = v___x_2989_;
v___y_2772_ = v___y_2972_;
v___y_2773_ = v___x_2992_;
v___y_2774_ = v___y_2973_;
v___y_2775_ = v___y_2974_;
v___y_2776_ = v___x_2994_;
v___y_2777_ = v___y_2975_;
v___y_2778_ = v___y_2977_;
v___y_2779_ = v___y_2979_;
v___y_2780_ = v___y_2980_;
v___y_2781_ = v___y_2981_;
v___y_2782_ = v___y_2982_;
v___y_2783_ = v___y_2978_;
v___y_2784_ = v___x_2987_;
v___y_2785_ = v___y_2983_;
v___y_2786_ = v___y_2984_;
v___y_2787_ = v___x_2997_;
goto v___jp_2766_;
}
}
v___jp_2998_:
{
lean_object* v___x_3015_; lean_object* v_a_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3015_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2999_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref(v___x_3015_);
v___x_3017_ = lean_array_get_size(v___y_3004_);
v___x_3018_ = lean_nat_dec_eq(v___x_3017_, v___x_2585_);
if (v___x_3018_ == 0)
{
if (lean_obj_tag(v___y_3001_) == 0)
{
v___y_2969_ = v___y_3000_;
v___y_2970_ = v___y_3013_;
v___y_2971_ = v___y_3002_;
v___y_2972_ = v___y_3009_;
v___y_2973_ = v___y_3003_;
v___y_2974_ = v_a_3016_;
v___y_2975_ = v___y_3010_;
v___y_2976_ = v___y_3005_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3001_;
v___y_2979_ = v___y_3011_;
v___y_2980_ = v___y_3007_;
v___y_2981_ = v___y_3012_;
v___y_2982_ = v___y_3014_;
v___y_2983_ = v_stxForExecution_3006_;
v___y_2984_ = v___y_3004_;
v___y_2985_ = v___x_3018_;
goto v___jp_2968_;
}
else
{
if (v___y_3003_ == 0)
{
v___y_2969_ = v___y_3000_;
v___y_2970_ = v___y_3013_;
v___y_2971_ = v___y_3002_;
v___y_2972_ = v___y_3009_;
v___y_2973_ = v___y_3003_;
v___y_2974_ = v_a_3016_;
v___y_2975_ = v___y_3010_;
v___y_2976_ = v___y_3005_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3001_;
v___y_2979_ = v___y_3011_;
v___y_2980_ = v___y_3007_;
v___y_2981_ = v___y_3012_;
v___y_2982_ = v___y_3014_;
v___y_2983_ = v_stxForExecution_3006_;
v___y_2984_ = v___y_3004_;
v___y_2985_ = v___y_3003_;
goto v___jp_2968_;
}
else
{
lean_object* v_ref_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_ref_3019_ = lean_ctor_get(v___y_3013_, 2);
v___x_3020_ = l_Lean_SourceInfo_fromRef(v_ref_3019_, v___x_3018_);
v___x_3021_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3022_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3021_);
v___x_3023_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3024_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3027_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3005_) == 1)
{
lean_object* v_val_3028_; lean_object* v___x_3029_; 
v_val_3028_ = lean_ctor_get(v___y_3005_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v___y_3005_, 1);
v___x_3029_ = l_Array_mkArray1___redArg(v_val_3028_);
v___y_2831_ = v___x_3020_;
v___y_2832_ = v___y_3000_;
v___y_2833_ = v___x_3026_;
v___y_2834_ = v___y_3002_;
v___y_2835_ = v___y_3013_;
v___y_2836_ = v___x_3027_;
v___y_2837_ = v___x_3025_;
v___y_2838_ = v___y_3009_;
v___y_2839_ = v___y_3003_;
v___y_2840_ = v_a_3016_;
v___y_2841_ = v___y_3010_;
v___y_2842_ = v___y_3008_;
v___y_2843_ = v___x_3022_;
v___y_2844_ = v___y_3011_;
v___y_2845_ = v___y_3007_;
v___y_2846_ = v___y_3012_;
v___y_2847_ = v___y_3014_;
v___y_2848_ = v___y_3001_;
v___y_2849_ = v_stxForExecution_3006_;
v___y_2850_ = v___y_3004_;
v___y_2851_ = v___x_3029_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_3030_; 
lean_dec(v___y_3005_);
v___x_3030_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2831_ = v___x_3020_;
v___y_2832_ = v___y_3000_;
v___y_2833_ = v___x_3026_;
v___y_2834_ = v___y_3002_;
v___y_2835_ = v___y_3013_;
v___y_2836_ = v___x_3027_;
v___y_2837_ = v___x_3025_;
v___y_2838_ = v___y_3009_;
v___y_2839_ = v___y_3003_;
v___y_2840_ = v_a_3016_;
v___y_2841_ = v___y_3010_;
v___y_2842_ = v___y_3008_;
v___y_2843_ = v___x_3022_;
v___y_2844_ = v___y_3011_;
v___y_2845_ = v___y_3007_;
v___y_2846_ = v___y_3012_;
v___y_2847_ = v___y_3014_;
v___y_2848_ = v___y_3001_;
v___y_2849_ = v_stxForExecution_3006_;
v___y_2850_ = v___y_3004_;
v___y_2851_ = v___x_3030_;
goto v___jp_2830_;
}
}
}
}
else
{
lean_dec_ref(v___y_3004_);
if (lean_obj_tag(v___y_3001_) == 0)
{
lean_object* v_ref_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_ref_3031_ = lean_ctor_get(v___y_3013_, 2);
v___x_3032_ = 0;
v___x_3033_ = l_Lean_SourceInfo_fromRef(v_ref_3031_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_3035_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3034_);
v___x_3036_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3037_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3040_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3005_) == 1)
{
lean_object* v_val_3041_; lean_object* v___x_3042_; 
v_val_3041_ = lean_ctor_get(v___y_3005_, 0);
lean_inc(v_val_3041_);
lean_dec_ref_known(v___y_3005_, 1);
v___x_3042_ = l_Array_mkArray1___redArg(v_val_3041_);
v___y_2886_ = v___y_3000_;
v___y_2887_ = v___y_3002_;
v___y_2888_ = v___y_3013_;
v___y_2889_ = v___x_3033_;
v___y_2890_ = v___y_3009_;
v___y_2891_ = v___y_3003_;
v___y_2892_ = v_a_3016_;
v___y_2893_ = v___y_3010_;
v___y_2894_ = v___y_3008_;
v___y_2895_ = v___x_3040_;
v___y_2896_ = v___y_3012_;
v___y_2897_ = v___y_3011_;
v___y_2898_ = v___y_3007_;
v___y_2899_ = v___y_3001_;
v___y_2900_ = v___y_3014_;
v___y_2901_ = v___x_3038_;
v___y_2902_ = v___x_3039_;
v___y_2903_ = v___x_3035_;
v___y_2904_ = v_stxForExecution_3006_;
v___y_2905_ = v___x_3042_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_3043_; 
lean_dec(v___y_3005_);
v___x_3043_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2886_ = v___y_3000_;
v___y_2887_ = v___y_3002_;
v___y_2888_ = v___y_3013_;
v___y_2889_ = v___x_3033_;
v___y_2890_ = v___y_3009_;
v___y_2891_ = v___y_3003_;
v___y_2892_ = v_a_3016_;
v___y_2893_ = v___y_3010_;
v___y_2894_ = v___y_3008_;
v___y_2895_ = v___x_3040_;
v___y_2896_ = v___y_3012_;
v___y_2897_ = v___y_3011_;
v___y_2898_ = v___y_3007_;
v___y_2899_ = v___y_3001_;
v___y_2900_ = v___y_3014_;
v___y_2901_ = v___x_3038_;
v___y_2902_ = v___x_3039_;
v___y_2903_ = v___x_3035_;
v___y_2904_ = v_stxForExecution_3006_;
v___y_2905_ = v___x_3043_;
goto v___jp_2885_;
}
}
else
{
lean_object* v_ref_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_ref_3044_ = lean_ctor_get(v___y_3013_, 2);
v___x_3045_ = 0;
v___x_3046_ = l_Lean_SourceInfo_fromRef(v_ref_3044_, v___x_3045_);
v___x_3047_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3048_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3047_);
v___x_3049_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3053_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3005_) == 1)
{
lean_object* v_val_3054_; lean_object* v___x_3055_; 
v_val_3054_ = lean_ctor_get(v___y_3005_, 0);
lean_inc(v_val_3054_);
lean_dec_ref_known(v___y_3005_, 1);
v___x_3055_ = l_Array_mkArray1___redArg(v_val_3054_);
v___y_2940_ = v___y_3000_;
v___y_2941_ = v___x_3046_;
v___y_2942_ = v___y_3002_;
v___y_2943_ = v___y_3013_;
v___y_2944_ = v___y_3009_;
v___y_2945_ = v___y_3003_;
v___y_2946_ = v___x_3051_;
v___y_2947_ = v_a_3016_;
v___y_2948_ = v___y_3010_;
v___y_2949_ = v___y_3008_;
v___y_2950_ = v___x_3052_;
v___y_2951_ = v___y_3012_;
v___y_2952_ = v___y_3011_;
v___y_2953_ = v___y_3007_;
v___y_2954_ = v___y_3014_;
v___y_2955_ = v___y_3001_;
v___y_2956_ = v___x_3053_;
v___y_2957_ = v_stxForExecution_3006_;
v___y_2958_ = v___x_3048_;
v___y_2959_ = v___x_3055_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_3056_; 
lean_dec(v___y_3005_);
v___x_3056_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2940_ = v___y_3000_;
v___y_2941_ = v___x_3046_;
v___y_2942_ = v___y_3002_;
v___y_2943_ = v___y_3013_;
v___y_2944_ = v___y_3009_;
v___y_2945_ = v___y_3003_;
v___y_2946_ = v___x_3051_;
v___y_2947_ = v_a_3016_;
v___y_2948_ = v___y_3010_;
v___y_2949_ = v___y_3008_;
v___y_2950_ = v___x_3052_;
v___y_2951_ = v___y_3012_;
v___y_2952_ = v___y_3011_;
v___y_2953_ = v___y_3007_;
v___y_2954_ = v___y_3014_;
v___y_2955_ = v___y_3001_;
v___y_2956_ = v___x_3053_;
v___y_2957_ = v_stxForExecution_3006_;
v___y_2958_ = v___x_3048_;
v___y_2959_ = v___x_3056_;
goto v___jp_2939_;
}
}
}
}
v___jp_3057_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_inc_ref_n(v___y_3065_, 2);
v___x_3080_ = l_Array_append___redArg(v___y_3065_, v___y_3079_);
lean_dec_ref(v___y_3079_);
lean_inc_n(v___y_3077_, 3);
lean_inc_n(v___y_3066_, 5);
v___x_3081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3066_);
lean_ctor_set(v___x_3081_, 1, v___y_3077_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
v___x_3082_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3066_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3085_ = l_Lean_Syntax_SepArray_ofElems(v___x_3084_, v___y_3078_);
v___x_3086_ = l_Array_append___redArg(v___y_3065_, v___x_3085_);
lean_dec_ref(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3087_, 0, v___y_3066_);
lean_ctor_set(v___x_3087_, 1, v___y_3077_);
lean_ctor_set(v___x_3087_, 2, v___x_3086_);
v___x_3088_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___y_3066_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Lean_Syntax_node3(v___y_3066_, v___y_3077_, v___x_3083_, v___x_3087_, v___x_3089_);
lean_inc(v___y_3058_);
v___x_3091_ = l_Lean_Syntax_node5(v___y_3066_, v___y_3076_, v___y_3068_, v___y_3058_, v___y_3075_, v___x_3081_, v___x_3090_);
v___y_2999_ = v___y_3058_;
v___y_3000_ = v___y_3060_;
v___y_3001_ = v___y_3071_;
v___y_3002_ = v___y_3062_;
v___y_3003_ = v___y_3067_;
v___y_3004_ = v___y_3078_;
v___y_3005_ = v___y_3069_;
v_stxForExecution_3006_ = v___x_3091_;
v___y_3007_ = v___y_3073_;
v___y_3008_ = v___y_3061_;
v___y_3009_ = v___y_3059_;
v___y_3010_ = v___y_3070_;
v___y_3011_ = v___y_3072_;
v___y_3012_ = v___y_3063_;
v___y_3013_ = v___y_3074_;
v___y_3014_ = v___y_3064_;
goto v___jp_2998_;
}
v___jp_3092_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_inc_ref(v___y_3099_);
v___x_3114_ = l_Array_append___redArg(v___y_3099_, v___y_3113_);
lean_dec_ref(v___y_3113_);
lean_inc(v___y_3111_);
lean_inc(v___y_3100_);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___y_3100_);
lean_ctor_set(v___x_3115_, 1, v___y_3111_);
lean_ctor_set(v___x_3115_, 2, v___x_3114_);
if (lean_obj_tag(v___y_3095_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_val_3116_ = lean_ctor_get(v___y_3095_, 0);
v___x_3117_ = l_Lean_SourceInfo_fromRef(v_val_3116_, v___x_2570_);
v___x_3118_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Array_mkArray1___redArg(v___x_3119_);
v___y_3058_ = v___y_3093_;
v___y_3059_ = v___y_3094_;
v___y_3060_ = v___y_3095_;
v___y_3061_ = v___y_3096_;
v___y_3062_ = v___y_3097_;
v___y_3063_ = v___y_3098_;
v___y_3064_ = v___y_3101_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3102_;
v___y_3068_ = v___y_3103_;
v___y_3069_ = v___y_3105_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3107_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3108_;
v___y_3074_ = v___y_3109_;
v___y_3075_ = v___x_3115_;
v___y_3076_ = v___y_3110_;
v___y_3077_ = v___y_3111_;
v___y_3078_ = v___y_3112_;
v___y_3079_ = v___x_3120_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3058_ = v___y_3093_;
v___y_3059_ = v___y_3094_;
v___y_3060_ = v___y_3095_;
v___y_3061_ = v___y_3096_;
v___y_3062_ = v___y_3097_;
v___y_3063_ = v___y_3098_;
v___y_3064_ = v___y_3101_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3102_;
v___y_3068_ = v___y_3103_;
v___y_3069_ = v___y_3105_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3107_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3108_;
v___y_3074_ = v___y_3109_;
v___y_3075_ = v___x_3115_;
v___y_3076_ = v___y_3110_;
v___y_3077_ = v___y_3111_;
v___y_3078_ = v___y_3112_;
v___y_3079_ = v___x_3121_;
goto v___jp_3057_;
}
}
v___jp_3122_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_inc_ref_n(v___y_3138_, 2);
v___x_3145_ = l_Array_append___redArg(v___y_3138_, v___y_3144_);
lean_dec_ref(v___y_3144_);
lean_inc_n(v___y_3132_, 3);
lean_inc_n(v___y_3131_, 5);
v___x_3146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3146_, 0, v___y_3131_);
lean_ctor_set(v___x_3146_, 1, v___y_3132_);
lean_ctor_set(v___x_3146_, 2, v___x_3145_);
v___x_3147_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___y_3131_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3150_ = l_Lean_Syntax_SepArray_ofElems(v___x_3149_, v___y_3142_);
v___x_3151_ = l_Array_append___redArg(v___y_3138_, v___x_3150_);
lean_dec_ref(v___x_3150_);
v___x_3152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3152_, 0, v___y_3131_);
lean_ctor_set(v___x_3152_, 1, v___y_3132_);
lean_ctor_set(v___x_3152_, 2, v___x_3151_);
v___x_3153_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___y_3131_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = l_Lean_Syntax_node3(v___y_3131_, v___y_3132_, v___x_3148_, v___x_3152_, v___x_3154_);
lean_inc(v___y_3123_);
v___x_3156_ = l_Lean_Syntax_node5(v___y_3131_, v___y_3143_, v___y_3141_, v___y_3123_, v___y_3133_, v___x_3146_, v___x_3155_);
v___y_2999_ = v___y_3123_;
v___y_3000_ = v___y_3125_;
v___y_3001_ = v___y_3136_;
v___y_3002_ = v___y_3127_;
v___y_3003_ = v___y_3130_;
v___y_3004_ = v___y_3142_;
v___y_3005_ = v___y_3134_;
v_stxForExecution_3006_ = v___x_3156_;
v___y_3007_ = v___y_3139_;
v___y_3008_ = v___y_3126_;
v___y_3009_ = v___y_3124_;
v___y_3010_ = v___y_3135_;
v___y_3011_ = v___y_3137_;
v___y_3012_ = v___y_3128_;
v___y_3013_ = v___y_3140_;
v___y_3014_ = v___y_3129_;
goto v___jp_2998_;
}
v___jp_3157_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_inc_ref(v___y_3173_);
v___x_3179_ = l_Array_append___redArg(v___y_3173_, v___y_3178_);
lean_dec_ref(v___y_3178_);
lean_inc(v___y_3167_);
lean_inc(v___y_3166_);
v___x_3180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3180_, 0, v___y_3166_);
lean_ctor_set(v___x_3180_, 1, v___y_3167_);
lean_ctor_set(v___x_3180_, 2, v___x_3179_);
if (lean_obj_tag(v___y_3160_) == 1)
{
lean_object* v_val_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_val_3181_ = lean_ctor_get(v___y_3160_, 0);
v___x_3182_ = l_Lean_SourceInfo_fromRef(v_val_3181_, v___x_2570_);
v___x_3183_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = l_Array_mkArray1___redArg(v___x_3184_);
v___y_3123_ = v___y_3158_;
v___y_3124_ = v___y_3159_;
v___y_3125_ = v___y_3160_;
v___y_3126_ = v___y_3161_;
v___y_3127_ = v___y_3162_;
v___y_3128_ = v___y_3163_;
v___y_3129_ = v___y_3164_;
v___y_3130_ = v___y_3165_;
v___y_3131_ = v___y_3166_;
v___y_3132_ = v___y_3167_;
v___y_3133_ = v___x_3180_;
v___y_3134_ = v___y_3168_;
v___y_3135_ = v___y_3169_;
v___y_3136_ = v___y_3171_;
v___y_3137_ = v___y_3170_;
v___y_3138_ = v___y_3173_;
v___y_3139_ = v___y_3172_;
v___y_3140_ = v___y_3174_;
v___y_3141_ = v___y_3175_;
v___y_3142_ = v___y_3176_;
v___y_3143_ = v___y_3177_;
v___y_3144_ = v___x_3185_;
goto v___jp_3122_;
}
else
{
lean_object* v___x_3186_; 
v___x_3186_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3123_ = v___y_3158_;
v___y_3124_ = v___y_3159_;
v___y_3125_ = v___y_3160_;
v___y_3126_ = v___y_3161_;
v___y_3127_ = v___y_3162_;
v___y_3128_ = v___y_3163_;
v___y_3129_ = v___y_3164_;
v___y_3130_ = v___y_3165_;
v___y_3131_ = v___y_3166_;
v___y_3132_ = v___y_3167_;
v___y_3133_ = v___x_3180_;
v___y_3134_ = v___y_3168_;
v___y_3135_ = v___y_3169_;
v___y_3136_ = v___y_3171_;
v___y_3137_ = v___y_3170_;
v___y_3138_ = v___y_3173_;
v___y_3139_ = v___y_3172_;
v___y_3140_ = v___y_3174_;
v___y_3141_ = v___y_3175_;
v___y_3142_ = v___y_3176_;
v___y_3143_ = v___y_3177_;
v___y_3144_ = v___x_3186_;
goto v___jp_3122_;
}
}
v___jp_3187_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_inc_ref_n(v___y_3202_, 2);
v___x_3210_ = l_Array_append___redArg(v___y_3202_, v___y_3209_);
lean_dec_ref(v___y_3209_);
lean_inc_n(v___y_3191_, 2);
lean_inc_n(v___y_3205_, 2);
v___x_3211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3211_, 0, v___y_3205_);
lean_ctor_set(v___x_3211_, 1, v___y_3191_);
lean_ctor_set(v___x_3211_, 2, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3212_, 0, v___y_3205_);
lean_ctor_set(v___x_3212_, 1, v___y_3191_);
lean_ctor_set(v___x_3212_, 2, v___y_3202_);
lean_inc(v___y_3189_);
v___x_3213_ = l_Lean_Syntax_node5(v___y_3205_, v___y_3188_, v___y_3208_, v___y_3189_, v___y_3206_, v___x_3211_, v___x_3212_);
v___y_2999_ = v___y_3189_;
v___y_3000_ = v___y_3192_;
v___y_3001_ = v___y_3200_;
v___y_3002_ = v___y_3194_;
v___y_3003_ = v___y_3197_;
v___y_3004_ = v___y_3207_;
v___y_3005_ = v___y_3198_;
v_stxForExecution_3006_ = v___x_3213_;
v___y_3007_ = v___y_3203_;
v___y_3008_ = v___y_3193_;
v___y_3009_ = v___y_3190_;
v___y_3010_ = v___y_3199_;
v___y_3011_ = v___y_3201_;
v___y_3012_ = v___y_3195_;
v___y_3013_ = v___y_3204_;
v___y_3014_ = v___y_3196_;
goto v___jp_2998_;
}
v___jp_3214_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_inc_ref(v___y_3229_);
v___x_3236_ = l_Array_append___redArg(v___y_3229_, v___y_3235_);
lean_dec_ref(v___y_3235_);
lean_inc(v___y_3218_);
lean_inc(v___y_3232_);
v___x_3237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3237_, 0, v___y_3232_);
lean_ctor_set(v___x_3237_, 1, v___y_3218_);
lean_ctor_set(v___x_3237_, 2, v___x_3236_);
if (lean_obj_tag(v___y_3219_) == 1)
{
lean_object* v_val_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_val_3238_ = lean_ctor_get(v___y_3219_, 0);
v___x_3239_ = l_Lean_SourceInfo_fromRef(v_val_3238_, v___x_2570_);
v___x_3240_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = l_Array_mkArray1___redArg(v___x_3241_);
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___y_3216_;
v___y_3190_ = v___y_3217_;
v___y_3191_ = v___y_3218_;
v___y_3192_ = v___y_3219_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___y_3223_;
v___y_3197_ = v___y_3224_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3227_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___x_3237_;
v___y_3207_ = v___y_3233_;
v___y_3208_ = v___y_3234_;
v___y_3209_ = v___x_3242_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3243_; 
v___x_3243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___y_3216_;
v___y_3190_ = v___y_3217_;
v___y_3191_ = v___y_3218_;
v___y_3192_ = v___y_3219_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___y_3223_;
v___y_3197_ = v___y_3224_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3227_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___x_3237_;
v___y_3207_ = v___y_3233_;
v___y_3208_ = v___y_3234_;
v___y_3209_ = v___x_3243_;
goto v___jp_3187_;
}
}
v___jp_3244_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_inc_ref_n(v___y_3253_, 2);
v___x_3267_ = l_Array_append___redArg(v___y_3253_, v___y_3266_);
lean_dec_ref(v___y_3266_);
lean_inc_n(v___y_3265_, 2);
lean_inc_n(v___y_3258_, 2);
v___x_3268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3268_, 0, v___y_3258_);
lean_ctor_set(v___x_3268_, 1, v___y_3265_);
lean_ctor_set(v___x_3268_, 2, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3269_, 0, v___y_3258_);
lean_ctor_set(v___x_3269_, 1, v___y_3265_);
lean_ctor_set(v___x_3269_, 2, v___y_3253_);
lean_inc(v___y_3245_);
v___x_3270_ = l_Lean_Syntax_node5(v___y_3258_, v___y_3261_, v___y_3255_, v___y_3245_, v___y_3263_, v___x_3268_, v___x_3269_);
v___y_2999_ = v___y_3245_;
v___y_3000_ = v___y_3247_;
v___y_3001_ = v___y_3257_;
v___y_3002_ = v___y_3249_;
v___y_3003_ = v___y_3252_;
v___y_3004_ = v___y_3264_;
v___y_3005_ = v___y_3254_;
v_stxForExecution_3006_ = v___x_3270_;
v___y_3007_ = v___y_3260_;
v___y_3008_ = v___y_3248_;
v___y_3009_ = v___y_3246_;
v___y_3010_ = v___y_3256_;
v___y_3011_ = v___y_3259_;
v___y_3012_ = v___y_3250_;
v___y_3013_ = v___y_3262_;
v___y_3014_ = v___y_3251_;
goto v___jp_2998_;
}
v___jp_3271_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_inc_ref(v___y_3280_);
v___x_3293_ = l_Array_append___redArg(v___y_3280_, v___y_3292_);
lean_dec_ref(v___y_3292_);
lean_inc(v___y_3291_);
lean_inc(v___y_3286_);
v___x_3294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3286_);
lean_ctor_set(v___x_3294_, 1, v___y_3291_);
lean_ctor_set(v___x_3294_, 2, v___x_3293_);
if (lean_obj_tag(v___y_3274_) == 1)
{
lean_object* v_val_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_val_3295_ = lean_ctor_get(v___y_3274_, 0);
v___x_3296_ = l_Lean_SourceInfo_fromRef(v_val_3295_, v___x_2570_);
v___x_3297_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = l_Array_mkArray1___redArg(v___x_3298_);
v___y_3245_ = v___y_3272_;
v___y_3246_ = v___y_3273_;
v___y_3247_ = v___y_3274_;
v___y_3248_ = v___y_3275_;
v___y_3249_ = v___y_3276_;
v___y_3250_ = v___y_3277_;
v___y_3251_ = v___y_3278_;
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3283_;
v___y_3256_ = v___y_3281_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3286_;
v___y_3259_ = v___y_3284_;
v___y_3260_ = v___y_3287_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3289_;
v___y_3263_ = v___x_3294_;
v___y_3264_ = v___y_3290_;
v___y_3265_ = v___y_3291_;
v___y_3266_ = v___x_3299_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3245_ = v___y_3272_;
v___y_3246_ = v___y_3273_;
v___y_3247_ = v___y_3274_;
v___y_3248_ = v___y_3275_;
v___y_3249_ = v___y_3276_;
v___y_3250_ = v___y_3277_;
v___y_3251_ = v___y_3278_;
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3283_;
v___y_3256_ = v___y_3281_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3286_;
v___y_3259_ = v___y_3284_;
v___y_3260_ = v___y_3287_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3289_;
v___y_3263_ = v___x_3294_;
v___y_3264_ = v___y_3290_;
v___y_3265_ = v___y_3291_;
v___y_3266_ = v___x_3300_;
goto v___jp_3244_;
}
}
v___jp_3301_:
{
lean_object* v_ref_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_ref_3318_ = lean_ctor_get(v___y_3315_, 2);
v___x_3319_ = l_Lean_SourceInfo_fromRef(v_ref_3318_, v___y_3317_);
v___x_3320_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3321_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3320_);
v___x_3322_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3326_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3311_) == 1)
{
lean_object* v_val_3327_; lean_object* v___x_3328_; 
v_val_3327_ = lean_ctor_get(v___y_3311_, 0);
lean_inc(v_val_3327_);
v___x_3328_ = l_Array_mkArray1___redArg(v_val_3327_);
v___y_3093_ = v___y_3302_;
v___y_3094_ = v___y_3303_;
v___y_3095_ = v___y_3304_;
v___y_3096_ = v___y_3305_;
v___y_3097_ = v___y_3306_;
v___y_3098_ = v___y_3307_;
v___y_3099_ = v___x_3326_;
v___y_3100_ = v___x_3319_;
v___y_3101_ = v___y_3308_;
v___y_3102_ = v___y_3309_;
v___y_3103_ = v___x_3324_;
v___y_3104_ = v___y_3310_;
v___y_3105_ = v___y_3311_;
v___y_3106_ = v___y_3312_;
v___y_3107_ = v___y_3313_;
v___y_3108_ = v___y_3314_;
v___y_3109_ = v___y_3315_;
v___y_3110_ = v___x_3321_;
v___y_3111_ = v___x_3325_;
v___y_3112_ = v___y_3316_;
v___y_3113_ = v___x_3328_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3329_; 
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3093_ = v___y_3302_;
v___y_3094_ = v___y_3303_;
v___y_3095_ = v___y_3304_;
v___y_3096_ = v___y_3305_;
v___y_3097_ = v___y_3306_;
v___y_3098_ = v___y_3307_;
v___y_3099_ = v___x_3326_;
v___y_3100_ = v___x_3319_;
v___y_3101_ = v___y_3308_;
v___y_3102_ = v___y_3309_;
v___y_3103_ = v___x_3324_;
v___y_3104_ = v___y_3310_;
v___y_3105_ = v___y_3311_;
v___y_3106_ = v___y_3312_;
v___y_3107_ = v___y_3313_;
v___y_3108_ = v___y_3314_;
v___y_3109_ = v___y_3315_;
v___y_3110_ = v___x_3321_;
v___y_3111_ = v___x_3325_;
v___y_3112_ = v___y_3316_;
v___y_3113_ = v___x_3329_;
goto v___jp_3092_;
}
}
v___jp_3330_:
{
lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3346_ = lean_array_get_size(v_argsArray_3337_);
v___x_3347_ = lean_nat_dec_eq(v___x_3346_, v___x_2585_);
if (v___x_3347_ == 0)
{
if (lean_obj_tag(v___y_3332_) == 0)
{
v___y_3302_ = v___y_3331_;
v___y_3303_ = v___y_3340_;
v___y_3304_ = v___y_3333_;
v___y_3305_ = v___y_3339_;
v___y_3306_ = v___y_3334_;
v___y_3307_ = v___y_3343_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3341_;
v___y_3311_ = v___y_3336_;
v___y_3312_ = v___y_3342_;
v___y_3313_ = v___y_3332_;
v___y_3314_ = v___y_3338_;
v___y_3315_ = v___y_3344_;
v___y_3316_ = v_argsArray_3337_;
v___y_3317_ = v___x_3347_;
goto v___jp_3301_;
}
else
{
if (v___y_3335_ == 0)
{
v___y_3302_ = v___y_3331_;
v___y_3303_ = v___y_3340_;
v___y_3304_ = v___y_3333_;
v___y_3305_ = v___y_3339_;
v___y_3306_ = v___y_3334_;
v___y_3307_ = v___y_3343_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3341_;
v___y_3311_ = v___y_3336_;
v___y_3312_ = v___y_3342_;
v___y_3313_ = v___y_3332_;
v___y_3314_ = v___y_3338_;
v___y_3315_ = v___y_3344_;
v___y_3316_ = v_argsArray_3337_;
v___y_3317_ = v___y_3335_;
goto v___jp_3301_;
}
else
{
lean_object* v_ref_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_ref_3348_ = lean_ctor_get(v___y_3344_, 2);
v___x_3349_ = l_Lean_SourceInfo_fromRef(v_ref_3348_, v___x_3347_);
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3351_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3350_);
v___x_3352_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3353_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3356_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3336_) == 1)
{
lean_object* v_val_3357_; lean_object* v___x_3358_; 
v_val_3357_ = lean_ctor_get(v___y_3336_, 0);
lean_inc(v_val_3357_);
v___x_3358_ = l_Array_mkArray1___redArg(v_val_3357_);
v___y_3158_ = v___y_3331_;
v___y_3159_ = v___y_3340_;
v___y_3160_ = v___y_3333_;
v___y_3161_ = v___y_3339_;
v___y_3162_ = v___y_3334_;
v___y_3163_ = v___y_3343_;
v___y_3164_ = v___y_3345_;
v___y_3165_ = v___y_3335_;
v___y_3166_ = v___x_3349_;
v___y_3167_ = v___x_3355_;
v___y_3168_ = v___y_3336_;
v___y_3169_ = v___y_3341_;
v___y_3170_ = v___y_3342_;
v___y_3171_ = v___y_3332_;
v___y_3172_ = v___y_3338_;
v___y_3173_ = v___x_3356_;
v___y_3174_ = v___y_3344_;
v___y_3175_ = v___x_3354_;
v___y_3176_ = v_argsArray_3337_;
v___y_3177_ = v___x_3351_;
v___y_3178_ = v___x_3358_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3359_; 
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3158_ = v___y_3331_;
v___y_3159_ = v___y_3340_;
v___y_3160_ = v___y_3333_;
v___y_3161_ = v___y_3339_;
v___y_3162_ = v___y_3334_;
v___y_3163_ = v___y_3343_;
v___y_3164_ = v___y_3345_;
v___y_3165_ = v___y_3335_;
v___y_3166_ = v___x_3349_;
v___y_3167_ = v___x_3355_;
v___y_3168_ = v___y_3336_;
v___y_3169_ = v___y_3341_;
v___y_3170_ = v___y_3342_;
v___y_3171_ = v___y_3332_;
v___y_3172_ = v___y_3338_;
v___y_3173_ = v___x_3356_;
v___y_3174_ = v___y_3344_;
v___y_3175_ = v___x_3354_;
v___y_3176_ = v_argsArray_3337_;
v___y_3177_ = v___x_3351_;
v___y_3178_ = v___x_3359_;
goto v___jp_3157_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3332_) == 0)
{
lean_object* v_ref_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_ref_3360_ = lean_ctor_get(v___y_3344_, 2);
v___x_3361_ = 0;
v___x_3362_ = l_Lean_SourceInfo_fromRef(v_ref_3360_, v___x_3361_);
v___x_3363_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3364_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3363_);
v___x_3365_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3366_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3369_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3336_) == 1)
{
lean_object* v_val_3370_; lean_object* v___x_3371_; 
v_val_3370_ = lean_ctor_get(v___y_3336_, 0);
lean_inc(v_val_3370_);
v___x_3371_ = l_Array_mkArray1___redArg(v_val_3370_);
v___y_3215_ = v___x_3364_;
v___y_3216_ = v___y_3331_;
v___y_3217_ = v___y_3340_;
v___y_3218_ = v___x_3368_;
v___y_3219_ = v___y_3333_;
v___y_3220_ = v___y_3339_;
v___y_3221_ = v___y_3334_;
v___y_3222_ = v___y_3343_;
v___y_3223_ = v___y_3345_;
v___y_3224_ = v___y_3335_;
v___y_3225_ = v___y_3341_;
v___y_3226_ = v___y_3336_;
v___y_3227_ = v___y_3342_;
v___y_3228_ = v___y_3332_;
v___y_3229_ = v___x_3369_;
v___y_3230_ = v___y_3338_;
v___y_3231_ = v___y_3344_;
v___y_3232_ = v___x_3362_;
v___y_3233_ = v_argsArray_3337_;
v___y_3234_ = v___x_3367_;
v___y_3235_ = v___x_3371_;
goto v___jp_3214_;
}
else
{
lean_object* v___x_3372_; 
v___x_3372_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3215_ = v___x_3364_;
v___y_3216_ = v___y_3331_;
v___y_3217_ = v___y_3340_;
v___y_3218_ = v___x_3368_;
v___y_3219_ = v___y_3333_;
v___y_3220_ = v___y_3339_;
v___y_3221_ = v___y_3334_;
v___y_3222_ = v___y_3343_;
v___y_3223_ = v___y_3345_;
v___y_3224_ = v___y_3335_;
v___y_3225_ = v___y_3341_;
v___y_3226_ = v___y_3336_;
v___y_3227_ = v___y_3342_;
v___y_3228_ = v___y_3332_;
v___y_3229_ = v___x_3369_;
v___y_3230_ = v___y_3338_;
v___y_3231_ = v___y_3344_;
v___y_3232_ = v___x_3362_;
v___y_3233_ = v_argsArray_3337_;
v___y_3234_ = v___x_3367_;
v___y_3235_ = v___x_3372_;
goto v___jp_3214_;
}
}
else
{
lean_object* v_ref_3373_; uint8_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_ref_3373_ = lean_ctor_get(v___y_3344_, 2);
v___x_3374_ = 0;
v___x_3375_ = l_Lean_SourceInfo_fromRef(v_ref_3373_, v___x_3374_);
v___x_3376_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3377_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3376_);
v___x_3378_ = l_Lean_SourceInfo_fromRef(v_tk_2586_, v___x_2570_);
v___x_3379_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3382_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3336_) == 1)
{
lean_object* v_val_3383_; lean_object* v___x_3384_; 
v_val_3383_ = lean_ctor_get(v___y_3336_, 0);
lean_inc(v_val_3383_);
v___x_3384_ = l_Array_mkArray1___redArg(v_val_3383_);
v___y_3272_ = v___y_3331_;
v___y_3273_ = v___y_3340_;
v___y_3274_ = v___y_3333_;
v___y_3275_ = v___y_3339_;
v___y_3276_ = v___y_3334_;
v___y_3277_ = v___y_3343_;
v___y_3278_ = v___y_3345_;
v___y_3279_ = v___y_3335_;
v___y_3280_ = v___x_3382_;
v___y_3281_ = v___y_3341_;
v___y_3282_ = v___y_3336_;
v___y_3283_ = v___x_3380_;
v___y_3284_ = v___y_3342_;
v___y_3285_ = v___y_3332_;
v___y_3286_ = v___x_3375_;
v___y_3287_ = v___y_3338_;
v___y_3288_ = v___x_3377_;
v___y_3289_ = v___y_3344_;
v___y_3290_ = v_argsArray_3337_;
v___y_3291_ = v___x_3381_;
v___y_3292_ = v___x_3384_;
goto v___jp_3271_;
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3272_ = v___y_3331_;
v___y_3273_ = v___y_3340_;
v___y_3274_ = v___y_3333_;
v___y_3275_ = v___y_3339_;
v___y_3276_ = v___y_3334_;
v___y_3277_ = v___y_3343_;
v___y_3278_ = v___y_3345_;
v___y_3279_ = v___y_3335_;
v___y_3280_ = v___x_3382_;
v___y_3281_ = v___y_3341_;
v___y_3282_ = v___y_3336_;
v___y_3283_ = v___x_3380_;
v___y_3284_ = v___y_3342_;
v___y_3285_ = v___y_3332_;
v___y_3286_ = v___x_3375_;
v___y_3287_ = v___y_3338_;
v___y_3288_ = v___x_3377_;
v___y_3289_ = v___y_3344_;
v___y_3290_ = v_argsArray_3337_;
v___y_3291_ = v___x_3381_;
v___y_3292_ = v___x_3385_;
goto v___jp_3271_;
}
}
}
}
v___jp_3386_:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3400_, v___y_3399_, v___y_3393_, v___y_3397_, v___y_3389_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___x_3405_ = l_Lean_LibrarySuggestions_select(v_a_3404_, v___y_3402_, v___y_3399_, v___y_3393_, v___y_3397_, v___y_3389_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; size_t v_sz_3407_; size_t v___x_3408_; lean_object* v___x_3409_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v_sz_3407_ = lean_array_size(v_a_3406_);
v___x_3408_ = ((size_t)0ULL);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3406_, v_sz_3407_, v___x_3408_, v___y_3398_, v___y_3394_, v___y_3400_, v___y_3390_, v___y_3387_, v___y_3399_, v___y_3393_, v___y_3397_, v___y_3389_);
lean_dec(v_a_3406_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3331_ = v___y_3388_;
v___y_3332_ = v___y_3401_;
v___y_3333_ = v___y_3391_;
v___y_3334_ = v___y_3392_;
v___y_3335_ = v___y_3395_;
v___y_3336_ = v___y_3396_;
v_argsArray_3337_ = v_a_3410_;
v___y_3338_ = v___y_3394_;
v___y_3339_ = v___y_3400_;
v___y_3340_ = v___y_3390_;
v___y_3341_ = v___y_3387_;
v___y_3342_ = v___y_3399_;
v___y_3343_ = v___y_3393_;
v___y_3344_ = v___y_3397_;
v___y_3345_ = v___y_3389_;
goto v___jp_3330_;
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v___y_3401_);
lean_dec(v___y_3396_);
lean_dec(v___y_3391_);
lean_dec(v___y_3388_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v_a_3411_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3409_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3409_);
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
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3396_);
lean_dec(v___y_3391_);
lean_dec(v___y_3388_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v_a_3419_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3405_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3405_);
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
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3396_);
lean_dec(v___y_3391_);
lean_dec(v___y_3388_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v_a_3427_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3403_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3403_);
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
v___jp_3435_:
{
lean_object* v_config_3452_; uint8_t v_suggestions_3453_; 
v_config_3452_ = lean_ctor_get(v___y_3450_, 0);
lean_inc_ref(v_config_3452_);
lean_dec_ref(v___y_3450_);
v_suggestions_3453_ = lean_ctor_get_uint8(v_config_3452_, sizeof(void*)*3 + 26);
if (v_suggestions_3453_ == 0)
{
lean_dec_ref(v_config_3452_);
lean_dec_ref(v___f_2574_);
v___y_3331_ = v___y_3437_;
v___y_3332_ = v___y_3448_;
v___y_3333_ = v___y_3440_;
v___y_3334_ = v___y_3441_;
v___y_3335_ = v___y_3444_;
v___y_3336_ = v___y_3445_;
v_argsArray_3337_ = v___y_3451_;
v___y_3338_ = v___y_3443_;
v___y_3339_ = v___y_3449_;
v___y_3340_ = v___y_3439_;
v___y_3341_ = v___y_3436_;
v___y_3342_ = v___y_3447_;
v___y_3343_ = v___y_3442_;
v___y_3344_ = v___y_3446_;
v___y_3345_ = v___y_3438_;
goto v___jp_3330_;
}
else
{
lean_object* v_maxSuggestions_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_maxSuggestions_3454_ = lean_ctor_get(v_config_3452_, 2);
lean_inc(v_maxSuggestions_3454_);
lean_dec_ref(v_config_3452_);
v___x_3455_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3456_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3454_) == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_unsigned_to_nat(100u);
v___x_3458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v___x_3455_);
lean_ctor_set(v___x_3458_, 2, v___f_2574_);
lean_ctor_set(v___x_3458_, 3, v___x_3456_);
v___y_3387_ = v___y_3436_;
v___y_3388_ = v___y_3437_;
v___y_3389_ = v___y_3438_;
v___y_3390_ = v___y_3439_;
v___y_3391_ = v___y_3440_;
v___y_3392_ = v___y_3441_;
v___y_3393_ = v___y_3442_;
v___y_3394_ = v___y_3443_;
v___y_3395_ = v___y_3444_;
v___y_3396_ = v___y_3445_;
v___y_3397_ = v___y_3446_;
v___y_3398_ = v___y_3451_;
v___y_3399_ = v___y_3447_;
v___y_3400_ = v___y_3449_;
v___y_3401_ = v___y_3448_;
v___y_3402_ = v___x_3458_;
goto v___jp_3386_;
}
else
{
lean_object* v_val_3459_; lean_object* v___x_3460_; 
v_val_3459_ = lean_ctor_get(v_maxSuggestions_3454_, 0);
lean_inc(v_val_3459_);
lean_dec_ref_known(v_maxSuggestions_3454_, 1);
v___x_3460_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3460_, 0, v_val_3459_);
lean_ctor_set(v___x_3460_, 1, v___x_3455_);
lean_ctor_set(v___x_3460_, 2, v___f_2574_);
lean_ctor_set(v___x_3460_, 3, v___x_3456_);
v___y_3387_ = v___y_3436_;
v___y_3388_ = v___y_3437_;
v___y_3389_ = v___y_3438_;
v___y_3390_ = v___y_3439_;
v___y_3391_ = v___y_3440_;
v___y_3392_ = v___y_3441_;
v___y_3393_ = v___y_3442_;
v___y_3394_ = v___y_3443_;
v___y_3395_ = v___y_3444_;
v___y_3396_ = v___y_3445_;
v___y_3397_ = v___y_3446_;
v___y_3398_ = v___y_3451_;
v___y_3399_ = v___y_3447_;
v___y_3400_ = v___y_3449_;
v___y_3401_ = v___y_3448_;
v___y_3402_ = v___x_3460_;
goto v___jp_3386_;
}
}
}
v___jp_3461_:
{
uint8_t v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = 1;
lean_inc(v___y_3462_);
v___x_3477_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3462_, v___x_3476_, v___y_3468_, v___y_3470_, v___y_3464_);
if (lean_obj_tag(v___x_3477_) == 0)
{
if (lean_obj_tag(v___y_3474_) == 1)
{
lean_object* v_a_3478_; lean_object* v_val_3479_; lean_object* v___x_3480_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v_val_3479_ = lean_ctor_get(v___y_3474_, 0);
lean_inc(v_val_3479_);
lean_dec_ref_known(v___y_3474_, 1);
v___x_3480_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3479_);
lean_dec(v_val_3479_);
v___y_3436_ = v___y_3463_;
v___y_3437_ = v___y_3462_;
v___y_3438_ = v___y_3464_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3466_;
v___y_3441_ = v___x_3476_;
v___y_3442_ = v___y_3467_;
v___y_3443_ = v___y_3468_;
v___y_3444_ = v___y_3469_;
v___y_3445_ = v___y_3475_;
v___y_3446_ = v___y_3470_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v_a_3478_;
v___y_3451_ = v___x_3480_;
goto v___jp_3435_;
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3482_; 
lean_dec(v___y_3474_);
v_a_3481_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3482_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3436_ = v___y_3463_;
v___y_3437_ = v___y_3462_;
v___y_3438_ = v___y_3464_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3466_;
v___y_3441_ = v___x_3476_;
v___y_3442_ = v___y_3467_;
v___y_3443_ = v___y_3468_;
v___y_3444_ = v___y_3469_;
v___y_3445_ = v___y_3475_;
v___y_3446_ = v___y_3470_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v_a_3481_;
v___y_3451_ = v___x_3482_;
goto v___jp_3435_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3472_);
lean_dec(v___y_3466_);
lean_dec(v___y_3462_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v_a_3483_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3477_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3477_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_Syntax_getOptional_x3f(v___y_3495_);
lean_dec(v___y_3495_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_box(0);
v___y_3462_ = v___y_3492_;
v___y_3463_ = v___y_3501_;
v___y_3464_ = v___y_3505_;
v___y_3465_ = v___y_3500_;
v___y_3466_ = v___y_3494_;
v___y_3467_ = v___y_3503_;
v___y_3468_ = v___y_3498_;
v___y_3469_ = v___y_3496_;
v___y_3470_ = v___y_3504_;
v___y_3471_ = v___y_3502_;
v___y_3472_ = v___y_3493_;
v___y_3473_ = v___y_3499_;
v___y_3474_ = v_args_3497_;
v___y_3475_ = v___x_3507_;
goto v___jp_3461_;
}
else
{
lean_object* v_val_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_val_3508_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3506_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_val_3508_);
lean_dec(v___x_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_val_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
v___y_3462_ = v___y_3492_;
v___y_3463_ = v___y_3501_;
v___y_3464_ = v___y_3505_;
v___y_3465_ = v___y_3500_;
v___y_3466_ = v___y_3494_;
v___y_3467_ = v___y_3503_;
v___y_3468_ = v___y_3498_;
v___y_3469_ = v___y_3496_;
v___y_3470_ = v___y_3504_;
v___y_3471_ = v___y_3502_;
v___y_3472_ = v___y_3493_;
v___y_3473_ = v___y_3499_;
v___y_3474_ = v_args_3497_;
v___y_3475_ = v___x_3513_;
goto v___jp_3461_;
}
}
}
}
v___jp_3517_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3532_ = lean_unsigned_to_nat(3u);
v___x_3533_ = l_Lean_Syntax_getArg(v___y_3519_, v___x_3532_);
lean_dec(v___y_3519_);
v___x_3534_ = l_Lean_Syntax_isNone(v___x_3533_);
if (v___x_3534_ == 0)
{
uint8_t v___x_3535_; 
lean_inc(v___x_3533_);
v___x_3535_ = l_Lean_Syntax_matchesNull(v___x_3533_, v___x_3516_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; 
lean_dec(v___x_3533_);
lean_dec(v_o_3523_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3518_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_3536_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3536_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3537_ = l_Lean_Syntax_getArg(v___x_3533_, v___x_2585_);
lean_dec(v___x_3533_);
v___x_3538_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3539_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3538_);
lean_inc(v___x_3537_);
v___x_3540_ = l_Lean_Syntax_isOfKind(v___x_3537_, v___x_3539_);
lean_dec(v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_dec(v___x_3537_);
lean_dec(v_o_3523_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3518_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_3541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3541_;
}
else
{
lean_object* v___x_3542_; lean_object* v_args_3543_; lean_object* v___x_3544_; 
v___x_3542_ = l_Lean_Syntax_getArg(v___x_3537_, v___x_3516_);
lean_dec(v___x_3537_);
v_args_3543_ = l_Lean_Syntax_getArgs(v___x_3542_);
lean_dec(v___x_3542_);
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_args_3543_);
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3520_;
v___y_3494_ = v_o_3523_;
v___y_3495_ = v___y_3521_;
v___y_3496_ = v___y_3522_;
v_args_3497_ = v___x_3544_;
v___y_3498_ = v___y_3524_;
v___y_3499_ = v___y_3525_;
v___y_3500_ = v___y_3526_;
v___y_3501_ = v___y_3527_;
v___y_3502_ = v___y_3528_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3530_;
v___y_3505_ = v___y_3531_;
goto v___jp_3491_;
}
}
}
else
{
lean_object* v___x_3545_; 
lean_dec(v___x_3533_);
v___x_3545_ = lean_box(0);
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3520_;
v___y_3494_ = v_o_3523_;
v___y_3495_ = v___y_3521_;
v___y_3496_ = v___y_3522_;
v_args_3497_ = v___x_3545_;
v___y_3498_ = v___y_3524_;
v___y_3499_ = v___y_3525_;
v___y_3500_ = v___y_3526_;
v___y_3501_ = v___y_3527_;
v___y_3502_ = v___y_3528_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3530_;
v___y_3505_ = v___y_3531_;
goto v___jp_3491_;
}
}
v___jp_3546_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3556_ = lean_unsigned_to_nat(2u);
v___x_3557_ = l_Lean_Syntax_getArg(v_stx_2569_, v___x_3556_);
v___x_3558_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3559_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3558_);
lean_inc(v___x_3557_);
v___x_3560_ = l_Lean_Syntax_isOfKind(v___x_3557_, v___x_3559_);
lean_dec(v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_dec(v___x_3557_);
lean_dec(v_bang_3547_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_3561_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3561_;
}
else
{
lean_object* v_cfg_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_cfg_3562_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_2585_);
v___x_3563_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
lean_inc_ref(v___x_2571_);
v___x_3564_ = l_Lean_Name_mkStr4(v___x_2571_, v___x_2572_, v___x_2573_, v___x_3563_);
lean_inc(v_cfg_3562_);
v___x_3565_ = l_Lean_Syntax_isOfKind(v_cfg_3562_, v___x_3564_);
lean_dec(v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
lean_dec(v_cfg_3562_);
lean_dec(v___x_3557_);
lean_dec(v_bang_3547_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_3566_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3566_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3567_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_3516_);
v___x_3568_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_3556_);
v___x_3569_ = l_Lean_Syntax_isNone(v___x_3568_);
if (v___x_3569_ == 0)
{
uint8_t v___x_3570_; 
lean_inc(v___x_3568_);
v___x_3570_ = l_Lean_Syntax_matchesNull(v___x_3568_, v___x_3516_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v___x_3568_);
lean_dec(v___x_3567_);
lean_dec(v_cfg_3562_);
lean_dec(v___x_3557_);
lean_dec(v_bang_3547_);
lean_dec(v_tk_2586_);
lean_dec_ref(v___f_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2571_);
v___x_3571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3571_;
}
else
{
lean_object* v_o_3572_; lean_object* v___x_3573_; 
v_o_3572_ = l_Lean_Syntax_getArg(v___x_3568_, v___x_2585_);
lean_dec(v___x_3568_);
v___x_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_o_3572_);
v___y_3518_ = v_cfg_3562_;
v___y_3519_ = v___x_3557_;
v___y_3520_ = v_bang_3547_;
v___y_3521_ = v___x_3567_;
v___y_3522_ = v___x_3560_;
v_o_3523_ = v___x_3573_;
v___y_3524_ = v___y_3548_;
v___y_3525_ = v___y_3549_;
v___y_3526_ = v___y_3550_;
v___y_3527_ = v___y_3551_;
v___y_3528_ = v___y_3552_;
v___y_3529_ = v___y_3553_;
v___y_3530_ = v___y_3554_;
v___y_3531_ = v___y_3555_;
goto v___jp_3517_;
}
}
else
{
lean_object* v___x_3574_; 
lean_dec(v___x_3568_);
v___x_3574_ = lean_box(0);
v___y_3518_ = v_cfg_3562_;
v___y_3519_ = v___x_3557_;
v___y_3520_ = v_bang_3547_;
v___y_3521_ = v___x_3567_;
v___y_3522_ = v___x_3560_;
v_o_3523_ = v___x_3574_;
v___y_3524_ = v___y_3548_;
v___y_3525_ = v___y_3549_;
v___y_3526_ = v___y_3550_;
v___y_3527_ = v___y_3551_;
v___y_3528_ = v___y_3552_;
v___y_3529_ = v___y_3553_;
v___y_3530_ = v___y_3554_;
v___y_3531_ = v___y_3555_;
goto v___jp_3517_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2568_ = stack[0].m_num;
lean_object* v_stx_2569_ = stack[1].m_obj;
uint8_t v___x_2570_ = stack[2].m_num;
lean_object* v___x_2571_ = stack[3].m_obj;
lean_object* v___x_2572_ = stack[4].m_obj;
lean_object* v___x_2573_ = stack[5].m_obj;
lean_object* v___f_2574_ = stack[6].m_obj;
lean_object* v___y_2575_ = stack[7].m_obj;
lean_object* v___y_2576_ = stack[8].m_obj;
lean_object* v___y_2577_ = stack[9].m_obj;
lean_object* v___y_2578_ = stack[10].m_obj;
lean_object* v___y_2579_ = stack[11].m_obj;
lean_object* v___y_2580_ = stack[12].m_obj;
lean_object* v___y_2581_ = stack[13].m_obj;
lean_object* v___y_2582_ = stack[14].m_obj;
lean_object* v_res_3582_;
v_res_3582_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_2568_, v_stx_2569_, v___x_2570_, v___x_2571_, v___x_2572_, v___x_2573_, v___f_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
stack->m_obj
 = v_res_3582_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3583_, lean_object* v_stx_3584_, lean_object* v___x_3585_, lean_object* v___x_3586_, lean_object* v___x_3587_, lean_object* v___x_3588_, lean_object* v___f_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
uint8_t v___x_31129__boxed_3599_; uint8_t v___x_31130__boxed_3600_; lean_object* v_res_3601_; 
v___x_31129__boxed_3599_ = lean_unbox(v___x_3583_);
v___x_31130__boxed_3600_ = lean_unbox(v___x_3585_);
v_res_3601_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31129__boxed_3599_, v_stx_3584_, v___x_31130__boxed_3600_, v___x_3586_, v___x_3587_, v___x_3588_, v___f_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v_stx_3584_);
return v_res_3601_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; uint8_t v___x_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___y_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3621_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3608_);
v___x_3622_ = l_Lean_Syntax_isOfKind(v_stx_3608_, v___x_3621_);
v___x_3623_ = 1;
v___f_3624_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3625_ = lean_box(v___x_3622_);
v___x_3626_ = lean_box(v___x_3623_);
v___y_3627_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3627_, 0, v___x_3625_);
lean_closure_set(v___y_3627_, 1, v_stx_3608_);
lean_closure_set(v___y_3627_, 2, v___x_3626_);
lean_closure_set(v___y_3627_, 3, v___x_3618_);
lean_closure_set(v___y_3627_, 4, v___x_3619_);
lean_closure_set(v___y_3627_, 5, v___x_3620_);
lean_closure_set(v___y_3627_, 6, v___f_3624_);
v___x_3628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3628_, 0, v___y_3627_);
v___x_3629_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3628_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
return v___x_3629_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSimpAllTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3608_ = stack[0].m_obj;
lean_object* v_a_3609_ = stack[1].m_obj;
lean_object* v_a_3610_ = stack[2].m_obj;
lean_object* v_a_3611_ = stack[3].m_obj;
lean_object* v_a_3612_ = stack[4].m_obj;
lean_object* v_a_3613_ = stack[5].m_obj;
lean_object* v_a_3614_ = stack[6].m_obj;
lean_object* v_a_3615_ = stack[7].m_obj;
lean_object* v_a_3616_ = stack[8].m_obj;
lean_object* v_res_3630_;
v_res_3630_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
stack->m_obj
 = v_res_3630_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
return v_res_3641_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3642_, lean_object* v_as_3643_, lean_object* v_as_x27_3644_, lean_object* v_b_3645_, lean_object* v_a_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3642_, v_as_x27_3644_, v_b_3645_, v___y_3653_);
return v___x_3656_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3642_ = stack[0].m_obj;
lean_object* v_as_3643_ = stack[1].m_obj;
lean_object* v_as_x27_3644_ = stack[2].m_obj;
lean_object* v_b_3645_ = stack[3].m_obj;
lean_object* v___y_3647_ = stack[5].m_obj;
lean_object* v___y_3648_ = stack[6].m_obj;
lean_object* v___y_3649_ = stack[7].m_obj;
lean_object* v___y_3650_ = stack[8].m_obj;
lean_object* v___y_3651_ = stack[9].m_obj;
lean_object* v___y_3652_ = stack[10].m_obj;
lean_object* v___y_3653_ = stack[11].m_obj;
lean_object* v___y_3654_ = stack[12].m_obj;
lean_object* v_res_3657_;
v_res_3657_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3642_, v_as_3643_, v_as_x27_3644_, v_b_3645_, lean_box(0), v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
stack->m_obj
 = v_res_3657_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3658_, lean_object* v_as_3659_, lean_object* v_as_x27_3660_, lean_object* v_b_3661_, lean_object* v_a_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3658_, v_as_3659_, v_as_x27_3660_, v_b_3661_, v_a_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v_as_x27_3660_);
lean_dec(v_as_3659_);
lean_dec(v___x_3658_);
return v_res_3672_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3680_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3681_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3683_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3684_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3680_, v___x_3681_, v___x_3682_, v___x_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3685_;
v_res_3685_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
stack->m_obj
 = v_res_3685_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3687_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3715_ = l_Lean_addBuiltinDeclarationRanges(v___x_3713_, v___x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3716_;
v_res_3716_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
stack->m_obj
 = v_res_3716_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3718_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3719_, lean_object* v_simprocs_3720_, lean_object* v_fvarIdsToSimp_3721_, uint8_t v_simplifyTarget_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = lean_unsigned_to_nat(32u);
v___x_3732_ = lean_mk_empty_array_with_capacity(v___x_3731_);
lean_dec_ref(v___x_3732_);
v___x_3733_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3734_ = l_Lean_Meta_dsimpGoal(v_a_3730_, v_ctx_3719_, v_simprocs_3720_, v_simplifyTarget_3722_, v_fvarIdsToSimp_3721_, v___x_3733_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v_fst_3736_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
v_fst_3736_ = lean_ctor_get(v_a_3735_, 0);
if (lean_obj_tag(v_fst_3736_) == 0)
{
lean_object* v_snd_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_snd_3737_ = lean_ctor_get(v_a_3735_, 1);
lean_inc(v_snd_3737_);
lean_dec(v_a_3735_);
v___x_3738_ = lean_box(0);
v___x_3739_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3738_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v___x_3739_, 0);
lean_dec(v_unused_3747_);
v___x_3741_ = v___x_3739_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_dec(v___x_3739_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v_snd_3737_);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_snd_3737_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_snd_3737_);
v_a_3748_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3739_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3739_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v_snd_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3782_; 
lean_inc_ref(v_fst_3736_);
v_snd_3756_ = lean_ctor_get(v_a_3735_, 1);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_a_3735_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v_a_3735_, 0);
lean_dec(v_unused_3783_);
v___x_3758_ = v_a_3735_;
v_isShared_3759_ = v_isSharedCheck_3782_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_snd_3756_);
lean_dec(v_a_3735_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3782_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v_val_3760_; lean_object* v___x_3761_; lean_object* v___x_3763_; 
v_val_3760_ = lean_ctor_get(v_fst_3736_, 0);
lean_inc(v_val_3760_);
lean_dec_ref_known(v_fst_3736_, 1);
v___x_3761_ = lean_box(0);
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 1);
lean_ctor_set(v___x_3758_, 1, v___x_3761_);
lean_ctor_set(v___x_3758_, 0, v_val_3760_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_val_3760_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3763_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___x_3764_, 0);
lean_dec(v_unused_3772_);
v___x_3766_ = v___x_3764_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_dec(v___x_3764_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v_snd_3756_);
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_snd_3756_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v_snd_3756_);
v_a_3773_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3764_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3764_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3734_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3734_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v_fvarIdsToSimp_3721_);
lean_dec_ref(v_simprocs_3720_);
lean_dec_ref(v_ctx_3719_);
v_a_3792_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3729_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3729_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3719_ = stack[0].m_obj;
lean_object* v_simprocs_3720_ = stack[1].m_obj;
lean_object* v_fvarIdsToSimp_3721_ = stack[2].m_obj;
uint8_t v_simplifyTarget_3722_ = stack[3].m_num;
lean_object* v_a_3723_ = stack[4].m_obj;
lean_object* v_a_3724_ = stack[5].m_obj;
lean_object* v_a_3725_ = stack[6].m_obj;
lean_object* v_a_3726_ = stack[7].m_obj;
lean_object* v_a_3727_ = stack[8].m_obj;
lean_object* v_res_3800_;
v_res_3800_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3719_, v_simprocs_3720_, v_fvarIdsToSimp_3721_, v_simplifyTarget_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
stack->m_obj
 = v_res_3800_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3801_, lean_object* v_simprocs_3802_, lean_object* v_fvarIdsToSimp_3803_, lean_object* v_simplifyTarget_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
uint8_t v_simplifyTarget_boxed_3811_; lean_object* v_res_3812_; 
v_simplifyTarget_boxed_3811_ = lean_unbox(v_simplifyTarget_3804_);
v_res_3812_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3801_, v_simprocs_3802_, v_fvarIdsToSimp_3803_, v_simplifyTarget_boxed_3811_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
return v_res_3812_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3813_, lean_object* v_simprocs_3814_, lean_object* v_fvarIdsToSimp_3815_, uint8_t v_simplifyTarget_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3813_, v_simprocs_3814_, v_fvarIdsToSimp_3815_, v_simplifyTarget_3816_, v_a_3818_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
return v___x_3826_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3813_ = stack[0].m_obj;
lean_object* v_simprocs_3814_ = stack[1].m_obj;
lean_object* v_fvarIdsToSimp_3815_ = stack[2].m_obj;
uint8_t v_simplifyTarget_3816_ = stack[3].m_num;
lean_object* v_a_3817_ = stack[4].m_obj;
lean_object* v_a_3818_ = stack[5].m_obj;
lean_object* v_a_3819_ = stack[6].m_obj;
lean_object* v_a_3820_ = stack[7].m_obj;
lean_object* v_a_3821_ = stack[8].m_obj;
lean_object* v_a_3822_ = stack[9].m_obj;
lean_object* v_a_3823_ = stack[10].m_obj;
lean_object* v_a_3824_ = stack[11].m_obj;
lean_object* v_res_3827_;
v_res_3827_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3813_, v_simprocs_3814_, v_fvarIdsToSimp_3815_, v_simplifyTarget_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
stack->m_obj
 = v_res_3827_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3828_, lean_object* v_simprocs_3829_, lean_object* v_fvarIdsToSimp_3830_, lean_object* v_simplifyTarget_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
uint8_t v_simplifyTarget_boxed_3841_; lean_object* v_res_3842_; 
v_simplifyTarget_boxed_3841_ = lean_unbox(v_simplifyTarget_3831_);
v_res_3842_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3828_, v_simprocs_3829_, v_fvarIdsToSimp_3830_, v_simplifyTarget_boxed_3841_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
return v_res_3842_;
}
}
lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3843_, lean_object* v_simprocs_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3846_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = l_Lean_MVarId_getNondepPropHyps(v_a_3855_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; uint8_t v___x_3858_; lean_object* v___x_3859_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = 1;
v___x_3859_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3843_, v_simprocs_3844_, v_a_3857_, v___x_3858_, v___y_3846_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3859_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_simprocs_3844_);
lean_dec_ref(v_ctx_3843_);
v_a_3860_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3856_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3856_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec_ref(v_simprocs_3844_);
lean_dec_ref(v_ctx_3843_);
v_a_3868_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3854_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3854_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3843_ = stack[0].m_obj;
lean_object* v_simprocs_3844_ = stack[1].m_obj;
lean_object* v___y_3845_ = stack[2].m_obj;
lean_object* v___y_3846_ = stack[3].m_obj;
lean_object* v___y_3847_ = stack[4].m_obj;
lean_object* v___y_3848_ = stack[5].m_obj;
lean_object* v___y_3849_ = stack[6].m_obj;
lean_object* v___y_3850_ = stack[7].m_obj;
lean_object* v___y_3851_ = stack[8].m_obj;
lean_object* v___y_3852_ = stack[9].m_obj;
lean_object* v_res_3876_;
v_res_3876_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3843_, v_simprocs_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
stack->m_obj
 = v_res_3876_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3877_, lean_object* v_simprocs_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3877_, v_simprocs_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
return v_res_3888_;
}
}
lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3889_, lean_object* v_ctx_3890_, lean_object* v_simprocs_3891_, uint8_t v_type_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3889_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3904_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3890_, v_simprocs_3891_, v_a_3903_, v_type_3892_, v___y_3894_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3904_;
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec_ref(v_simprocs_3891_);
lean_dec_ref(v_ctx_3890_);
v_a_3905_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3902_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3902_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_hypotheses_3889_ = stack[0].m_obj;
lean_object* v_ctx_3890_ = stack[1].m_obj;
lean_object* v_simprocs_3891_ = stack[2].m_obj;
uint8_t v_type_3892_ = stack[3].m_num;
lean_object* v___y_3893_ = stack[4].m_obj;
lean_object* v___y_3894_ = stack[5].m_obj;
lean_object* v___y_3895_ = stack[6].m_obj;
lean_object* v___y_3896_ = stack[7].m_obj;
lean_object* v___y_3897_ = stack[8].m_obj;
lean_object* v___y_3898_ = stack[9].m_obj;
lean_object* v___y_3899_ = stack[10].m_obj;
lean_object* v___y_3900_ = stack[11].m_obj;
lean_object* v_res_3913_;
v_res_3913_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3889_, v_ctx_3890_, v_simprocs_3891_, v_type_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
stack->m_obj
 = v_res_3913_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3914_, lean_object* v_ctx_3915_, lean_object* v_simprocs_3916_, lean_object* v_type_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v_type_595__boxed_3927_; lean_object* v_res_3928_; 
v_type_595__boxed_3927_ = lean_unbox(v_type_3917_);
v_res_3928_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3914_, v_ctx_3915_, v_simprocs_3916_, v_type_595__boxed_3927_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
return v_res_3928_;
}
}
lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3929_, lean_object* v_simprocs_3930_, lean_object* v_loc_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
if (lean_obj_tag(v_loc_3931_) == 0)
{
lean_object* v___f_3941_; lean_object* v___x_3942_; 
v___f_3941_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3941_, 0, v_ctx_3929_);
lean_closure_set(v___f_3941_, 1, v_simprocs_3930_);
v___x_3942_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3941_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
return v___x_3942_;
}
else
{
lean_object* v_hypotheses_3943_; uint8_t v_type_3944_; lean_object* v___x_3945_; lean_object* v___f_3946_; lean_object* v___x_3947_; 
v_hypotheses_3943_ = lean_ctor_get(v_loc_3931_, 0);
lean_inc_ref(v_hypotheses_3943_);
v_type_3944_ = lean_ctor_get_uint8(v_loc_3931_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3931_, 1);
v___x_3945_ = lean_box(v_type_3944_);
v___f_3946_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3946_, 0, v_hypotheses_3943_);
lean_closure_set(v___f_3946_, 1, v_ctx_3929_);
lean_closure_set(v___f_3946_, 2, v_simprocs_3930_);
lean_closure_set(v___f_3946_, 3, v___x_3945_);
v___x_3947_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3946_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
return v___x_3947_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_dsimpLocation_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3929_ = stack[0].m_obj;
lean_object* v_simprocs_3930_ = stack[1].m_obj;
lean_object* v_loc_3931_ = stack[2].m_obj;
lean_object* v_a_3932_ = stack[3].m_obj;
lean_object* v_a_3933_ = stack[4].m_obj;
lean_object* v_a_3934_ = stack[5].m_obj;
lean_object* v_a_3935_ = stack[6].m_obj;
lean_object* v_a_3936_ = stack[7].m_obj;
lean_object* v_a_3937_ = stack[8].m_obj;
lean_object* v_a_3938_ = stack[9].m_obj;
lean_object* v_a_3939_ = stack[10].m_obj;
lean_object* v_res_3948_;
v_res_3948_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3929_, v_simprocs_3930_, v_loc_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
stack->m_obj
 = v_res_3948_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3949_, lean_object* v_simprocs_3950_, lean_object* v_loc_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3949_, v_simprocs_3950_, v_loc_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
return v_res_3961_;
}
}
lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3966_, lean_object* v_stx_3967_, uint8_t v___x_3968_, lean_object* v___x_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
if (v___x_3966_ == 0)
{
lean_object* v___x_3981_; 
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_3981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; lean_object* v_tk_3983_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; uint8_t v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v_stx_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; uint8_t v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; uint8_t v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; uint8_t v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; uint8_t v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; uint8_t v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; uint8_t v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; uint8_t v___y_4288_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; uint8_t v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4338_; lean_object* v___y_4339_; uint8_t v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v_args_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___x_4364_; lean_object* v___y_4366_; uint8_t v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v_o_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v_bang_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___x_4421_; uint8_t v___x_4422_; 
v___x_3982_ = lean_unsigned_to_nat(0u);
v_tk_3983_ = l_Lean_Syntax_getArg(v_stx_3967_, v___x_3982_);
v___x_4364_ = lean_unsigned_to_nat(1u);
v___x_4421_ = l_Lean_Syntax_getArg(v_stx_3967_, v___x_4364_);
v___x_4422_ = l_Lean_Syntax_isNone(v___x_4421_);
if (v___x_4422_ == 0)
{
uint8_t v___x_4423_; 
lean_inc(v___x_4421_);
v___x_4423_ = l_Lean_Syntax_matchesNull(v___x_4421_, v___x_4364_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; 
lean_dec(v___x_4421_);
lean_dec(v_tk_3983_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_4424_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4424_;
}
else
{
lean_object* v_bang_4425_; lean_object* v___x_4426_; 
v_bang_4425_ = l_Lean_Syntax_getArg(v___x_4421_, v___x_3982_);
lean_dec(v___x_4421_);
v___x_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4426_, 0, v_bang_4425_);
v_bang_4394_ = v___x_4426_;
v___y_4395_ = v___y_3972_;
v___y_4396_ = v___y_3973_;
v___y_4397_ = v___y_3974_;
v___y_4398_ = v___y_3975_;
v___y_4399_ = v___y_3976_;
v___y_4400_ = v___y_3977_;
v___y_4401_ = v___y_3978_;
v___y_4402_ = v___y_3979_;
goto v___jp_4393_;
}
}
else
{
lean_object* v___x_4427_; 
lean_dec(v___x_4421_);
v___x_4427_ = lean_box(0);
v_bang_4394_ = v___x_4427_;
v___y_4395_ = v___y_3972_;
v___y_4396_ = v___y_3973_;
v___y_4397_ = v___y_3974_;
v___y_4398_ = v___y_3975_;
v___y_4399_ = v___y_3976_;
v___y_4400_ = v___y_3977_;
v___y_4401_ = v___y_3978_;
v___y_4402_ = v___y_3979_;
goto v___jp_4393_;
}
v___jp_3984_:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3988_, v___y_3993_, v___y_3996_, v___y_3995_, v___y_3991_, v___y_3990_, v___y_3994_, v___y_3989_, v___y_3986_, v___y_3985_, v___y_3992_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v_usedTheorems_3999_; lean_object* v_diag_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4042_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v_usedTheorems_3999_ = lean_ctor_get(v_a_3998_, 0);
v_diag_4000_ = lean_ctor_get(v_a_3998_, 1);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_a_3998_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4002_ = v_a_3998_;
v_isShared_4003_ = v_isSharedCheck_4042_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_diag_4000_);
lean_inc(v_usedTheorems_3999_);
lean_dec(v_a_3998_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4042_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3987_, v_usedTheorems_3999_, v___y_3989_, v___y_3986_, v___y_3985_, v___y_3992_);
lean_dec_ref(v_usedTheorems_3999_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v_ref_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v_ref_4006_ = lean_ctor_get(v___y_3985_, 2);
v___x_4007_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 1, v_a_4005_);
lean_ctor_set(v___x_4002_, 0, v___x_4007_);
v___x_4009_ = v___x_4002_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_a_4005_);
v___x_4009_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4010_ = lean_box(0);
v___x_4011_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
lean_ctor_set(v___x_4011_, 2, v___x_4010_);
lean_ctor_set(v___x_4011_, 3, v___x_4010_);
lean_ctor_set(v___x_4011_, 4, v___x_4010_);
lean_ctor_set(v___x_4011_, 5, v___x_4010_);
lean_inc(v_ref_4006_);
v___x_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_ref_4006_);
v___x_4013_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_4014_ = 4;
v___x_4015_ = l_Lean_MessageData_nil;
v___x_4016_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3983_, v___x_4011_, v___x_4012_, v___x_4013_, v___x_4010_, v___x_4014_, v___x_4015_, v___y_3985_, v___y_3992_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v___x_4016_, 0);
lean_dec(v_unused_4024_);
v___x_4018_ = v___x_4016_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_dec(v___x_4016_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v_diag_4000_);
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_diag_4000_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v_diag_4000_);
v_a_4025_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4016_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4016_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_del_object(v___x_4002_);
lean_dec_ref(v_diag_4000_);
lean_dec(v_tk_3983_);
v_a_4034_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4004_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4004_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v___y_3987_);
lean_dec(v_tk_3983_);
v_a_4043_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_3997_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_3997_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
v___jp_4051_:
{
if (lean_obj_tag(v___y_4055_) == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4065_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set_uint8(v___x_4065_, sizeof(void*)*1, v___x_3968_);
v___y_3985_ = v___y_4053_;
v___y_3986_ = v___y_4052_;
v___y_3987_ = v___y_4054_;
v___y_3988_ = v___y_4063_;
v___y_3989_ = v___y_4056_;
v___y_3990_ = v___y_4057_;
v___y_3991_ = v___y_4058_;
v___y_3992_ = v___y_4060_;
v___y_3993_ = v___y_4059_;
v___y_3994_ = v___y_4062_;
v___y_3995_ = v___y_4061_;
v___y_3996_ = v___x_4065_;
goto v___jp_3984_;
}
else
{
lean_object* v_val_4066_; lean_object* v___x_4067_; 
v_val_4066_ = lean_ctor_get(v___y_4055_, 0);
lean_inc(v_val_4066_);
lean_dec_ref_known(v___y_4055_, 1);
v___x_4067_ = l_Lean_Elab_Tactic_expandLocation(v_val_4066_);
lean_dec(v_val_4066_);
v___y_3985_ = v___y_4053_;
v___y_3986_ = v___y_4052_;
v___y_3987_ = v___y_4054_;
v___y_3988_ = v___y_4063_;
v___y_3989_ = v___y_4056_;
v___y_3990_ = v___y_4057_;
v___y_3991_ = v___y_4058_;
v___y_3992_ = v___y_4060_;
v___y_3993_ = v___y_4059_;
v___y_3994_ = v___y_4062_;
v___y_3995_ = v___y_4061_;
v___y_3996_ = v___x_4067_;
goto v___jp_3984_;
}
}
v___jp_4068_:
{
uint8_t v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4081_ = 0;
v___x_4082_ = 2;
v___x_4083_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4084_ = lean_box(v___x_4081_);
v___x_4085_ = lean_box(v___x_4082_);
v___x_4086_ = lean_box(v___x_4081_);
lean_inc(v_stx_4072_);
v___x_4087_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4087_, 0, v_stx_4072_);
lean_closure_set(v___x_4087_, 1, v___x_4084_);
lean_closure_set(v___x_4087_, 2, v___x_4085_);
lean_closure_set(v___x_4087_, 3, v___x_4086_);
lean_closure_set(v___x_4087_, 4, v___x_4083_);
v___x_4088_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4087_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
if (lean_obj_tag(v___y_4071_) == 0)
{
lean_object* v_ctx_4090_; lean_object* v_simprocs_4091_; 
v_ctx_4090_ = lean_ctor_get(v_a_4089_, 0);
lean_inc_ref(v_ctx_4090_);
v_simprocs_4091_ = lean_ctor_get(v_a_4089_, 1);
lean_inc_ref(v_simprocs_4091_);
lean_dec(v_a_4089_);
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v_stx_4072_;
v___y_4055_ = v___y_4070_;
v___y_4056_ = v___y_4077_;
v___y_4057_ = v___y_4075_;
v___y_4058_ = v___y_4074_;
v___y_4059_ = v_simprocs_4091_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4073_;
v___y_4062_ = v___y_4076_;
v___y_4063_ = v_ctx_4090_;
goto v___jp_4051_;
}
else
{
lean_dec_ref_known(v___y_4071_, 1);
if (v___y_4069_ == 0)
{
lean_object* v_ctx_4092_; lean_object* v_simprocs_4093_; 
v_ctx_4092_ = lean_ctor_get(v_a_4089_, 0);
lean_inc_ref(v_ctx_4092_);
v_simprocs_4093_ = lean_ctor_get(v_a_4089_, 1);
lean_inc_ref(v_simprocs_4093_);
lean_dec(v_a_4089_);
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v_stx_4072_;
v___y_4055_ = v___y_4070_;
v___y_4056_ = v___y_4077_;
v___y_4057_ = v___y_4075_;
v___y_4058_ = v___y_4074_;
v___y_4059_ = v_simprocs_4093_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4073_;
v___y_4062_ = v___y_4076_;
v___y_4063_ = v_ctx_4092_;
goto v___jp_4051_;
}
else
{
lean_object* v_ctx_4094_; lean_object* v_simprocs_4095_; lean_object* v___x_4096_; 
v_ctx_4094_ = lean_ctor_get(v_a_4089_, 0);
lean_inc_ref(v_ctx_4094_);
v_simprocs_4095_ = lean_ctor_get(v_a_4089_, 1);
lean_inc_ref(v_simprocs_4095_);
lean_dec(v_a_4089_);
v___x_4096_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4094_);
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v_stx_4072_;
v___y_4055_ = v___y_4070_;
v___y_4056_ = v___y_4077_;
v___y_4057_ = v___y_4075_;
v___y_4058_ = v___y_4074_;
v___y_4059_ = v_simprocs_4095_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4073_;
v___y_4062_ = v___y_4076_;
v___y_4063_ = v___x_4096_;
goto v___jp_4051_;
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_stx_4072_);
lean_dec(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec(v_tk_3983_);
v_a_4097_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4088_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4088_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
v___jp_4105_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_inc_ref(v___y_4125_);
v___x_4127_ = l_Array_append___redArg(v___y_4125_, v___y_4126_);
lean_dec_ref(v___y_4126_);
lean_inc(v___y_4120_);
lean_inc(v___y_4112_);
v___x_4128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4128_, 0, v___y_4112_);
lean_ctor_set(v___x_4128_, 1, v___y_4120_);
lean_ctor_set(v___x_4128_, 2, v___x_4127_);
v___x_4129_ = l_Lean_Syntax_node6(v___y_4112_, v___y_4123_, v___y_4117_, v___y_4109_, v___y_4106_, v___y_4124_, v___y_4115_, v___x_4128_);
v___y_4069_ = v___y_4110_;
v___y_4070_ = v___y_4122_;
v___y_4071_ = v___y_4111_;
v_stx_4072_ = v___x_4129_;
v___y_4073_ = v___y_4113_;
v___y_4074_ = v___y_4107_;
v___y_4075_ = v___y_4121_;
v___y_4076_ = v___y_4119_;
v___y_4077_ = v___y_4114_;
v___y_4078_ = v___y_4116_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4108_;
goto v___jp_4068_;
}
v___jp_4130_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_inc_ref(v___y_4149_);
v___x_4151_ = l_Array_append___redArg(v___y_4149_, v___y_4150_);
lean_dec_ref(v___y_4150_);
lean_inc(v___y_4145_);
lean_inc(v___y_4136_);
v___x_4152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4152_, 0, v___y_4136_);
lean_ctor_set(v___x_4152_, 1, v___y_4145_);
lean_ctor_set(v___x_4152_, 2, v___x_4151_);
if (lean_obj_tag(v___y_4146_) == 0)
{
lean_object* v___x_4153_; 
v___x_4153_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4106_ = v___y_4131_;
v___y_4107_ = v___y_4132_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4136_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___x_4152_;
v___y_4116_ = v___y_4140_;
v___y_4117_ = v___y_4141_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4143_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4144_;
v___y_4122_ = v___y_4146_;
v___y_4123_ = v___y_4147_;
v___y_4124_ = v___y_4148_;
v___y_4125_ = v___y_4149_;
v___y_4126_ = v___x_4153_;
goto v___jp_4105_;
}
else
{
lean_object* v_val_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_val_4154_ = lean_ctor_get(v___y_4146_, 0);
v___x_4155_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4154_);
v___x_4156_ = lean_array_push(v___x_4155_, v_val_4154_);
v___y_4106_ = v___y_4131_;
v___y_4107_ = v___y_4132_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4136_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___x_4152_;
v___y_4116_ = v___y_4140_;
v___y_4117_ = v___y_4141_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4143_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4144_;
v___y_4122_ = v___y_4146_;
v___y_4123_ = v___y_4147_;
v___y_4124_ = v___y_4148_;
v___y_4125_ = v___y_4149_;
v___y_4126_ = v___x_4156_;
goto v___jp_4105_;
}
}
v___jp_4157_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
lean_inc_ref(v___y_4176_);
v___x_4178_ = l_Array_append___redArg(v___y_4176_, v___y_4177_);
lean_dec_ref(v___y_4177_);
lean_inc(v___y_4173_);
lean_inc(v___y_4164_);
v___x_4179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4179_, 0, v___y_4164_);
lean_ctor_set(v___x_4179_, 1, v___y_4173_);
lean_ctor_set(v___x_4179_, 2, v___x_4178_);
if (lean_obj_tag(v___y_4163_) == 1)
{
lean_object* v_val_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_val_4180_ = lean_ctor_get(v___y_4163_, 0);
lean_inc(v_val_4180_);
lean_dec_ref_known(v___y_4163_, 1);
v___x_4181_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4164_, 3);
v___x_4182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___y_4164_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
lean_inc_ref(v___y_4176_);
v___x_4183_ = l_Array_append___redArg(v___y_4176_, v_val_4180_);
lean_dec(v_val_4180_);
lean_inc(v___y_4173_);
v___x_4184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4184_, 0, v___y_4164_);
lean_ctor_set(v___x_4184_, 1, v___y_4173_);
lean_ctor_set(v___x_4184_, 2, v___x_4183_);
v___x_4185_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___y_4164_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = l_Array_mkArray3___redArg(v___x_4182_, v___x_4184_, v___x_4186_);
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
v___y_4136_ = v___y_4164_;
v___y_4137_ = v___y_4165_;
v___y_4138_ = v___y_4166_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4168_;
v___y_4141_ = v___y_4169_;
v___y_4142_ = v___y_4170_;
v___y_4143_ = v___y_4171_;
v___y_4144_ = v___y_4172_;
v___y_4145_ = v___y_4173_;
v___y_4146_ = v___y_4174_;
v___y_4147_ = v___y_4175_;
v___y_4148_ = v___x_4179_;
v___y_4149_ = v___y_4176_;
v___y_4150_ = v___x_4187_;
goto v___jp_4130_;
}
else
{
lean_object* v___x_4188_; 
lean_dec(v___y_4163_);
v___x_4188_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4159_;
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
v___y_4136_ = v___y_4164_;
v___y_4137_ = v___y_4165_;
v___y_4138_ = v___y_4166_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4168_;
v___y_4141_ = v___y_4169_;
v___y_4142_ = v___y_4170_;
v___y_4143_ = v___y_4171_;
v___y_4144_ = v___y_4172_;
v___y_4145_ = v___y_4173_;
v___y_4146_ = v___y_4174_;
v___y_4147_ = v___y_4175_;
v___y_4148_ = v___x_4179_;
v___y_4149_ = v___y_4176_;
v___y_4150_ = v___x_4188_;
goto v___jp_4130_;
}
}
v___jp_4189_:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_inc_ref(v___y_4198_);
v___x_4211_ = l_Array_append___redArg(v___y_4198_, v___y_4210_);
lean_dec_ref(v___y_4210_);
lean_inc(v___y_4195_);
lean_inc(v___y_4203_);
v___x_4212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4212_, 0, v___y_4203_);
lean_ctor_set(v___x_4212_, 1, v___y_4195_);
lean_ctor_set(v___x_4212_, 2, v___x_4211_);
v___x_4213_ = l_Lean_Syntax_node6(v___y_4203_, v___y_4208_, v___y_4190_, v___y_4193_, v___y_4207_, v___y_4209_, v___y_4197_, v___x_4212_);
v___y_4069_ = v___y_4194_;
v___y_4070_ = v___y_4206_;
v___y_4071_ = v___y_4196_;
v_stx_4072_ = v___x_4213_;
v___y_4073_ = v___y_4199_;
v___y_4074_ = v___y_4191_;
v___y_4075_ = v___y_4205_;
v___y_4076_ = v___y_4204_;
v___y_4077_ = v___y_4200_;
v___y_4078_ = v___y_4201_;
v___y_4079_ = v___y_4202_;
v___y_4080_ = v___y_4192_;
goto v___jp_4068_;
}
v___jp_4214_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_inc_ref(v___y_4222_);
v___x_4235_ = l_Array_append___redArg(v___y_4222_, v___y_4234_);
lean_dec_ref(v___y_4234_);
lean_inc(v___y_4220_);
lean_inc(v___y_4227_);
v___x_4236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4236_, 0, v___y_4227_);
lean_ctor_set(v___x_4236_, 1, v___y_4220_);
lean_ctor_set(v___x_4236_, 2, v___x_4235_);
if (lean_obj_tag(v___y_4230_) == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4190_ = v___y_4215_;
v___y_4191_ = v___y_4216_;
v___y_4192_ = v___y_4217_;
v___y_4193_ = v___y_4218_;
v___y_4194_ = v___y_4219_;
v___y_4195_ = v___y_4220_;
v___y_4196_ = v___y_4221_;
v___y_4197_ = v___x_4236_;
v___y_4198_ = v___y_4222_;
v___y_4199_ = v___y_4223_;
v___y_4200_ = v___y_4224_;
v___y_4201_ = v___y_4225_;
v___y_4202_ = v___y_4226_;
v___y_4203_ = v___y_4227_;
v___y_4204_ = v___y_4228_;
v___y_4205_ = v___y_4229_;
v___y_4206_ = v___y_4230_;
v___y_4207_ = v___y_4231_;
v___y_4208_ = v___y_4233_;
v___y_4209_ = v___y_4232_;
v___y_4210_ = v___x_4237_;
goto v___jp_4189_;
}
else
{
lean_object* v_val_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_val_4238_ = lean_ctor_get(v___y_4230_, 0);
v___x_4239_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4238_);
v___x_4240_ = lean_array_push(v___x_4239_, v_val_4238_);
v___y_4190_ = v___y_4215_;
v___y_4191_ = v___y_4216_;
v___y_4192_ = v___y_4217_;
v___y_4193_ = v___y_4218_;
v___y_4194_ = v___y_4219_;
v___y_4195_ = v___y_4220_;
v___y_4196_ = v___y_4221_;
v___y_4197_ = v___x_4236_;
v___y_4198_ = v___y_4222_;
v___y_4199_ = v___y_4223_;
v___y_4200_ = v___y_4224_;
v___y_4201_ = v___y_4225_;
v___y_4202_ = v___y_4226_;
v___y_4203_ = v___y_4227_;
v___y_4204_ = v___y_4228_;
v___y_4205_ = v___y_4229_;
v___y_4206_ = v___y_4230_;
v___y_4207_ = v___y_4231_;
v___y_4208_ = v___y_4233_;
v___y_4209_ = v___y_4232_;
v___y_4210_ = v___x_4240_;
goto v___jp_4189_;
}
}
v___jp_4241_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_inc_ref(v___y_4250_);
v___x_4262_ = l_Array_append___redArg(v___y_4250_, v___y_4261_);
lean_dec_ref(v___y_4261_);
lean_inc(v___y_4247_);
lean_inc(v___y_4255_);
v___x_4263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4263_, 0, v___y_4255_);
lean_ctor_set(v___x_4263_, 1, v___y_4247_);
lean_ctor_set(v___x_4263_, 2, v___x_4262_);
if (lean_obj_tag(v___y_4248_) == 1)
{
lean_object* v_val_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v_val_4264_ = lean_ctor_get(v___y_4248_, 0);
lean_inc(v_val_4264_);
lean_dec_ref_known(v___y_4248_, 1);
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4255_, 3);
v___x_4266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___y_4255_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
lean_inc_ref(v___y_4250_);
v___x_4267_ = l_Array_append___redArg(v___y_4250_, v_val_4264_);
lean_dec(v_val_4264_);
lean_inc(v___y_4247_);
v___x_4268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4268_, 0, v___y_4255_);
lean_ctor_set(v___x_4268_, 1, v___y_4247_);
lean_ctor_set(v___x_4268_, 2, v___x_4267_);
v___x_4269_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___y_4255_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l_Array_mkArray3___redArg(v___x_4266_, v___x_4268_, v___x_4270_);
v___y_4215_ = v___y_4242_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4244_;
v___y_4218_ = v___y_4245_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4249_;
v___y_4222_ = v___y_4250_;
v___y_4223_ = v___y_4251_;
v___y_4224_ = v___y_4252_;
v___y_4225_ = v___y_4253_;
v___y_4226_ = v___y_4254_;
v___y_4227_ = v___y_4255_;
v___y_4228_ = v___y_4256_;
v___y_4229_ = v___y_4257_;
v___y_4230_ = v___y_4258_;
v___y_4231_ = v___y_4259_;
v___y_4232_ = v___x_4263_;
v___y_4233_ = v___y_4260_;
v___y_4234_ = v___x_4271_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4272_; 
lean_dec(v___y_4248_);
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4215_ = v___y_4242_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4244_;
v___y_4218_ = v___y_4245_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4249_;
v___y_4222_ = v___y_4250_;
v___y_4223_ = v___y_4251_;
v___y_4224_ = v___y_4252_;
v___y_4225_ = v___y_4253_;
v___y_4226_ = v___y_4254_;
v___y_4227_ = v___y_4255_;
v___y_4228_ = v___y_4256_;
v___y_4229_ = v___y_4257_;
v___y_4230_ = v___y_4258_;
v___y_4231_ = v___y_4259_;
v___y_4232_ = v___x_4263_;
v___y_4233_ = v___y_4260_;
v___y_4234_ = v___x_4272_;
goto v___jp_4214_;
}
}
v___jp_4273_:
{
lean_object* v_ref_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_ref_4289_ = lean_ctor_get(v___y_4283_, 2);
v___x_4290_ = l_Lean_SourceInfo_fromRef(v_ref_4289_, v___y_4288_);
v___x_4291_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4292_ = l_Lean_Name_mkStr4(v___x_3969_, v___x_3970_, v___x_3971_, v___x_4291_);
v___x_4293_ = l_Lean_SourceInfo_fromRef(v_tk_3983_, v___x_3968_);
v___x_4294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set(v___x_4294_, 1, v___x_4291_);
v___x_4295_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4296_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4290_);
v___x_4297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4290_);
lean_ctor_set(v___x_4297_, 1, v___x_4295_);
lean_ctor_set(v___x_4297_, 2, v___x_4296_);
if (lean_obj_tag(v___y_4285_) == 1)
{
lean_object* v_val_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_val_4298_ = lean_ctor_get(v___y_4285_, 0);
lean_inc(v_val_4298_);
lean_dec_ref_known(v___y_4285_, 1);
v___x_4299_ = l_Lean_SourceInfo_fromRef(v_val_4298_, v___x_3968_);
lean_dec(v_val_4298_);
v___x_4300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Array_mkArray1___redArg(v___x_4301_);
v___y_4158_ = v___x_4297_;
v___y_4159_ = v___y_4274_;
v___y_4160_ = v___y_4275_;
v___y_4161_ = v___y_4276_;
v___y_4162_ = v___y_4277_;
v___y_4163_ = v___y_4278_;
v___y_4164_ = v___x_4290_;
v___y_4165_ = v___y_4279_;
v___y_4166_ = v___y_4280_;
v___y_4167_ = v___y_4281_;
v___y_4168_ = v___y_4282_;
v___y_4169_ = v___x_4294_;
v___y_4170_ = v___y_4283_;
v___y_4171_ = v___y_4284_;
v___y_4172_ = v___y_4286_;
v___y_4173_ = v___x_4295_;
v___y_4174_ = v___y_4287_;
v___y_4175_ = v___x_4292_;
v___y_4176_ = v___x_4296_;
v___y_4177_ = v___x_4302_;
goto v___jp_4157_;
}
else
{
lean_object* v___x_4303_; 
lean_dec(v___y_4285_);
v___x_4303_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4158_ = v___x_4297_;
v___y_4159_ = v___y_4274_;
v___y_4160_ = v___y_4275_;
v___y_4161_ = v___y_4276_;
v___y_4162_ = v___y_4277_;
v___y_4163_ = v___y_4278_;
v___y_4164_ = v___x_4290_;
v___y_4165_ = v___y_4279_;
v___y_4166_ = v___y_4280_;
v___y_4167_ = v___y_4281_;
v___y_4168_ = v___y_4282_;
v___y_4169_ = v___x_4294_;
v___y_4170_ = v___y_4283_;
v___y_4171_ = v___y_4284_;
v___y_4172_ = v___y_4286_;
v___y_4173_ = v___x_4295_;
v___y_4174_ = v___y_4287_;
v___y_4175_ = v___x_4292_;
v___y_4176_ = v___x_4296_;
v___y_4177_ = v___x_4303_;
goto v___jp_4157_;
}
}
v___jp_4304_:
{
if (lean_obj_tag(v___y_4310_) == 0)
{
uint8_t v___x_4319_; 
v___x_4319_ = 0;
v___y_4274_ = v___y_4305_;
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4307_;
v___y_4277_ = v___y_4308_;
v___y_4278_ = v___y_4309_;
v___y_4279_ = v___y_4310_;
v___y_4280_ = v___y_4311_;
v___y_4281_ = v___y_4312_;
v___y_4282_ = v___y_4313_;
v___y_4283_ = v___y_4314_;
v___y_4284_ = v___y_4315_;
v___y_4285_ = v___y_4316_;
v___y_4286_ = v___y_4317_;
v___y_4287_ = v___y_4318_;
v___y_4288_ = v___x_4319_;
goto v___jp_4273_;
}
else
{
if (v___y_4308_ == 0)
{
v___y_4274_ = v___y_4305_;
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4307_;
v___y_4277_ = v___y_4308_;
v___y_4278_ = v___y_4309_;
v___y_4279_ = v___y_4310_;
v___y_4280_ = v___y_4311_;
v___y_4281_ = v___y_4312_;
v___y_4282_ = v___y_4313_;
v___y_4283_ = v___y_4314_;
v___y_4284_ = v___y_4315_;
v___y_4285_ = v___y_4316_;
v___y_4286_ = v___y_4317_;
v___y_4287_ = v___y_4318_;
v___y_4288_ = v___y_4308_;
goto v___jp_4273_;
}
else
{
lean_object* v_ref_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_ref_4320_ = lean_ctor_get(v___y_4314_, 2);
v___x_4321_ = 0;
v___x_4322_ = l_Lean_SourceInfo_fromRef(v_ref_4320_, v___x_4321_);
v___x_4323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4324_ = l_Lean_Name_mkStr4(v___x_3969_, v___x_3970_, v___x_3971_, v___x_4323_);
v___x_4325_ = l_Lean_SourceInfo_fromRef(v_tk_3983_, v___x_3968_);
v___x_4326_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4329_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4322_);
v___x_4330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4322_);
lean_ctor_set(v___x_4330_, 1, v___x_4328_);
lean_ctor_set(v___x_4330_, 2, v___x_4329_);
if (lean_obj_tag(v___y_4316_) == 1)
{
lean_object* v_val_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v_val_4331_ = lean_ctor_get(v___y_4316_, 0);
lean_inc(v_val_4331_);
lean_dec_ref_known(v___y_4316_, 1);
v___x_4332_ = l_Lean_SourceInfo_fromRef(v_val_4331_, v___x_3968_);
lean_dec(v_val_4331_);
v___x_4333_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = l_Array_mkArray1___redArg(v___x_4334_);
v___y_4242_ = v___x_4327_;
v___y_4243_ = v___y_4305_;
v___y_4244_ = v___y_4306_;
v___y_4245_ = v___y_4307_;
v___y_4246_ = v___y_4308_;
v___y_4247_ = v___x_4328_;
v___y_4248_ = v___y_4309_;
v___y_4249_ = v___y_4310_;
v___y_4250_ = v___x_4329_;
v___y_4251_ = v___y_4311_;
v___y_4252_ = v___y_4312_;
v___y_4253_ = v___y_4313_;
v___y_4254_ = v___y_4314_;
v___y_4255_ = v___x_4322_;
v___y_4256_ = v___y_4315_;
v___y_4257_ = v___y_4317_;
v___y_4258_ = v___y_4318_;
v___y_4259_ = v___x_4330_;
v___y_4260_ = v___x_4324_;
v___y_4261_ = v___x_4335_;
goto v___jp_4241_;
}
else
{
lean_object* v___x_4336_; 
lean_dec(v___y_4316_);
v___x_4336_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4242_ = v___x_4327_;
v___y_4243_ = v___y_4305_;
v___y_4244_ = v___y_4306_;
v___y_4245_ = v___y_4307_;
v___y_4246_ = v___y_4308_;
v___y_4247_ = v___x_4328_;
v___y_4248_ = v___y_4309_;
v___y_4249_ = v___y_4310_;
v___y_4250_ = v___x_4329_;
v___y_4251_ = v___y_4311_;
v___y_4252_ = v___y_4312_;
v___y_4253_ = v___y_4313_;
v___y_4254_ = v___y_4314_;
v___y_4255_ = v___x_4322_;
v___y_4256_ = v___y_4315_;
v___y_4257_ = v___y_4317_;
v___y_4258_ = v___y_4318_;
v___y_4259_ = v___x_4330_;
v___y_4260_ = v___x_4324_;
v___y_4261_ = v___x_4336_;
goto v___jp_4241_;
}
}
}
}
v___jp_4337_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_unsigned_to_nat(3u);
v___x_4353_ = l_Lean_Syntax_getArg(v___y_4341_, v___x_4352_);
lean_dec(v___y_4341_);
v___x_4354_ = l_Lean_Syntax_getOptional_x3f(v___x_4353_);
lean_dec(v___x_4353_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_box(0);
v___y_4305_ = v___y_4345_;
v___y_4306_ = v___y_4351_;
v___y_4307_ = v___y_4338_;
v___y_4308_ = v___y_4340_;
v___y_4309_ = v_args_4343_;
v___y_4310_ = v___y_4342_;
v___y_4311_ = v___y_4344_;
v___y_4312_ = v___y_4348_;
v___y_4313_ = v___y_4349_;
v___y_4314_ = v___y_4350_;
v___y_4315_ = v___y_4347_;
v___y_4316_ = v___y_4339_;
v___y_4317_ = v___y_4346_;
v___y_4318_ = v___x_4355_;
goto v___jp_4304_;
}
else
{
lean_object* v_val_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_val_4356_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4354_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_val_4356_);
lean_dec(v___x_4354_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_val_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
v___y_4305_ = v___y_4345_;
v___y_4306_ = v___y_4351_;
v___y_4307_ = v___y_4338_;
v___y_4308_ = v___y_4340_;
v___y_4309_ = v_args_4343_;
v___y_4310_ = v___y_4342_;
v___y_4311_ = v___y_4344_;
v___y_4312_ = v___y_4348_;
v___y_4313_ = v___y_4349_;
v___y_4314_ = v___y_4350_;
v___y_4315_ = v___y_4347_;
v___y_4316_ = v___y_4339_;
v___y_4317_ = v___y_4346_;
v___y_4318_ = v___x_4361_;
goto v___jp_4304_;
}
}
}
}
v___jp_4365_:
{
lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4380_ = l_Lean_Syntax_getArg(v___y_4369_, v___y_4368_);
v___x_4381_ = l_Lean_Syntax_isNone(v___x_4380_);
if (v___x_4381_ == 0)
{
uint8_t v___x_4382_; 
lean_inc(v___x_4380_);
v___x_4382_ = l_Lean_Syntax_matchesNull(v___x_4380_, v___x_4364_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; 
lean_dec(v___x_4380_);
lean_dec(v_o_4371_);
lean_dec(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec(v___y_4366_);
lean_dec(v_tk_3983_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_4383_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4383_;
}
else
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4384_ = l_Lean_Syntax_getArg(v___x_4380_, v___x_3982_);
lean_dec(v___x_4380_);
v___x_4385_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3970_);
lean_inc_ref(v___x_3969_);
v___x_4386_ = l_Lean_Name_mkStr4(v___x_3969_, v___x_3970_, v___x_3971_, v___x_4385_);
lean_inc(v___x_4384_);
v___x_4387_ = l_Lean_Syntax_isOfKind(v___x_4384_, v___x_4386_);
lean_dec(v___x_4386_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_dec(v___x_4384_);
lean_dec(v_o_4371_);
lean_dec(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec(v___y_4366_);
lean_dec(v_tk_3983_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_4388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; lean_object* v_args_4390_; lean_object* v___x_4391_; 
v___x_4389_ = l_Lean_Syntax_getArg(v___x_4384_, v___x_4364_);
lean_dec(v___x_4384_);
v_args_4390_ = l_Lean_Syntax_getArgs(v___x_4389_);
lean_dec(v___x_4389_);
v___x_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4391_, 0, v_args_4390_);
v___y_4338_ = v___y_4366_;
v___y_4339_ = v_o_4371_;
v___y_4340_ = v___y_4367_;
v___y_4341_ = v___y_4369_;
v___y_4342_ = v___y_4370_;
v_args_4343_ = v___x_4391_;
v___y_4344_ = v___y_4372_;
v___y_4345_ = v___y_4373_;
v___y_4346_ = v___y_4374_;
v___y_4347_ = v___y_4375_;
v___y_4348_ = v___y_4376_;
v___y_4349_ = v___y_4377_;
v___y_4350_ = v___y_4378_;
v___y_4351_ = v___y_4379_;
goto v___jp_4337_;
}
}
}
else
{
lean_object* v___x_4392_; 
lean_dec(v___x_4380_);
v___x_4392_ = lean_box(0);
v___y_4338_ = v___y_4366_;
v___y_4339_ = v_o_4371_;
v___y_4340_ = v___y_4367_;
v___y_4341_ = v___y_4369_;
v___y_4342_ = v___y_4370_;
v_args_4343_ = v___x_4392_;
v___y_4344_ = v___y_4372_;
v___y_4345_ = v___y_4373_;
v___y_4346_ = v___y_4374_;
v___y_4347_ = v___y_4375_;
v___y_4348_ = v___y_4376_;
v___y_4349_ = v___y_4377_;
v___y_4350_ = v___y_4378_;
v___y_4351_ = v___y_4379_;
goto v___jp_4337_;
}
}
v___jp_4393_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4403_ = lean_unsigned_to_nat(2u);
v___x_4404_ = l_Lean_Syntax_getArg(v_stx_3967_, v___x_4403_);
v___x_4405_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3970_);
lean_inc_ref(v___x_3969_);
v___x_4406_ = l_Lean_Name_mkStr4(v___x_3969_, v___x_3970_, v___x_3971_, v___x_4405_);
lean_inc(v___x_4404_);
v___x_4407_ = l_Lean_Syntax_isOfKind(v___x_4404_, v___x_4406_);
lean_dec(v___x_4406_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
lean_dec(v___x_4404_);
lean_dec(v_bang_4394_);
lean_dec(v_tk_3983_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_4408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4408_;
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; uint8_t v___x_4412_; 
v___x_4409_ = l_Lean_Syntax_getArg(v___x_4404_, v___x_3982_);
v___x_4410_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3970_);
lean_inc_ref(v___x_3969_);
v___x_4411_ = l_Lean_Name_mkStr4(v___x_3969_, v___x_3970_, v___x_3971_, v___x_4410_);
lean_inc(v___x_4409_);
v___x_4412_ = l_Lean_Syntax_isOfKind(v___x_4409_, v___x_4411_);
lean_dec(v___x_4411_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; 
lean_dec(v___x_4409_);
lean_dec(v___x_4404_);
lean_dec(v_bang_4394_);
lean_dec(v_tk_3983_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_4413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4413_;
}
else
{
lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4414_ = l_Lean_Syntax_getArg(v___x_4404_, v___x_4364_);
v___x_4415_ = l_Lean_Syntax_isNone(v___x_4414_);
if (v___x_4415_ == 0)
{
uint8_t v___x_4416_; 
lean_inc(v___x_4414_);
v___x_4416_ = l_Lean_Syntax_matchesNull(v___x_4414_, v___x_4364_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; 
lean_dec(v___x_4414_);
lean_dec(v___x_4409_);
lean_dec(v___x_4404_);
lean_dec(v_bang_4394_);
lean_dec(v_tk_3983_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v___x_3969_);
v___x_4417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4417_;
}
else
{
lean_object* v_o_4418_; lean_object* v___x_4419_; 
v_o_4418_ = l_Lean_Syntax_getArg(v___x_4414_, v___x_3982_);
lean_dec(v___x_4414_);
v___x_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4419_, 0, v_o_4418_);
v___y_4366_ = v___x_4409_;
v___y_4367_ = v___x_4407_;
v___y_4368_ = v___x_4403_;
v___y_4369_ = v___x_4404_;
v___y_4370_ = v_bang_4394_;
v_o_4371_ = v___x_4419_;
v___y_4372_ = v___y_4395_;
v___y_4373_ = v___y_4396_;
v___y_4374_ = v___y_4397_;
v___y_4375_ = v___y_4398_;
v___y_4376_ = v___y_4399_;
v___y_4377_ = v___y_4400_;
v___y_4378_ = v___y_4401_;
v___y_4379_ = v___y_4402_;
goto v___jp_4365_;
}
}
else
{
lean_object* v___x_4420_; 
lean_dec(v___x_4414_);
v___x_4420_ = lean_box(0);
v___y_4366_ = v___x_4409_;
v___y_4367_ = v___x_4407_;
v___y_4368_ = v___x_4403_;
v___y_4369_ = v___x_4404_;
v___y_4370_ = v_bang_4394_;
v_o_4371_ = v___x_4420_;
v___y_4372_ = v___y_4395_;
v___y_4373_ = v___y_4396_;
v___y_4374_ = v___y_4397_;
v___y_4375_ = v___y_4398_;
v___y_4376_ = v___y_4399_;
v___y_4377_ = v___y_4400_;
v___y_4378_ = v___y_4401_;
v___y_4379_ = v___y_4402_;
goto v___jp_4365_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalDSimpTrace___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3966_ = stack[0].m_num;
lean_object* v_stx_3967_ = stack[1].m_obj;
uint8_t v___x_3968_ = stack[2].m_num;
lean_object* v___x_3969_ = stack[3].m_obj;
lean_object* v___x_3970_ = stack[4].m_obj;
lean_object* v___x_3971_ = stack[5].m_obj;
lean_object* v___y_3972_ = stack[6].m_obj;
lean_object* v___y_3973_ = stack[7].m_obj;
lean_object* v___y_3974_ = stack[8].m_obj;
lean_object* v___y_3975_ = stack[9].m_obj;
lean_object* v___y_3976_ = stack[10].m_obj;
lean_object* v___y_3977_ = stack[11].m_obj;
lean_object* v___y_3978_ = stack[12].m_obj;
lean_object* v___y_3979_ = stack[13].m_obj;
lean_object* v_res_4428_;
v_res_4428_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_3966_, v_stx_3967_, v___x_3968_, v___x_3969_, v___x_3970_, v___x_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
stack->m_obj
 = v_res_4428_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4429_, lean_object* v_stx_4430_, lean_object* v___x_4431_, lean_object* v___x_4432_, lean_object* v___x_4433_, lean_object* v___x_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
uint8_t v___x_8035__boxed_4444_; uint8_t v___x_8036__boxed_4445_; lean_object* v_res_4446_; 
v___x_8035__boxed_4444_ = lean_unbox(v___x_4429_);
v___x_8036__boxed_4445_ = lean_unbox(v___x_4431_);
v_res_4446_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8035__boxed_4444_, v_stx_4430_, v___x_8036__boxed_4445_, v___x_4432_, v___x_4433_, v___x_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v_stx_4430_);
return v_res_4446_;
}
}
lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; uint8_t v___x_4467_; uint8_t v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___y_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4466_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4453_);
v___x_4467_ = l_Lean_Syntax_isOfKind(v_stx_4453_, v___x_4466_);
v___x_4468_ = 1;
v___x_4469_ = lean_box(v___x_4467_);
v___x_4470_ = lean_box(v___x_4468_);
v___y_4471_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4471_, 0, v___x_4469_);
lean_closure_set(v___y_4471_, 1, v_stx_4453_);
lean_closure_set(v___y_4471_, 2, v___x_4470_);
lean_closure_set(v___y_4471_, 3, v___x_4463_);
lean_closure_set(v___y_4471_, 4, v___x_4464_);
lean_closure_set(v___y_4471_, 5, v___x_4465_);
v___x_4472_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4472_, 0, v___y_4471_);
v___x_4473_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4472_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
return v___x_4473_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalDSimpTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4453_ = stack[0].m_obj;
lean_object* v_a_4454_ = stack[1].m_obj;
lean_object* v_a_4455_ = stack[2].m_obj;
lean_object* v_a_4456_ = stack[3].m_obj;
lean_object* v_a_4457_ = stack[4].m_obj;
lean_object* v_a_4458_ = stack[5].m_obj;
lean_object* v_a_4459_ = stack[6].m_obj;
lean_object* v_a_4460_ = stack[7].m_obj;
lean_object* v_a_4461_ = stack[8].m_obj;
lean_object* v_res_4474_;
v_res_4474_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
stack->m_obj
 = v_res_4474_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
return v_res_4485_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4493_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4494_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4496_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4497_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4493_, v___x_4494_, v___x_4495_, v___x_4496_);
return v___x_4497_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4498_;
v_res_4498_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
stack->m_obj
 = v_res_4498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4500_;
}
}
lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4529_ = l_Lean_addBuiltinDeclarationRanges(v___x_4527_, v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4530_;
v_res_4530_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
stack->m_obj
 = v_res_4530_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4532_;
}
}
lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_SimpTrace(builtin);
}
#ifdef __cplusplus
}
#endif
