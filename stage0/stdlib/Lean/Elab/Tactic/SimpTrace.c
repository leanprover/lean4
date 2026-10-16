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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(lean_object* v_as_12_, size_t v_i_13_, size_t v_stop_14_, lean_object* v_b_15_){
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
lean_dec_ref_known(v___x_48_, 2);
lean_dec(v_pre_49_);
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
lean_dec(v_pre_28_);
lean_dec_ref_known(v_pre_27_, 2);
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
lean_dec_ref_known(v___x_25_, 2);
lean_dec(v_pre_26_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(lean_object* v_cfg_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_nullNode_95_; lean_object* v___y_97_; lean_object* v_configItems_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v_nullNode_95_ = l_Lean_Syntax_getArg(v_cfg_92_, v___x_94_);
v_configItems_101_ = l_Lean_Syntax_getArgs(v_nullNode_95_);
v___x_102_ = lean_array_get_size(v_configItems_101_);
v___x_103_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_104_ = lean_nat_dec_lt(v___x_94_, v___x_102_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_103_;
goto v___jp_96_;
}
else
{
size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_102_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_101_, v___x_105_, v___x_106_, v___x_103_);
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_107_;
goto v___jp_96_;
}
v___jp_96_:
{
lean_object* v_newNullNode_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_newNullNode_98_ = l_Lean_Syntax_setArgs(v_nullNode_95_, v___y_97_);
v___x_99_ = l_Lean_Syntax_setArg(v_cfg_92_, v___x_94_, v_newNullNode_98_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object* v_cfg_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object* v_cfg_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_111_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object* v_cfg_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* v_stx_125_, lean_object* v_usedSimps_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_stx_132_; lean_object* v___x_133_; 
v_stx_132_ = l_Lean_Syntax_unsetTrailing(v_stx_125_);
v___x_133_ = l_Lean_Elab_Tactic_mkSimpOnly(v_stx_132_, v_usedSimps_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_133_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_133_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* v_stx_150_, lean_object* v_usedSimps_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_150_, v_usedSimps_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec_ref(v_usedSimps_151_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
v___x_159_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* v_00_u03b1_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(v_00_u03b1_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t v___x_188_, lean_object* v_x_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(v___x_188_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object* v___x_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
uint8_t v___x_33986__boxed_204_; lean_object* v_res_205_; 
v___x_33986__boxed_204_ = lean_unbox(v___x_197_);
v_res_205_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33986__boxed_204_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v_x_198_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* v___y_206_, lean_object* v___x_207_, uint8_t v___x_208_, lean_object* v___y_209_, lean_object* v_simprocs_210_, lean_object* v_discharge_x3f_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
if (lean_obj_tag(v___y_206_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_207_);
v___x_222_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_208_);
v___x_223_ = l_Lean_Elab_Tactic_simpLocation(v___y_209_, v_simprocs_210_, v_discharge_x3f_211_, v___x_222_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_val_224_ = lean_ctor_get(v___y_206_, 0);
v___x_225_ = l_Lean_Elab_Tactic_expandLocation(v_val_224_);
v___x_226_ = l_Lean_Elab_Tactic_simpLocation(v___y_209_, v_simprocs_210_, v_discharge_x3f_211_, v___x_225_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* v___y_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v___y_230_, lean_object* v_simprocs_231_, lean_object* v_discharge_x3f_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v___x_34013__boxed_242_; lean_object* v_res_243_; 
v___x_34013__boxed_242_ = lean_unbox(v___x_229_);
v_res_243_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_227_, v___x_228_, v___x_34013__boxed_242_, v___y_230_, v_simprocs_231_, v_discharge_x3f_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_228_);
lean_dec(v___y_227_);
return v_res_243_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Array_mkArray0___redArg();
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object* v___x_254_, lean_object* v_as_x27_255_, lean_object* v_b_256_, lean_object* v___y_257_){
_start:
{
if (lean_obj_tag(v_as_x27_255_) == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_b_256_);
return v___x_259_;
}
else
{
lean_object* v_head_260_; lean_object* v_tail_261_; lean_object* v_ref_262_; uint8_t v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_head_260_ = lean_ctor_get(v_as_x27_255_, 0);
v_tail_261_ = lean_ctor_get(v_as_x27_255_, 1);
v_ref_262_ = lean_ctor_get(v___y_257_, 2);
v___x_263_ = 1;
v___x_264_ = 0;
v___x_265_ = l_Lean_SourceInfo_fromRef(v_ref_262_, v___x_264_);
v___x_266_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_267_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_268_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_265_);
v___x_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_265_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
lean_inc(v_head_260_);
v___x_270_ = l_Lean_mkCIdentFrom(v___x_254_, v_head_260_, v___x_263_);
lean_inc_ref(v___x_269_);
v___x_271_ = l_Lean_Syntax_node3(v___x_265_, v___x_266_, v___x_269_, v___x_269_, v___x_270_);
v___x_272_ = lean_array_push(v_b_256_, v___x_271_);
v_as_x27_255_ = v_tail_261_;
v_b_256_ = v___x_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object* v___x_274_, lean_object* v_as_x27_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_274_, v_as_x27_275_, v_b_276_, v___y_277_);
lean_dec_ref(v___y_277_);
lean_dec(v_as_x27_275_);
lean_dec(v___x_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_head_282_; lean_object* v_tail_283_; lean_object* v_fst_284_; uint8_t v___x_285_; 
v_head_282_ = lean_ctor_get(v_x_280_, 0);
v_tail_283_ = lean_ctor_get(v_x_280_, 1);
v_fst_284_ = lean_ctor_get(v_head_282_, 0);
v___x_285_ = l_Lean_isPrivateName(v_fst_284_);
if (v___x_285_ == 0)
{
v_x_280_ = v_tail_283_;
goto _start;
}
else
{
lean_object* v___x_287_; 
lean_inc(v_head_282_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_head_282_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_288_);
lean_dec(v_x_288_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object* v_opts_290_, lean_object* v_opt_291_){
_start:
{
lean_object* v_name_292_; lean_object* v_defValue_293_; lean_object* v_map_294_; lean_object* v___x_295_; 
v_name_292_ = lean_ctor_get(v_opt_291_, 0);
v_defValue_293_ = lean_ctor_get(v_opt_291_, 1);
v_map_294_ = lean_ctor_get(v_opts_290_, 0);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_294_, v_name_292_);
if (lean_obj_tag(v___x_295_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = lean_unbox(v_defValue_293_);
return v___x_296_;
}
else
{
lean_object* v_val_297_; 
v_val_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_295_, 1);
if (lean_obj_tag(v_val_297_) == 1)
{
uint8_t v_v_298_; 
v_v_298_ = lean_ctor_get_uint8(v_val_297_, 0);
lean_dec_ref_known(v_val_297_, 0);
return v_v_298_;
}
else
{
uint8_t v___x_299_; 
lean_dec(v_val_297_);
v___x_299_ = lean_unbox(v_defValue_293_);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object* v_opts_300_, lean_object* v_opt_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_300_, v_opt_301_);
lean_dec_ref(v_opt_301_);
lean_dec_ref(v_opts_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object* v_opt_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_305_);
v___x_308_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_307_, v_opt_304_);
lean_dec_ref(v___x_307_);
v___x_309_ = lean_box(v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_311_, v___y_312_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v_opt_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v_env_322_; uint8_t v___x_323_; lean_object* v_env_324_; lean_object* v___x_325_; lean_object* v_toCold_326_; lean_object* v_mctx_327_; lean_object* v_lctx_328_; lean_object* v_options_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_321_ = lean_st_ref_get(v___y_319_);
v_env_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_env_322_);
lean_dec(v___x_321_);
v___x_323_ = 0;
v_env_324_ = l_Lean_Environment_setRecordingDeps(v_env_322_, v___x_323_);
v___x_325_ = lean_st_ref_get(v___y_317_);
v_toCold_326_ = lean_ctor_get(v___y_318_, 0);
v_mctx_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_mctx_327_);
lean_dec(v___x_325_);
v_lctx_328_ = lean_ctor_get(v___y_316_, 2);
v_options_329_ = lean_ctor_get(v_toCold_326_, 2);
lean_inc_ref(v_options_329_);
lean_inc_ref(v_lctx_328_);
v___x_330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_330_, 0, v_env_324_);
lean_ctor_set(v___x_330_, 1, v_mctx_327_);
lean_ctor_set(v___x_330_, 2, v_lctx_328_);
lean_ctor_set(v___x_330_, 3, v_options_329_);
v___x_331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_msgData_315_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_348_) == 1)
{
lean_object* v_pre_349_; 
v_pre_349_ = lean_ctor_get(v_x_348_, 0);
switch(lean_obj_tag(v_pre_349_))
{
case 1:
{
lean_object* v_pre_350_; 
v_pre_350_ = lean_ctor_get(v_pre_349_, 0);
switch(lean_obj_tag(v_pre_350_))
{
case 0:
{
lean_object* v_str_351_; lean_object* v_str_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_str_351_ = lean_ctor_get(v_x_348_, 1);
v_str_352_ = lean_ctor_get(v_pre_349_, 1);
v___x_353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_354_ = lean_string_dec_eq(v_str_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_356_ = lean_string_dec_eq(v_str_352_, v___x_355_);
if (v___x_356_ == 0)
{
return v___x_356_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_358_ = lean_string_dec_eq(v_str_351_, v___x_357_);
if (v___x_358_ == 0)
{
return v___x_358_;
}
else
{
return v_suppressElabErrors_347_;
}
}
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_360_ = lean_string_dec_eq(v_str_351_, v___x_359_);
if (v___x_360_ == 0)
{
return v___x_360_;
}
else
{
return v_suppressElabErrors_347_;
}
}
}
case 1:
{
lean_object* v_pre_361_; 
v_pre_361_ = lean_ctor_get(v_pre_350_, 0);
if (lean_obj_tag(v_pre_361_) == 0)
{
lean_object* v_str_362_; lean_object* v_str_363_; lean_object* v_str_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_str_362_ = lean_ctor_get(v_x_348_, 1);
v_str_363_ = lean_ctor_get(v_pre_349_, 1);
v_str_364_ = lean_ctor_get(v_pre_350_, 1);
v___x_365_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_366_ = lean_string_dec_eq(v_str_364_, v___x_365_);
if (v___x_366_ == 0)
{
return v___x_366_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_368_ = lean_string_dec_eq(v_str_363_, v___x_367_);
if (v___x_368_ == 0)
{
return v___x_368_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_370_ = lean_string_dec_eq(v_str_362_, v___x_369_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
return v_suppressElabErrors_347_;
}
}
}
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
}
default: 
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
}
}
case 0:
{
lean_object* v_str_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_str_373_ = lean_ctor_get(v_x_348_, 1);
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_375_ = lean_string_dec_eq(v_str_373_, v___x_374_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
return v_suppressElabErrors_347_;
}
}
default: 
{
uint8_t v___x_376_; 
v___x_376_ = 0;
return v___x_376_;
}
}
}
else
{
uint8_t v___x_377_; 
v___x_377_ = 0;
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_suppressElabErrors_boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v_suppressElabErrors_boxed_380_ = lean_unbox(v_suppressElabErrors_378_);
v_res_381_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_380_, v_x_379_);
lean_dec(v_x_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_384_, lean_object* v_msgData_385_, uint8_t v_severity_386_, uint8_t v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v_toCold_401_; lean_object* v___y_402_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; uint8_t v___y_463_; lean_object* v___y_464_; uint8_t v___y_468_; uint8_t v___y_469_; uint8_t v___x_479_; uint8_t v___y_481_; uint8_t v___x_487_; 
v___x_479_ = 2;
v___x_487_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_479_);
if (v___x_487_ == 0)
{
v___y_481_ = v___x_487_;
goto v___jp_480_;
}
else
{
uint8_t v___x_488_; 
lean_inc_ref(v_msgData_385_);
v___x_488_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_385_);
if (v___x_488_ == 0)
{
v___y_481_ = v___x_488_;
goto v___jp_480_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v_msgData_385_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
v___jp_393_:
{
lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_env_409_; lean_object* v_nextMacroScope_410_; lean_object* v_ngen_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_traceState_413_; lean_object* v_cache_414_; lean_object* v_recordedDeps_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
v_currNamespace_403_ = lean_ctor_get(v_toCold_401_, 4);
v_openDecls_404_ = lean_ctor_get(v_toCold_401_, 5);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_currNamespace_403_);
lean_ctor_set(v___x_405_, 1, v_openDecls_404_);
v___x_406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___y_397_);
lean_inc_ref(v___y_399_);
lean_inc_ref(v___y_396_);
v___x_407_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_407_, 0, v___y_396_);
lean_ctor_set(v___x_407_, 1, v___y_398_);
lean_ctor_set(v___x_407_, 2, v___y_395_);
lean_ctor_set(v___x_407_, 3, v___y_399_);
lean_ctor_set(v___x_407_, 4, v___x_406_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5, v___y_400_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5 + 1, v___y_394_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*5 + 2, v_isSilent_387_);
v___x_408_ = lean_st_ref_take(v___y_402_);
v_env_409_ = lean_ctor_get(v___x_408_, 0);
v_nextMacroScope_410_ = lean_ctor_get(v___x_408_, 1);
v_ngen_411_ = lean_ctor_get(v___x_408_, 2);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_408_, 3);
v_traceState_413_ = lean_ctor_get(v___x_408_, 4);
v_cache_414_ = lean_ctor_get(v___x_408_, 5);
v_recordedDeps_415_ = lean_ctor_get(v___x_408_, 6);
v_messages_416_ = lean_ctor_get(v___x_408_, 7);
v_infoState_417_ = lean_ctor_get(v___x_408_, 8);
v_snapshotTasks_418_ = lean_ctor_get(v___x_408_, 9);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_420_ = v___x_408_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_recordedDeps_415_);
lean_inc(v_cache_414_);
lean_inc(v_traceState_413_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_ngen_411_);
lean_inc(v_nextMacroScope_410_);
lean_inc(v_env_409_);
lean_dec(v___x_408_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_MessageLog_add(v___x_407_, v_messages_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 7, v___x_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_env_409_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_nextMacroScope_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_ngen_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_traceState_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v_recordedDeps_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 9, v_snapshotTasks_418_);
v___x_425_ = v_reuseFailAlloc_428_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_st_ref_put(v___y_402_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_422_);
return v___x_427_;
}
}
}
v___jp_430_:
{
lean_object* v_fileName_439_; lean_object* v_fileMap_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_456_; 
v_fileName_439_ = lean_ctor_get(v___y_435_, 0);
v_fileMap_440_ = lean_ctor_get(v___y_435_, 1);
v___x_441_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_385_);
v___x_442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_441_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_456_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref_n(v_fileMap_440_, 2);
v___x_447_ = l_Lean_FileMap_toPosition(v_fileMap_440_, v___y_433_);
lean_dec(v___y_433_);
v___x_448_ = l_Lean_FileMap_toPosition(v_fileMap_440_, v___y_438_);
lean_dec(v___y_438_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_434_ == 0)
{
lean_del_object(v___x_445_);
lean_dec_ref(v___y_431_);
v___y_394_ = v___y_436_;
v___y_395_ = v___x_449_;
v___y_396_ = v_fileName_439_;
v___y_397_ = v_a_443_;
v___y_398_ = v___x_447_;
v___y_399_ = v___x_450_;
v___y_400_ = v___y_437_;
v_toCold_401_ = v___y_432_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
else
{
uint8_t v___x_451_; 
lean_inc(v_a_443_);
v___x_451_ = l_Lean_MessageData_hasTag(v___y_431_, v_a_443_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec_ref_known(v___x_449_, 1);
lean_dec_ref(v___x_447_);
lean_dec(v_a_443_);
v___x_452_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_452_);
v___x_454_ = v___x_445_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_del_object(v___x_445_);
v___y_394_ = v___y_436_;
v___y_395_ = v___x_449_;
v___y_396_ = v_fileName_439_;
v___y_397_ = v_a_443_;
v___y_398_ = v___x_447_;
v___y_399_ = v___x_450_;
v___y_400_ = v___y_437_;
v_toCold_401_ = v___y_432_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Syntax_getTailPos_x3f(v___y_461_, v___y_463_);
lean_dec(v___y_461_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_inc(v___y_464_);
v___y_431_ = v___y_458_;
v___y_432_ = v___y_460_;
v___y_433_ = v___y_464_;
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_463_;
v___y_438_ = v___y_464_;
goto v___jp_430_;
}
else
{
lean_object* v_val_466_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
v___y_431_ = v___y_458_;
v___y_432_ = v___y_460_;
v___y_433_ = v___y_464_;
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_463_;
v___y_438_ = v_val_466_;
goto v___jp_430_;
}
}
v___jp_467_:
{
lean_object* v_toCold_470_; lean_object* v_ref_471_; uint8_t v_suppressElabErrors_472_; lean_object* v___x_473_; lean_object* v___f_474_; lean_object* v_ref_475_; lean_object* v___x_476_; 
v_toCold_470_ = lean_ctor_get(v___y_390_, 0);
v_ref_471_ = lean_ctor_get(v___y_390_, 2);
v_suppressElabErrors_472_ = lean_ctor_get_uint8(v___y_390_, sizeof(void*)*3 + 2);
v___x_473_ = lean_box(v_suppressElabErrors_472_);
v___f_474_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_474_, 0, v___x_473_);
v_ref_475_ = l_Lean_replaceRef(v_ref_384_, v_ref_471_);
v___x_476_ = l_Lean_Syntax_getPos_x3f(v_ref_475_, v___y_468_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___y_458_ = v___f_474_;
v___y_459_ = v_suppressElabErrors_472_;
v___y_460_ = v_toCold_470_;
v___y_461_ = v_ref_475_;
v___y_462_ = v___y_469_;
v___y_463_ = v___y_468_;
v___y_464_ = v___x_477_;
goto v___jp_457_;
}
else
{
lean_object* v_val_478_; 
v_val_478_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_476_, 1);
v___y_458_ = v___f_474_;
v___y_459_ = v_suppressElabErrors_472_;
v___y_460_ = v_toCold_470_;
v___y_461_ = v_ref_475_;
v___y_462_ = v___y_469_;
v___y_463_ = v___y_468_;
v___y_464_ = v_val_478_;
goto v___jp_457_;
}
}
v___jp_480_:
{
uint8_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 1;
v___x_483_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_482_);
if (v___x_483_ == 0)
{
v___y_468_ = v___y_481_;
v___y_469_ = v_severity_386_;
goto v___jp_467_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_390_);
v___x_485_ = l_Lean_warningAsError;
v___x_486_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_484_, v___x_485_);
lean_dec_ref(v___x_484_);
if (v___x_486_ == 0)
{
v___y_468_ = v___y_481_;
v___y_469_ = v_severity_386_;
goto v___jp_467_;
}
else
{
v___y_468_ = v___y_481_;
v___y_469_ = v___x_479_;
goto v___jp_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_491_, lean_object* v_msgData_492_, lean_object* v_severity_493_, lean_object* v_isSilent_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v_severity_boxed_500_; uint8_t v_isSilent_boxed_501_; lean_object* v_res_502_; 
v_severity_boxed_500_ = lean_unbox(v_severity_493_);
v_isSilent_boxed_501_ = lean_unbox(v_isSilent_494_);
v_res_502_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_491_, v_msgData_492_, v_severity_boxed_500_, v_isSilent_boxed_501_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v_ref_491_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_503_, uint8_t v_severity_504_, uint8_t v_isSilent_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_ref_515_; lean_object* v___x_516_; 
v_ref_515_ = lean_ctor_get(v___y_512_, 2);
v___x_516_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_515_, v_msgData_503_, v_severity_504_, v_isSilent_505_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_517_, lean_object* v_severity_518_, lean_object* v_isSilent_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v_severity_boxed_529_; uint8_t v_isSilent_boxed_530_; lean_object* v_res_531_; 
v_severity_boxed_529_ = lean_unbox(v_severity_518_);
v_isSilent_boxed_530_ = lean_unbox(v_isSilent_519_);
v_res_531_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_517_, v_severity_boxed_529_, v_isSilent_boxed_530_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = 1;
v___x_543_ = 0;
v___x_544_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_532_, v___x_542_, v___x_543_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_555_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_558_ = l_Lean_stringToMessageData(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_env_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_595_; 
v___x_572_ = lean_st_ref_get(v___y_570_);
v_env_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_env_573_);
lean_dec(v___x_572_);
v___x_574_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_575_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_574_, v___y_569_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_595_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_595_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_595_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v_isExporting_585_; 
v_isExporting_585_ = lean_ctor_get_uint8(v_env_573_, sizeof(void*)*13);
lean_dec_ref(v_env_573_);
if (v_isExporting_585_ == 0)
{
lean_dec(v_a_576_);
lean_dec(v_id_562_);
goto v___jp_580_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = l_Lean_isPrivateName(v_id_562_);
if (v___x_586_ == 0)
{
lean_dec(v_a_576_);
lean_dec(v_id_562_);
goto v___jp_580_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = lean_unbox(v_a_576_);
lean_dec(v_a_576_);
if (v___x_587_ == 0)
{
lean_dec(v_id_562_);
goto v___jp_580_;
}
else
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_578_);
v___x_588_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_589_ = 0;
v___x_590_ = l_Lean_MessageData_ofConstName(v_id_562_, v___x_589_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_593_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_594_;
}
}
}
v___jp_580_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_box(0);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_607_, uint8_t v_enableLog_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; lean_object* v_toCold_619_; lean_object* v_env_620_; lean_object* v_currNamespace_621_; lean_object* v_openDecls_622_; lean_object* v___x_623_; lean_object* v_res_624_; lean_object* v___x_625_; 
v___x_618_ = lean_st_ref_get(v___y_616_);
v_toCold_619_ = lean_ctor_get(v___y_615_, 0);
v_env_620_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_618_);
v_currNamespace_621_ = lean_ctor_get(v_toCold_619_, 4);
v_openDecls_622_ = lean_ctor_get(v_toCold_619_, 5);
v___x_623_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_615_);
lean_inc(v_openDecls_622_);
lean_inc(v_currNamespace_621_);
v_res_624_ = l_Lean_ResolveName_resolveGlobalName(v_env_620_, v___x_623_, v_currNamespace_621_, v_openDecls_622_, v_id_607_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_st_ref_get(v___y_616_);
if (v_enableLog_608_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v___x_625_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_res_624_);
return v___x_626_;
}
else
{
lean_object* v_env_627_; uint8_t v_isExporting_628_; 
v_env_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc_ref(v_env_627_);
lean_dec(v___x_625_);
v_isExporting_628_ = lean_ctor_get_uint8(v_env_627_, sizeof(void*)*13);
lean_dec_ref(v_env_627_);
if (v_isExporting_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_res_624_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_624_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; lean_object* v_fst_632_; lean_object* v___x_633_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v_fst_632_ = lean_ctor_get(v_val_631_, 0);
lean_inc(v_fst_632_);
lean_dec(v_val_631_);
v___x_633_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_632_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_641_);
v___x_635_ = v___x_633_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_dec(v___x_633_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_res_624_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_res_624_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_res_624_);
v_a_642_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v___x_630_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_res_624_);
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_651_, lean_object* v_enableLog_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v_enableLog_boxed_662_; lean_object* v_res_663_; 
v_enableLog_boxed_662_ = lean_unbox(v_enableLog_652_);
v_res_663_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_651_, v_enableLog_boxed_662_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
if (lean_obj_tag(v_a_664_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_List_reverse___redArg(v_a_665_);
return v___x_666_;
}
else
{
lean_object* v_head_667_; lean_object* v_tail_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_679_; 
v_head_667_ = lean_ctor_get(v_a_664_, 0);
v_tail_668_ = lean_ctor_get(v_a_664_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_679_ == 0)
{
v___x_670_ = v_a_664_;
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_tail_668_);
lean_inc(v_head_667_);
lean_dec(v_a_664_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_snd_672_; uint8_t v___x_673_; 
v_snd_672_ = lean_ctor_get(v_head_667_, 1);
v___x_673_ = l_List_isEmpty___redArg(v_snd_672_);
if (v___x_673_ == 0)
{
lean_del_object(v___x_670_);
lean_dec(v_head_667_);
v_a_664_ = v_tail_668_;
goto _start;
}
else
{
lean_object* v___x_676_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_a_665_);
v___x_676_ = v___x_670_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_head_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_a_665_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v_a_664_ = v_tail_668_;
v_a_665_ = v___x_676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
if (lean_obj_tag(v_a_680_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = l_List_reverse___redArg(v_a_681_);
return v___x_682_;
}
else
{
lean_object* v_head_683_; lean_object* v_tail_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_head_683_ = lean_ctor_get(v_a_680_, 0);
v_tail_684_ = lean_ctor_get(v_a_680_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_693_ == 0)
{
v___x_686_ = v_a_680_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_tail_684_);
lean_inc(v_head_683_);
lean_dec(v_a_680_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v___x_690_; 
v_fst_688_ = lean_ctor_get(v_head_683_, 0);
lean_inc(v_fst_688_);
lean_dec(v_head_683_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_a_681_);
lean_ctor_set(v___x_686_, 0, v_fst_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_681_);
v___x_690_ = v_reuseFailAlloc_692_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v_a_680_ = v_tail_684_;
v_a_681_ = v___x_690_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_ref_700_; lean_object* v___x_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_ref_700_ = lean_ctor_get(v___y_697_, 2);
v___x_701_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_inc(v_ref_700_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_ref_700_);
lean_ctor_set(v___x_706_, 1, v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 1);
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_toCold_729_; lean_object* v_currRecDepth_730_; lean_object* v_ref_731_; uint16_t v_optionFlags_732_; uint8_t v_suppressElabErrors_733_; uint8_t v_isRecordingDeps_734_; lean_object* v_ref_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_toCold_729_ = lean_ctor_get(v___y_726_, 0);
v_currRecDepth_730_ = lean_ctor_get(v___y_726_, 1);
v_ref_731_ = lean_ctor_get(v___y_726_, 2);
v_optionFlags_732_ = lean_ctor_get_uint16(v___y_726_, sizeof(void*)*3);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*3 + 2);
v_isRecordingDeps_734_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*3 + 3);
v_ref_735_ = l_Lean_replaceRef(v_ref_718_, v_ref_731_);
lean_inc(v_currRecDepth_730_);
lean_inc_ref(v_toCold_729_);
v___x_736_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_736_, 0, v_toCold_729_);
lean_ctor_set(v___x_736_, 1, v_currRecDepth_730_);
lean_ctor_set(v___x_736_, 2, v_ref_735_);
lean_ctor_set_uint16(v___x_736_, sizeof(void*)*3, v_optionFlags_732_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*3 + 2, v_suppressElabErrors_733_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*3 + 3, v_isRecordingDeps_734_);
v___x_737_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_719_, v___y_724_, v___y_725_, v___x_736_, v___y_727_);
lean_dec_ref_known(v___x_736_, 3);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_738_, lean_object* v_msg_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_738_, v_msg_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v_ref_738_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
lean_ctor_set(v___x_756_, 3, v___x_755_);
lean_ctor_set(v___x_756_, 4, v___x_754_);
lean_ctor_set(v___x_756_, 5, v___x_754_);
lean_ctor_set(v___x_756_, 6, v___x_754_);
lean_ctor_set(v___x_756_, 7, v___x_754_);
lean_ctor_set(v___x_756_, 8, v___x_754_);
lean_ctor_set(v___x_756_, 9, v___x_754_);
lean_ctor_set(v___x_756_, 10, v___x_754_);
lean_ctor_set(v___x_756_, 11, v___x_753_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_unsigned_to_nat(32u);
v___x_758_ = lean_mk_empty_array_with_capacity(v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = ((size_t)5ULL);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_unsigned_to_nat(32u);
v___x_763_ = lean_mk_empty_array_with_capacity(v___x_762_);
v___x_764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_765_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
lean_ctor_set(v___x_765_, 2, v___x_761_);
lean_ctor_set(v___x_765_, 3, v___x_761_);
lean_ctor_set_usize(v___x_765_, 4, v___x_760_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_box(1);
v___x_767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
lean_ctor_set(v___x_769_, 2, v___x_766_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_791_, lean_object* v_declHint_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_env_797_; uint8_t v___x_798_; 
v___x_795_ = lean_box(0);
v___x_796_ = lean_st_ref_get(v___y_793_);
v_env_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_env_797_);
lean_dec(v___x_796_);
v___x_798_ = l_Lean_Name_isAnonymous(v_declHint_792_);
if (v___x_798_ == 0)
{
uint8_t v_isExporting_799_; 
v_isExporting_799_ = lean_ctor_get_uint8(v_env_797_, sizeof(void*)*13);
if (v_isExporting_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_msg_791_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; uint8_t v___x_802_; 
lean_inc_ref(v_env_797_);
v___x_801_ = l_Lean_Environment_setExporting(v_env_797_, v___x_798_);
lean_inc(v_declHint_792_);
lean_inc_ref(v___x_801_);
v___x_802_ = l_Lean_Environment_contains(v___x_801_, v_declHint_792_, v_isExporting_799_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v___x_801_);
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_msg_791_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_c_809_; lean_object* v___x_810_; 
v___x_804_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_806_ = l_Lean_Options_empty;
v___x_807_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_807_, 0, v___x_801_);
lean_ctor_set(v___x_807_, 1, v___x_804_);
lean_ctor_set(v___x_807_, 2, v___x_805_);
lean_ctor_set(v___x_807_, 3, v___x_806_);
lean_inc(v_declHint_792_);
v___x_808_ = l_Lean_MessageData_ofConstName(v_declHint_792_, v___x_798_);
v_c_809_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_809_, 0, v___x_807_);
lean_ctor_set(v_c_809_, 1, v___x_808_);
v___x_810_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_797_, v_declHint_792_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_c_809_);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_MessageData_note(v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v_msg_791_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
else
{
lean_object* v_val_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_852_; 
v_val_818_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_852_ == 0)
{
v___x_820_ = v___x_810_;
v_isShared_821_ = v_isSharedCheck_852_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_val_818_);
lean_dec(v___x_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_852_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v_moduleNames_823_; lean_object* v_mod_824_; uint8_t v___x_825_; 
v___x_822_ = l_Lean_Environment_header(v_env_797_);
lean_dec_ref(v_env_797_);
v_moduleNames_823_ = lean_ctor_get(v___x_822_, 4);
lean_inc_ref(v_moduleNames_823_);
lean_dec_ref(v___x_822_);
v_mod_824_ = lean_array_get(v___x_795_, v_moduleNames_823_, v_val_818_);
lean_dec(v_val_818_);
lean_dec_ref(v_moduleNames_823_);
v___x_825_ = l_Lean_isPrivateName(v_declHint_792_);
lean_dec(v_declHint_792_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v_c_809_);
v___x_828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_MessageData_ofName(v_mod_824_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_MessageData_note(v___x_833_);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v_msg_791_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_835_);
v___x_837_ = v___x_820_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_c_809_);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_MessageData_ofName(v_mod_824_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Lean_MessageData_note(v___x_846_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v_msg_791_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_848_);
v___x_850_ = v___x_820_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_853_; 
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_msg_791_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_854_, lean_object* v_declHint_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_854_, v_declHint_855_, v___y_856_);
lean_dec(v___y_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_859_, lean_object* v_declHint_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
v___x_870_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_859_, v_declHint_860_, v___y_868_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = l_Lean_unknownIdentifierMessageTag;
v___x_876_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_881_, lean_object* v_declHint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_881_, v_declHint_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_893_, lean_object* v_msg_894_, lean_object* v_declHint_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_a_906_; lean_object* v___x_907_; 
v___x_905_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_894_, v_declHint_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref(v___x_905_);
v___x_907_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_893_, v_a_906_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_908_, lean_object* v_msg_909_, lean_object* v_declHint_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_908_, v_msg_909_, v_declHint_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v_ref_908_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_927_, lean_object* v_constName_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_938_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_939_ = 0;
lean_inc(v_constName_928_);
v___x_940_ = l_Lean_MessageData_ofConstName(v_constName_928_, v___x_939_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_938_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_927_, v___x_943_, v_constName_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_945_, lean_object* v_constName_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_945_, v_constName_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v_ref_945_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_957_, lean_object* v_cs_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v_cs_969_; uint8_t v___x_973_; 
v___x_968_ = lean_box(0);
v_cs_969_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_958_, v___x_968_);
v___x_973_ = l_List_isEmpty___redArg(v_cs_969_);
if (v___x_973_ == 0)
{
lean_dec(v_n_957_);
goto v___jp_970_;
}
else
{
lean_object* v_ref_974_; lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_cs_969_);
v_ref_974_ = lean_ctor_get(v___y_965_, 2);
v___x_975_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_974_, v_n_957_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
v___jp_970_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_969_, v___x_968_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_984_, lean_object* v_cs_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_984_, v_cs_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = 1;
lean_inc(v_n_996_);
v___x_1007_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_996_, v___x_1006_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_996_, v_a_1008_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_n_996_);
v_a_1010_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1007_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1007_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
if (lean_obj_tag(v_a_1029_) == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_array_to_list(v_a_1030_);
return v___x_1031_;
}
else
{
lean_object* v_head_1032_; 
v_head_1032_ = lean_ctor_get(v_a_1029_, 0);
if (lean_obj_tag(v_head_1032_) == 1)
{
lean_object* v_fields_1033_; 
v_fields_1033_ = lean_ctor_get(v_head_1032_, 1);
if (lean_obj_tag(v_fields_1033_) == 0)
{
lean_object* v_tail_1034_; lean_object* v_n_1035_; lean_object* v___x_1036_; 
lean_inc_ref(v_head_1032_);
v_tail_1034_ = lean_ctor_get(v_a_1029_, 1);
lean_inc(v_tail_1034_);
lean_dec_ref_known(v_a_1029_, 2);
v_n_1035_ = lean_ctor_get(v_head_1032_, 0);
lean_inc(v_n_1035_);
lean_dec_ref_known(v_head_1032_, 2);
v___x_1036_ = lean_array_push(v_a_1030_, v_n_1035_);
v_a_1029_ = v_tail_1034_;
v_a_1030_ = v___x_1036_;
goto _start;
}
else
{
lean_object* v_tail_1038_; 
v_tail_1038_ = lean_ctor_get(v_a_1029_, 1);
lean_inc(v_tail_1038_);
lean_dec_ref_known(v_a_1029_, 2);
v_a_1029_ = v_tail_1038_;
goto _start;
}
}
else
{
lean_object* v_tail_1040_; 
v_tail_1040_ = lean_ctor_get(v_a_1029_, 1);
lean_inc(v_tail_1040_);
lean_dec_ref_known(v_a_1029_, 2);
v_a_1029_ = v_tail_1040_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1048_ = l_Lean_MessageData_ofFormat(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1049_, lean_object* v_k_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
if (lean_obj_tag(v_stx_1049_) == 3)
{
lean_object* v_val_1060_; lean_object* v_preresolved_1061_; lean_object* v___x_1062_; lean_object* v_pre_1063_; uint8_t v___x_1064_; 
v_val_1060_ = lean_ctor_get(v_stx_1049_, 2);
lean_inc(v_val_1060_);
v_preresolved_1061_ = lean_ctor_get(v_stx_1049_, 3);
v___x_1062_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1061_);
v_pre_1063_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1061_, v___x_1062_);
v___x_1064_ = l_List_isEmpty___redArg(v_pre_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec(v_val_1060_);
lean_dec_ref_known(v_stx_1049_, 4);
lean_dec_ref(v_k_1050_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_pre_1063_);
return v___x_1065_;
}
else
{
lean_object* v_toCold_1066_; lean_object* v_currRecDepth_1067_; lean_object* v_ref_1068_; uint16_t v_optionFlags_1069_; uint8_t v_suppressElabErrors_1070_; uint8_t v_isRecordingDeps_1071_; lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_pre_1063_);
v_toCold_1066_ = lean_ctor_get(v___y_1057_, 0);
v_currRecDepth_1067_ = lean_ctor_get(v___y_1057_, 1);
v_ref_1068_ = lean_ctor_get(v___y_1057_, 2);
v_optionFlags_1069_ = lean_ctor_get_uint16(v___y_1057_, sizeof(void*)*3);
v_suppressElabErrors_1070_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1071_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*3 + 3);
v_ref_1072_ = l_Lean_replaceRef(v_stx_1049_, v_ref_1068_);
lean_dec_ref_known(v_stx_1049_, 4);
lean_inc(v_currRecDepth_1067_);
lean_inc_ref(v_toCold_1066_);
v___x_1073_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1073_, 0, v_toCold_1066_);
lean_ctor_set(v___x_1073_, 1, v_currRecDepth_1067_);
lean_ctor_set(v___x_1073_, 2, v_ref_1072_);
lean_ctor_set_uint16(v___x_1073_, sizeof(void*)*3, v_optionFlags_1069_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*3 + 2, v_suppressElabErrors_1070_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*3 + 3, v_isRecordingDeps_1071_);
lean_inc(v___y_1058_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1074_ = lean_apply_10(v_k_1050_, v_val_1060_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___x_1073_, v___y_1058_, lean_box(0));
return v___x_1074_;
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_k_1050_);
v___x_1075_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1076_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1049_, v___x_1075_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v_stx_1049_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1077_, lean_object* v_k_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1077_, v_k_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1101_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1090_, v___x_1100_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1113_, size_t v_sz_1114_, size_t v_i_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_lt(v_i_1115_, v_sz_1114_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_b_1116_);
return v___x_1127_;
}
else
{
lean_object* v_a_1128_; lean_object* v_name_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1128_ = lean_array_uget_borrowed(v_as_1113_, v_i_1115_);
v_name_1129_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_name_1129_);
v___x_1130_ = l_Lean_mkIdent(v_name_1129_);
lean_inc(v___x_1130_);
v___x_1131_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1130_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1130_, v_a_1132_, v_b_1116_, v___y_1123_);
lean_dec(v_a_1132_);
lean_dec(v___x_1130_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; size_t v___x_1135_; size_t v___x_1136_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_add(v_i_1115_, v___x_1135_);
v_i_1115_ = v___x_1136_;
v_b_1116_ = v_a_1134_;
goto _start;
}
else
{
return v___x_1133_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v___x_1130_);
lean_dec_ref(v_b_1116_);
v_a_1138_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1131_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1131_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1146_, lean_object* v_sz_1147_, lean_object* v_i_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1147_);
lean_dec(v_sz_1147_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1148_);
lean_dec(v_i_1148_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1146_, v_sz_boxed_1159_, v_i_boxed_1160_, v_b_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v_as_1146_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1181_, lean_object* v_stx_1182_, uint8_t v___x_1183_, lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v___f_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
if (v___x_1181_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v_tk_1199_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v_stxForSuggestion_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; uint8_t v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; uint8_t v___y_1499_; lean_object* v_stxForExecution_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; uint8_t v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; uint8_t v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; uint8_t v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; lean_object* v_argsArray_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; uint8_t v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; uint8_t v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v_args_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___x_1934_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v_o_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v_bang_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v_tk_1199_ = l_Lean_Syntax_getArg(v_stx_1182_, v___x_1198_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1992_ = l_Lean_Syntax_getArg(v_stx_1182_, v___x_1934_);
v___x_1993_ = l_Lean_Syntax_isNone(v___x_1992_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
lean_inc(v___x_1992_);
v___x_1994_ = l_Lean_Syntax_matchesNull(v___x_1992_, v___x_1934_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec(v___x_1992_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1995_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1995_;
}
else
{
lean_object* v_bang_1996_; lean_object* v___x_1997_; 
v_bang_1996_ = l_Lean_Syntax_getArg(v___x_1992_, v___x_1198_);
lean_dec(v___x_1992_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_bang_1996_);
v_bang_1964_ = v___x_1997_;
v___y_1965_ = v___y_1188_;
v___y_1966_ = v___y_1189_;
v___y_1967_ = v___y_1190_;
v___y_1968_ = v___y_1191_;
v___y_1969_ = v___y_1192_;
v___y_1970_ = v___y_1193_;
v___y_1971_ = v___y_1194_;
v___y_1972_ = v___y_1195_;
goto v___jp_1963_;
}
}
else
{
lean_object* v___x_1998_; 
lean_dec(v___x_1992_);
v___x_1998_ = lean_box(0);
v_bang_1964_ = v___x_1998_;
v___y_1965_ = v___y_1188_;
v___y_1966_ = v___y_1189_;
v___y_1967_ = v___y_1190_;
v___y_1968_ = v___y_1191_;
v___y_1969_ = v___y_1192_;
v___y_1970_ = v___y_1193_;
v___y_1971_ = v___y_1194_;
v___y_1972_ = v___y_1195_;
goto v___jp_1963_;
}
v___jp_1200_:
{
lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_box(v___x_1183_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1215_, 0, v___y_1202_);
lean_closure_set(v___f_1215_, 1, v___x_1198_);
lean_closure_set(v___f_1215_, 2, v___x_1214_);
lean_closure_set(v___f_1215_, 3, v___y_1213_);
lean_closure_set(v___f_1215_, 4, v___y_1203_);
v___x_1216_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1201_, v___f_1215_, v___y_1210_, v___y_1206_, v___y_1211_, v___y_1212_, v___y_1207_, v___y_1205_, v___y_1209_, v___y_1204_);
lean_dec(v___y_1201_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v_usedTheorems_1218_; lean_object* v_diag_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1261_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v_usedTheorems_1218_ = lean_ctor_get(v_a_1217_, 0);
v_diag_1219_ = lean_ctor_get(v_a_1217_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1217_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1221_ = v_a_1217_;
v_isShared_1222_ = v_isSharedCheck_1261_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_diag_1219_);
lean_inc(v_usedTheorems_1218_);
lean_dec(v_a_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1261_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1208_, v_usedTheorems_1218_, v___y_1207_, v___y_1205_, v___y_1209_, v___y_1204_);
lean_dec_ref(v_usedTheorems_1218_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v_ref_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v_ref_1225_ = lean_ctor_get(v___y_1209_, 2);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v_a_1224_);
lean_ctor_set(v___x_1221_, 0, v___x_1226_);
v___x_1228_ = v___x_1221_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_a_1224_);
v___x_1228_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
lean_ctor_set(v___x_1230_, 2, v___x_1229_);
lean_ctor_set(v___x_1230_, 3, v___x_1229_);
lean_ctor_set(v___x_1230_, 4, v___x_1229_);
lean_ctor_set(v___x_1230_, 5, v___x_1229_);
lean_inc(v_ref_1225_);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_ref_1225_);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1233_ = 4;
v___x_1234_ = l_Lean_MessageData_nil;
v___x_1235_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1199_, v___x_1230_, v___x_1231_, v___x_1232_, v___x_1229_, v___x_1233_, v___x_1234_, v___y_1209_, v___y_1204_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1235_, 0);
lean_dec(v_unused_1243_);
v___x_1237_ = v___x_1235_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_dec(v___x_1235_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_diag_1219_);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_diag_1219_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_diag_1219_);
v_a_1244_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1235_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1235_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_del_object(v___x_1221_);
lean_dec_ref(v_diag_1219_);
lean_dec(v_tk_1199_);
v_a_1253_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1223_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1223_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v___y_1208_);
lean_dec(v_tk_1199_);
v_a_1262_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1216_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1216_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
v___jp_1270_:
{
uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = 0;
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1286_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1272_, v___x_1284_, v___y_1274_, v___x_1284_, v___x_1285_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1272_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
if (lean_obj_tag(v___y_1273_) == 0)
{
lean_object* v_ctx_1288_; lean_object* v_simprocs_1289_; lean_object* v_dischargeWrapper_1290_; 
v_ctx_1288_ = lean_ctor_get(v_a_1287_, 0);
lean_inc_ref(v_ctx_1288_);
v_simprocs_1289_ = lean_ctor_get(v_a_1287_, 1);
lean_inc_ref(v_simprocs_1289_);
v_dischargeWrapper_1290_ = lean_ctor_get(v_a_1287_, 2);
lean_inc(v_dischargeWrapper_1290_);
lean_dec(v_a_1287_);
v___y_1201_ = v_dischargeWrapper_1290_;
v___y_1202_ = v___y_1271_;
v___y_1203_ = v_simprocs_1289_;
v___y_1204_ = v___y_1283_;
v___y_1205_ = v___y_1281_;
v___y_1206_ = v___y_1277_;
v___y_1207_ = v___y_1280_;
v___y_1208_ = v_stxForSuggestion_1275_;
v___y_1209_ = v___y_1282_;
v___y_1210_ = v___y_1276_;
v___y_1211_ = v___y_1278_;
v___y_1212_ = v___y_1279_;
v___y_1213_ = v_ctx_1288_;
goto v___jp_1200_;
}
else
{
lean_object* v_ctx_1291_; lean_object* v_simprocs_1292_; lean_object* v_dischargeWrapper_1293_; lean_object* v___x_1294_; 
lean_dec_ref_known(v___y_1273_, 1);
v_ctx_1291_ = lean_ctor_get(v_a_1287_, 0);
lean_inc_ref(v_ctx_1291_);
v_simprocs_1292_ = lean_ctor_get(v_a_1287_, 1);
lean_inc_ref(v_simprocs_1292_);
v_dischargeWrapper_1293_ = lean_ctor_get(v_a_1287_, 2);
lean_inc(v_dischargeWrapper_1293_);
lean_dec(v_a_1287_);
v___x_1294_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1291_);
v___y_1201_ = v_dischargeWrapper_1293_;
v___y_1202_ = v___y_1271_;
v___y_1203_ = v_simprocs_1292_;
v___y_1204_ = v___y_1283_;
v___y_1205_ = v___y_1281_;
v___y_1206_ = v___y_1277_;
v___y_1207_ = v___y_1280_;
v___y_1208_ = v_stxForSuggestion_1275_;
v___y_1209_ = v___y_1282_;
v___y_1210_ = v___y_1276_;
v___y_1211_ = v___y_1278_;
v___y_1212_ = v___y_1279_;
v___y_1213_ = v___x_1294_;
goto v___jp_1200_;
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_stxForSuggestion_1275_);
lean_dec(v___y_1273_);
lean_dec(v___y_1271_);
lean_dec(v_tk_1199_);
v_a_1295_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1286_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1286_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
v___jp_1303_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_inc_ref(v___y_1308_);
v___x_1326_ = l_Array_append___redArg(v___y_1308_, v___y_1325_);
lean_dec_ref(v___y_1325_);
lean_inc(v___y_1319_);
lean_inc(v___y_1311_);
v___x_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___y_1311_);
lean_ctor_set(v___x_1327_, 1, v___y_1319_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
v___x_1328_ = l_Lean_Syntax_node6(v___y_1311_, v___y_1324_, v___y_1309_, v___y_1320_, v___y_1318_, v___y_1316_, v___y_1305_, v___x_1327_);
v___y_1271_ = v___y_1304_;
v___y_1272_ = v___y_1307_;
v___y_1273_ = v___y_1322_;
v___y_1274_ = v___y_1312_;
v_stxForSuggestion_1275_ = v___x_1328_;
v___y_1276_ = v___y_1310_;
v___y_1277_ = v___y_1306_;
v___y_1278_ = v___y_1317_;
v___y_1279_ = v___y_1313_;
v___y_1280_ = v___y_1314_;
v___y_1281_ = v___y_1321_;
v___y_1282_ = v___y_1323_;
v___y_1283_ = v___y_1315_;
goto v___jp_1270_;
}
v___jp_1329_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_inc_ref_n(v___y_1332_, 2);
v___x_1352_ = l_Array_append___redArg(v___y_1332_, v___y_1351_);
lean_dec_ref(v___y_1351_);
lean_inc_n(v___y_1345_, 3);
lean_inc_n(v___y_1337_, 5);
v___x_1353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1353_, 0, v___y_1337_);
lean_ctor_set(v___x_1353_, 1, v___y_1345_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___y_1337_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1357_ = l_Lean_Syntax_SepArray_ofElems(v___x_1356_, v___y_1350_);
lean_dec_ref(v___y_1350_);
v___x_1358_ = l_Array_append___redArg(v___y_1332_, v___x_1357_);
lean_dec_ref(v___x_1357_);
v___x_1359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1359_, 0, v___y_1337_);
lean_ctor_set(v___x_1359_, 1, v___y_1345_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1337_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = l_Lean_Syntax_node3(v___y_1337_, v___y_1345_, v___x_1355_, v___x_1359_, v___x_1361_);
if (lean_obj_tag(v___y_1335_) == 1)
{
lean_object* v_val_1363_; lean_object* v___x_1364_; 
v_val_1363_ = lean_ctor_get(v___y_1335_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v___y_1335_, 1);
v___x_1364_ = l_Array_mkArray1___redArg(v_val_1363_);
v___y_1304_ = v___y_1330_;
v___y_1305_ = v___x_1362_;
v___y_1306_ = v___y_1331_;
v___y_1307_ = v___y_1333_;
v___y_1308_ = v___y_1332_;
v___y_1309_ = v___y_1334_;
v___y_1310_ = v___y_1336_;
v___y_1311_ = v___y_1337_;
v___y_1312_ = v___y_1338_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1340_;
v___y_1315_ = v___y_1341_;
v___y_1316_ = v___x_1353_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1343_;
v___y_1319_ = v___y_1345_;
v___y_1320_ = v___y_1344_;
v___y_1321_ = v___y_1346_;
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1349_;
v___y_1324_ = v___y_1348_;
v___y_1325_ = v___x_1364_;
goto v___jp_1303_;
}
else
{
lean_object* v___x_1365_; 
lean_dec(v___y_1335_);
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1304_ = v___y_1330_;
v___y_1305_ = v___x_1362_;
v___y_1306_ = v___y_1331_;
v___y_1307_ = v___y_1333_;
v___y_1308_ = v___y_1332_;
v___y_1309_ = v___y_1334_;
v___y_1310_ = v___y_1336_;
v___y_1311_ = v___y_1337_;
v___y_1312_ = v___y_1338_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1340_;
v___y_1315_ = v___y_1341_;
v___y_1316_ = v___x_1353_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1343_;
v___y_1319_ = v___y_1345_;
v___y_1320_ = v___y_1344_;
v___y_1321_ = v___y_1346_;
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1349_;
v___y_1324_ = v___y_1348_;
v___y_1325_ = v___x_1365_;
goto v___jp_1303_;
}
}
v___jp_1366_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc_ref(v___y_1369_);
v___x_1389_ = l_Array_append___redArg(v___y_1369_, v___y_1388_);
lean_dec_ref(v___y_1388_);
lean_inc(v___y_1381_);
lean_inc(v___y_1374_);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___y_1374_);
lean_ctor_set(v___x_1390_, 1, v___y_1381_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
if (lean_obj_tag(v___y_1386_) == 1)
{
lean_object* v_val_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_val_1391_ = lean_ctor_get(v___y_1386_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___y_1386_, 1);
v___x_1392_ = l_Lean_SourceInfo_fromRef(v_val_1391_, v___x_1183_);
lean_dec(v_val_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = l_Array_mkArray1___redArg(v___x_1394_);
v___y_1330_ = v___y_1367_;
v___y_1331_ = v___y_1368_;
v___y_1332_ = v___y_1369_;
v___y_1333_ = v___y_1370_;
v___y_1334_ = v___y_1371_;
v___y_1335_ = v___y_1372_;
v___y_1336_ = v___y_1373_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___y_1375_;
v___y_1339_ = v___y_1376_;
v___y_1340_ = v___y_1377_;
v___y_1341_ = v___y_1378_;
v___y_1342_ = v___y_1379_;
v___y_1343_ = v___x_1390_;
v___y_1344_ = v___y_1380_;
v___y_1345_ = v___y_1381_;
v___y_1346_ = v___y_1382_;
v___y_1347_ = v___y_1383_;
v___y_1348_ = v___y_1385_;
v___y_1349_ = v___y_1384_;
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___x_1395_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1396_; 
lean_dec(v___y_1386_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1330_ = v___y_1367_;
v___y_1331_ = v___y_1368_;
v___y_1332_ = v___y_1369_;
v___y_1333_ = v___y_1370_;
v___y_1334_ = v___y_1371_;
v___y_1335_ = v___y_1372_;
v___y_1336_ = v___y_1373_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___y_1375_;
v___y_1339_ = v___y_1376_;
v___y_1340_ = v___y_1377_;
v___y_1341_ = v___y_1378_;
v___y_1342_ = v___y_1379_;
v___y_1343_ = v___x_1390_;
v___y_1344_ = v___y_1380_;
v___y_1345_ = v___y_1381_;
v___y_1346_ = v___y_1382_;
v___y_1347_ = v___y_1383_;
v___y_1348_ = v___y_1385_;
v___y_1349_ = v___y_1384_;
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___x_1396_;
goto v___jp_1329_;
}
}
v___jp_1397_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_inc_ref(v___y_1410_);
v___x_1420_ = l_Array_append___redArg(v___y_1410_, v___y_1419_);
lean_dec_ref(v___y_1419_);
lean_inc(v___y_1406_);
lean_inc(v___y_1399_);
v___x_1421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1421_, 0, v___y_1399_);
lean_ctor_set(v___x_1421_, 1, v___y_1406_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
v___x_1422_ = l_Lean_Syntax_node6(v___y_1399_, v___y_1403_, v___y_1414_, v___y_1415_, v___y_1405_, v___y_1413_, v___y_1400_, v___x_1421_);
v___y_1271_ = v___y_1398_;
v___y_1272_ = v___y_1402_;
v___y_1273_ = v___y_1417_;
v___y_1274_ = v___y_1407_;
v_stxForSuggestion_1275_ = v___x_1422_;
v___y_1276_ = v___y_1404_;
v___y_1277_ = v___y_1401_;
v___y_1278_ = v___y_1412_;
v___y_1279_ = v___y_1408_;
v___y_1280_ = v___y_1409_;
v___y_1281_ = v___y_1416_;
v___y_1282_ = v___y_1418_;
v___y_1283_ = v___y_1411_;
goto v___jp_1270_;
}
v___jp_1423_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_inc_ref_n(v___y_1436_, 2);
v___x_1446_ = l_Array_append___redArg(v___y_1436_, v___y_1445_);
lean_dec_ref(v___y_1445_);
lean_inc_n(v___y_1432_, 3);
lean_inc_n(v___y_1425_, 5);
v___x_1447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1425_);
lean_ctor_set(v___x_1447_, 1, v___y_1432_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1425_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1451_ = l_Lean_Syntax_SepArray_ofElems(v___x_1450_, v___y_1444_);
lean_dec_ref(v___y_1444_);
v___x_1452_ = l_Array_append___redArg(v___y_1436_, v___x_1451_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1425_);
lean_ctor_set(v___x_1453_, 1, v___y_1432_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1425_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_Syntax_node3(v___y_1425_, v___y_1432_, v___x_1449_, v___x_1453_, v___x_1455_);
if (lean_obj_tag(v___y_1429_) == 1)
{
lean_object* v_val_1457_; lean_object* v___x_1458_; 
v_val_1457_ = lean_ctor_get(v___y_1429_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v___y_1429_, 1);
v___x_1458_ = l_Array_mkArray1___redArg(v_val_1457_);
v___y_1398_ = v___y_1424_;
v___y_1399_ = v___y_1425_;
v___y_1400_ = v___x_1456_;
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1430_;
v___y_1405_ = v___y_1431_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___y_1435_;
v___y_1410_ = v___y_1436_;
v___y_1411_ = v___y_1437_;
v___y_1412_ = v___y_1438_;
v___y_1413_ = v___x_1447_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1439_;
v___y_1416_ = v___y_1441_;
v___y_1417_ = v___y_1442_;
v___y_1418_ = v___y_1443_;
v___y_1419_ = v___x_1458_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1459_; 
lean_dec(v___y_1429_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1398_ = v___y_1424_;
v___y_1399_ = v___y_1425_;
v___y_1400_ = v___x_1456_;
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1430_;
v___y_1405_ = v___y_1431_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___y_1435_;
v___y_1410_ = v___y_1436_;
v___y_1411_ = v___y_1437_;
v___y_1412_ = v___y_1438_;
v___y_1413_ = v___x_1447_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1439_;
v___y_1416_ = v___y_1441_;
v___y_1417_ = v___y_1442_;
v___y_1418_ = v___y_1443_;
v___y_1419_ = v___x_1459_;
goto v___jp_1397_;
}
}
v___jp_1460_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_inc_ref(v___y_1472_);
v___x_1483_ = l_Array_append___redArg(v___y_1472_, v___y_1482_);
lean_dec_ref(v___y_1482_);
lean_inc(v___y_1468_);
lean_inc(v___y_1462_);
v___x_1484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1462_);
lean_ctor_set(v___x_1484_, 1, v___y_1468_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
if (lean_obj_tag(v___y_1480_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_val_1485_ = lean_ctor_get(v___y_1480_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v___y_1480_, 1);
v___x_1486_ = l_Lean_SourceInfo_fromRef(v_val_1485_, v___x_1183_);
lean_dec(v_val_1485_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Array_mkArray1___redArg(v___x_1488_);
v___y_1424_ = v___y_1461_;
v___y_1425_ = v___y_1462_;
v___y_1426_ = v___y_1463_;
v___y_1427_ = v___y_1464_;
v___y_1428_ = v___y_1465_;
v___y_1429_ = v___y_1466_;
v___y_1430_ = v___y_1467_;
v___y_1431_ = v___x_1484_;
v___y_1432_ = v___y_1468_;
v___y_1433_ = v___y_1469_;
v___y_1434_ = v___y_1470_;
v___y_1435_ = v___y_1471_;
v___y_1436_ = v___y_1472_;
v___y_1437_ = v___y_1473_;
v___y_1438_ = v___y_1474_;
v___y_1439_ = v___y_1476_;
v___y_1440_ = v___y_1475_;
v___y_1441_ = v___y_1477_;
v___y_1442_ = v___y_1478_;
v___y_1443_ = v___y_1479_;
v___y_1444_ = v___y_1481_;
v___y_1445_ = v___x_1489_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___y_1480_);
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1424_ = v___y_1461_;
v___y_1425_ = v___y_1462_;
v___y_1426_ = v___y_1463_;
v___y_1427_ = v___y_1464_;
v___y_1428_ = v___y_1465_;
v___y_1429_ = v___y_1466_;
v___y_1430_ = v___y_1467_;
v___y_1431_ = v___x_1484_;
v___y_1432_ = v___y_1468_;
v___y_1433_ = v___y_1469_;
v___y_1434_ = v___y_1470_;
v___y_1435_ = v___y_1471_;
v___y_1436_ = v___y_1472_;
v___y_1437_ = v___y_1473_;
v___y_1438_ = v___y_1474_;
v___y_1439_ = v___y_1476_;
v___y_1440_ = v___y_1475_;
v___y_1441_ = v___y_1477_;
v___y_1442_ = v___y_1478_;
v___y_1443_ = v___y_1479_;
v___y_1444_ = v___y_1481_;
v___y_1445_ = v___x_1490_;
goto v___jp_1423_;
}
}
v___jp_1491_:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1495_);
if (lean_obj_tag(v___y_1496_) == 0)
{
lean_object* v_a_1510_; lean_object* v_ref_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
v_ref_1511_ = lean_ctor_get(v___y_1507_, 2);
v___x_1512_ = 0;
v___x_1513_ = l_Lean_SourceInfo_fromRef(v_ref_1511_, v___x_1512_);
v___x_1514_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1515_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1514_);
v___x_1516_ = l_Lean_SourceInfo_fromRef(v_tk_1199_, v___x_1183_);
v___x_1517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1514_);
v___x_1518_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1519_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1494_) == 1)
{
lean_object* v_val_1520_; lean_object* v___x_1521_; 
v_val_1520_ = lean_ctor_get(v___y_1494_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___y_1494_, 1);
v___x_1521_ = l_Array_mkArray1___redArg(v_val_1520_);
v___y_1461_ = v___y_1492_;
v___y_1462_ = v___x_1513_;
v___y_1463_ = v___y_1502_;
v___y_1464_ = v_stxForExecution_1500_;
v___y_1465_ = v___x_1515_;
v___y_1466_ = v___y_1493_;
v___y_1467_ = v___y_1501_;
v___y_1468_ = v___x_1518_;
v___y_1469_ = v___y_1499_;
v___y_1470_ = v___y_1504_;
v___y_1471_ = v___y_1505_;
v___y_1472_ = v___x_1519_;
v___y_1473_ = v___y_1508_;
v___y_1474_ = v___y_1503_;
v___y_1475_ = v___x_1517_;
v___y_1476_ = v_a_1510_;
v___y_1477_ = v___y_1506_;
v___y_1478_ = v___y_1496_;
v___y_1479_ = v___y_1507_;
v___y_1480_ = v___y_1498_;
v___y_1481_ = v___y_1497_;
v___y_1482_ = v___x_1521_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v___y_1494_);
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1461_ = v___y_1492_;
v___y_1462_ = v___x_1513_;
v___y_1463_ = v___y_1502_;
v___y_1464_ = v_stxForExecution_1500_;
v___y_1465_ = v___x_1515_;
v___y_1466_ = v___y_1493_;
v___y_1467_ = v___y_1501_;
v___y_1468_ = v___x_1518_;
v___y_1469_ = v___y_1499_;
v___y_1470_ = v___y_1504_;
v___y_1471_ = v___y_1505_;
v___y_1472_ = v___x_1519_;
v___y_1473_ = v___y_1508_;
v___y_1474_ = v___y_1503_;
v___y_1475_ = v___x_1517_;
v___y_1476_ = v_a_1510_;
v___y_1477_ = v___y_1506_;
v___y_1478_ = v___y_1496_;
v___y_1479_ = v___y_1507_;
v___y_1480_ = v___y_1498_;
v___y_1481_ = v___y_1497_;
v___y_1482_ = v___x_1522_;
goto v___jp_1460_;
}
}
else
{
lean_object* v_a_1523_; lean_object* v_ref_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1523_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1509_);
v_ref_1524_ = lean_ctor_get(v___y_1507_, 2);
v___x_1525_ = 0;
v___x_1526_ = l_Lean_SourceInfo_fromRef(v_ref_1524_, v___x_1525_);
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1528_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1527_);
v___x_1529_ = l_Lean_SourceInfo_fromRef(v_tk_1199_, v___x_1183_);
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1533_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1494_) == 1)
{
lean_object* v_val_1534_; lean_object* v___x_1535_; 
v_val_1534_ = lean_ctor_get(v___y_1494_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___y_1494_, 1);
v___x_1535_ = l_Array_mkArray1___redArg(v_val_1534_);
v___y_1367_ = v___y_1492_;
v___y_1368_ = v___y_1502_;
v___y_1369_ = v___x_1533_;
v___y_1370_ = v_stxForExecution_1500_;
v___y_1371_ = v___x_1531_;
v___y_1372_ = v___y_1493_;
v___y_1373_ = v___y_1501_;
v___y_1374_ = v___x_1526_;
v___y_1375_ = v___y_1499_;
v___y_1376_ = v___y_1504_;
v___y_1377_ = v___y_1505_;
v___y_1378_ = v___y_1508_;
v___y_1379_ = v___y_1503_;
v___y_1380_ = v_a_1523_;
v___y_1381_ = v___x_1532_;
v___y_1382_ = v___y_1506_;
v___y_1383_ = v___y_1496_;
v___y_1384_ = v___y_1507_;
v___y_1385_ = v___x_1528_;
v___y_1386_ = v___y_1498_;
v___y_1387_ = v___y_1497_;
v___y_1388_ = v___x_1535_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1536_; 
lean_dec(v___y_1494_);
v___x_1536_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1367_ = v___y_1492_;
v___y_1368_ = v___y_1502_;
v___y_1369_ = v___x_1533_;
v___y_1370_ = v_stxForExecution_1500_;
v___y_1371_ = v___x_1531_;
v___y_1372_ = v___y_1493_;
v___y_1373_ = v___y_1501_;
v___y_1374_ = v___x_1526_;
v___y_1375_ = v___y_1499_;
v___y_1376_ = v___y_1504_;
v___y_1377_ = v___y_1505_;
v___y_1378_ = v___y_1508_;
v___y_1379_ = v___y_1503_;
v___y_1380_ = v_a_1523_;
v___y_1381_ = v___x_1532_;
v___y_1382_ = v___y_1506_;
v___y_1383_ = v___y_1496_;
v___y_1384_ = v___y_1507_;
v___y_1385_ = v___x_1528_;
v___y_1386_ = v___y_1498_;
v___y_1387_ = v___y_1497_;
v___y_1388_ = v___x_1536_;
goto v___jp_1366_;
}
}
}
v___jp_1537_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_inc_ref(v___y_1556_);
v___x_1563_ = l_Array_append___redArg(v___y_1556_, v___y_1562_);
lean_dec_ref(v___y_1562_);
lean_inc(v___y_1553_);
lean_inc(v___y_1555_);
v___x_1564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1564_, 0, v___y_1555_);
lean_ctor_set(v___x_1564_, 1, v___y_1553_);
lean_ctor_set(v___x_1564_, 2, v___x_1563_);
lean_inc(v___y_1554_);
v___x_1565_ = l_Lean_Syntax_node6(v___y_1555_, v___y_1540_, v___y_1557_, v___y_1554_, v___y_1545_, v___y_1550_, v___y_1559_, v___x_1564_);
v___y_1492_ = v___y_1538_;
v___y_1493_ = v___y_1541_;
v___y_1494_ = v___y_1552_;
v___y_1495_ = v___y_1554_;
v___y_1496_ = v___y_1558_;
v___y_1497_ = v___y_1561_;
v___y_1498_ = v___y_1560_;
v___y_1499_ = v___y_1549_;
v_stxForExecution_1500_ = v___x_1565_;
v___y_1501_ = v___y_1539_;
v___y_1502_ = v___y_1548_;
v___y_1503_ = v___y_1543_;
v___y_1504_ = v___y_1551_;
v___y_1505_ = v___y_1547_;
v___y_1506_ = v___y_1546_;
v___y_1507_ = v___y_1542_;
v___y_1508_ = v___y_1544_;
goto v___jp_1491_;
}
v___jp_1566_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_inc_ref_n(v___y_1585_, 2);
v___x_1590_ = l_Array_append___redArg(v___y_1585_, v___y_1589_);
lean_dec_ref(v___y_1589_);
lean_inc_n(v___y_1581_, 3);
lean_inc_n(v___y_1583_, 5);
v___x_1591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1591_, 0, v___y_1583_);
lean_ctor_set(v___x_1591_, 1, v___y_1581_);
lean_ctor_set(v___x_1591_, 2, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___y_1583_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1595_ = l_Lean_Syntax_SepArray_ofElems(v___x_1594_, v___y_1588_);
v___x_1596_ = l_Array_append___redArg(v___y_1585_, v___x_1595_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___y_1583_);
lean_ctor_set(v___x_1597_, 1, v___y_1581_);
lean_ctor_set(v___x_1597_, 2, v___x_1596_);
v___x_1598_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1583_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = l_Lean_Syntax_node3(v___y_1583_, v___y_1581_, v___x_1593_, v___x_1597_, v___x_1599_);
if (lean_obj_tag(v___y_1570_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1602_; 
v_val_1601_ = lean_ctor_get(v___y_1570_, 0);
lean_inc(v_val_1601_);
v___x_1602_ = l_Array_mkArray1___redArg(v_val_1601_);
v___y_1538_ = v___y_1567_;
v___y_1539_ = v___y_1568_;
v___y_1540_ = v___y_1569_;
v___y_1541_ = v___y_1570_;
v___y_1542_ = v___y_1571_;
v___y_1543_ = v___y_1572_;
v___y_1544_ = v___y_1573_;
v___y_1545_ = v___y_1574_;
v___y_1546_ = v___y_1575_;
v___y_1547_ = v___y_1576_;
v___y_1548_ = v___y_1577_;
v___y_1549_ = v___y_1578_;
v___y_1550_ = v___x_1591_;
v___y_1551_ = v___y_1579_;
v___y_1552_ = v___y_1580_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1582_;
v___y_1555_ = v___y_1583_;
v___y_1556_ = v___y_1585_;
v___y_1557_ = v___y_1584_;
v___y_1558_ = v___y_1586_;
v___y_1559_ = v___x_1600_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v___y_1588_;
v___y_1562_ = v___x_1602_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1538_ = v___y_1567_;
v___y_1539_ = v___y_1568_;
v___y_1540_ = v___y_1569_;
v___y_1541_ = v___y_1570_;
v___y_1542_ = v___y_1571_;
v___y_1543_ = v___y_1572_;
v___y_1544_ = v___y_1573_;
v___y_1545_ = v___y_1574_;
v___y_1546_ = v___y_1575_;
v___y_1547_ = v___y_1576_;
v___y_1548_ = v___y_1577_;
v___y_1549_ = v___y_1578_;
v___y_1550_ = v___x_1591_;
v___y_1551_ = v___y_1579_;
v___y_1552_ = v___y_1580_;
v___y_1553_ = v___y_1581_;
v___y_1554_ = v___y_1582_;
v___y_1555_ = v___y_1583_;
v___y_1556_ = v___y_1585_;
v___y_1557_ = v___y_1584_;
v___y_1558_ = v___y_1586_;
v___y_1559_ = v___x_1600_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v___y_1588_;
v___y_1562_ = v___x_1603_;
goto v___jp_1537_;
}
}
v___jp_1604_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_inc_ref(v___y_1622_);
v___x_1627_ = l_Array_append___redArg(v___y_1622_, v___y_1626_);
lean_dec_ref(v___y_1626_);
lean_inc(v___y_1618_);
lean_inc(v___y_1620_);
v___x_1628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1620_);
lean_ctor_set(v___x_1628_, 1, v___y_1618_);
lean_ctor_set(v___x_1628_, 2, v___x_1627_);
if (lean_obj_tag(v___y_1625_) == 1)
{
lean_object* v_val_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_val_1629_ = lean_ctor_get(v___y_1625_, 0);
v___x_1630_ = l_Lean_SourceInfo_fromRef(v_val_1629_, v___x_1183_);
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Array_mkArray1___redArg(v___x_1632_);
v___y_1567_ = v___y_1605_;
v___y_1568_ = v___y_1606_;
v___y_1569_ = v___y_1607_;
v___y_1570_ = v___y_1608_;
v___y_1571_ = v___y_1609_;
v___y_1572_ = v___y_1610_;
v___y_1573_ = v___y_1611_;
v___y_1574_ = v___x_1628_;
v___y_1575_ = v___y_1612_;
v___y_1576_ = v___y_1613_;
v___y_1577_ = v___y_1614_;
v___y_1578_ = v___y_1615_;
v___y_1579_ = v___y_1616_;
v___y_1580_ = v___y_1617_;
v___y_1581_ = v___y_1618_;
v___y_1582_ = v___y_1619_;
v___y_1583_ = v___y_1620_;
v___y_1584_ = v___y_1621_;
v___y_1585_ = v___y_1622_;
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___y_1624_;
v___y_1589_ = v___x_1633_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1567_ = v___y_1605_;
v___y_1568_ = v___y_1606_;
v___y_1569_ = v___y_1607_;
v___y_1570_ = v___y_1608_;
v___y_1571_ = v___y_1609_;
v___y_1572_ = v___y_1610_;
v___y_1573_ = v___y_1611_;
v___y_1574_ = v___x_1628_;
v___y_1575_ = v___y_1612_;
v___y_1576_ = v___y_1613_;
v___y_1577_ = v___y_1614_;
v___y_1578_ = v___y_1615_;
v___y_1579_ = v___y_1616_;
v___y_1580_ = v___y_1617_;
v___y_1581_ = v___y_1618_;
v___y_1582_ = v___y_1619_;
v___y_1583_ = v___y_1620_;
v___y_1584_ = v___y_1621_;
v___y_1585_ = v___y_1622_;
v___y_1586_ = v___y_1623_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___y_1624_;
v___y_1589_ = v___x_1634_;
goto v___jp_1566_;
}
}
v___jp_1635_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_inc_ref(v___y_1645_);
v___x_1661_ = l_Array_append___redArg(v___y_1645_, v___y_1660_);
lean_dec_ref(v___y_1660_);
lean_inc(v___y_1656_);
lean_inc(v___y_1654_);
v___x_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___y_1654_);
lean_ctor_set(v___x_1662_, 1, v___y_1656_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
lean_inc(v___y_1655_);
v___x_1663_ = l_Lean_Syntax_node6(v___y_1654_, v___y_1638_, v___y_1652_, v___y_1655_, v___y_1639_, v___y_1648_, v___y_1643_, v___x_1662_);
v___y_1492_ = v___y_1636_;
v___y_1493_ = v___y_1640_;
v___y_1494_ = v___y_1653_;
v___y_1495_ = v___y_1655_;
v___y_1496_ = v___y_1657_;
v___y_1497_ = v___y_1659_;
v___y_1498_ = v___y_1658_;
v___y_1499_ = v___y_1650_;
v_stxForExecution_1500_ = v___x_1663_;
v___y_1501_ = v___y_1637_;
v___y_1502_ = v___y_1649_;
v___y_1503_ = v___y_1642_;
v___y_1504_ = v___y_1651_;
v___y_1505_ = v___y_1647_;
v___y_1506_ = v___y_1646_;
v___y_1507_ = v___y_1641_;
v___y_1508_ = v___y_1644_;
goto v___jp_1491_;
}
v___jp_1664_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_inc_ref_n(v___y_1673_, 2);
v___x_1688_ = l_Array_append___redArg(v___y_1673_, v___y_1687_);
lean_dec_ref(v___y_1687_);
lean_inc_n(v___y_1683_, 3);
lean_inc_n(v___y_1681_, 5);
v___x_1689_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1689_, 0, v___y_1681_);
lean_ctor_set(v___x_1689_, 1, v___y_1683_);
lean_ctor_set(v___x_1689_, 2, v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1681_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1693_ = l_Lean_Syntax_SepArray_ofElems(v___x_1692_, v___y_1686_);
v___x_1694_ = l_Array_append___redArg(v___y_1673_, v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1681_);
lean_ctor_set(v___x_1695_, 1, v___y_1683_);
lean_ctor_set(v___x_1695_, 2, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1681_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = l_Lean_Syntax_node3(v___y_1681_, v___y_1683_, v___x_1691_, v___x_1695_, v___x_1697_);
if (lean_obj_tag(v___y_1669_) == 1)
{
lean_object* v_val_1699_; lean_object* v___x_1700_; 
v_val_1699_ = lean_ctor_get(v___y_1669_, 0);
lean_inc(v_val_1699_);
v___x_1700_ = l_Array_mkArray1___redArg(v_val_1699_);
v___y_1636_ = v___y_1665_;
v___y_1637_ = v___y_1666_;
v___y_1638_ = v___y_1667_;
v___y_1639_ = v___y_1668_;
v___y_1640_ = v___y_1669_;
v___y_1641_ = v___y_1670_;
v___y_1642_ = v___y_1671_;
v___y_1643_ = v___x_1698_;
v___y_1644_ = v___y_1672_;
v___y_1645_ = v___y_1673_;
v___y_1646_ = v___y_1674_;
v___y_1647_ = v___y_1675_;
v___y_1648_ = v___x_1689_;
v___y_1649_ = v___y_1676_;
v___y_1650_ = v___y_1677_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v___y_1682_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1685_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___x_1700_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1636_ = v___y_1665_;
v___y_1637_ = v___y_1666_;
v___y_1638_ = v___y_1667_;
v___y_1639_ = v___y_1668_;
v___y_1640_ = v___y_1669_;
v___y_1641_ = v___y_1670_;
v___y_1642_ = v___y_1671_;
v___y_1643_ = v___x_1698_;
v___y_1644_ = v___y_1672_;
v___y_1645_ = v___y_1673_;
v___y_1646_ = v___y_1674_;
v___y_1647_ = v___y_1675_;
v___y_1648_ = v___x_1689_;
v___y_1649_ = v___y_1676_;
v___y_1650_ = v___y_1677_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v___y_1682_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1685_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___x_1701_;
goto v___jp_1635_;
}
}
v___jp_1702_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_inc_ref(v___y_1710_);
v___x_1725_ = l_Array_append___redArg(v___y_1710_, v___y_1724_);
lean_dec_ref(v___y_1724_);
lean_inc(v___y_1720_);
lean_inc(v___y_1718_);
v___x_1726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1718_);
lean_ctor_set(v___x_1726_, 1, v___y_1720_);
lean_ctor_set(v___x_1726_, 2, v___x_1725_);
if (lean_obj_tag(v___y_1723_) == 1)
{
lean_object* v_val_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_val_1727_ = lean_ctor_get(v___y_1723_, 0);
v___x_1728_ = l_Lean_SourceInfo_fromRef(v_val_1727_, v___x_1183_);
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Array_mkArray1___redArg(v___x_1730_);
v___y_1665_ = v___y_1703_;
v___y_1666_ = v___y_1704_;
v___y_1667_ = v___y_1705_;
v___y_1668_ = v___x_1726_;
v___y_1669_ = v___y_1706_;
v___y_1670_ = v___y_1707_;
v___y_1671_ = v___y_1708_;
v___y_1672_ = v___y_1709_;
v___y_1673_ = v___y_1710_;
v___y_1674_ = v___y_1711_;
v___y_1675_ = v___y_1712_;
v___y_1676_ = v___y_1713_;
v___y_1677_ = v___y_1714_;
v___y_1678_ = v___y_1715_;
v___y_1679_ = v___y_1716_;
v___y_1680_ = v___y_1717_;
v___y_1681_ = v___y_1718_;
v___y_1682_ = v___y_1719_;
v___y_1683_ = v___y_1720_;
v___y_1684_ = v___y_1721_;
v___y_1685_ = v___y_1723_;
v___y_1686_ = v___y_1722_;
v___y_1687_ = v___x_1731_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1665_ = v___y_1703_;
v___y_1666_ = v___y_1704_;
v___y_1667_ = v___y_1705_;
v___y_1668_ = v___x_1726_;
v___y_1669_ = v___y_1706_;
v___y_1670_ = v___y_1707_;
v___y_1671_ = v___y_1708_;
v___y_1672_ = v___y_1709_;
v___y_1673_ = v___y_1710_;
v___y_1674_ = v___y_1711_;
v___y_1675_ = v___y_1712_;
v___y_1676_ = v___y_1713_;
v___y_1677_ = v___y_1714_;
v___y_1678_ = v___y_1715_;
v___y_1679_ = v___y_1716_;
v___y_1680_ = v___y_1717_;
v___y_1681_ = v___y_1718_;
v___y_1682_ = v___y_1719_;
v___y_1683_ = v___y_1720_;
v___y_1684_ = v___y_1721_;
v___y_1685_ = v___y_1723_;
v___y_1686_ = v___y_1722_;
v___y_1687_ = v___x_1732_;
goto v___jp_1664_;
}
}
v___jp_1733_:
{
if (lean_obj_tag(v___y_1738_) == 0)
{
lean_object* v_ref_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_ref_1750_ = lean_ctor_get(v___y_1748_, 2);
v___x_1751_ = 0;
v___x_1752_ = l_Lean_SourceInfo_fromRef(v_ref_1750_, v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1186_);
lean_inc_ref(v___x_1185_);
lean_inc_ref(v___x_1184_);
v___x_1754_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1753_);
v___x_1755_ = l_Lean_SourceInfo_fromRef(v_tk_1199_, v___x_1183_);
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1753_);
v___x_1757_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1758_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1736_) == 1)
{
lean_object* v_val_1759_; lean_object* v___x_1760_; 
v_val_1759_ = lean_ctor_get(v___y_1736_, 0);
lean_inc(v_val_1759_);
v___x_1760_ = l_Array_mkArray1___redArg(v_val_1759_);
v___y_1703_ = v___y_1734_;
v___y_1704_ = v___y_1742_;
v___y_1705_ = v___x_1754_;
v___y_1706_ = v___y_1735_;
v___y_1707_ = v___y_1748_;
v___y_1708_ = v___y_1744_;
v___y_1709_ = v___y_1749_;
v___y_1710_ = v___x_1758_;
v___y_1711_ = v___y_1747_;
v___y_1712_ = v___y_1746_;
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1740_;
v___y_1715_ = v___y_1745_;
v___y_1716_ = v___x_1756_;
v___y_1717_ = v___y_1736_;
v___y_1718_ = v___x_1752_;
v___y_1719_ = v___y_1737_;
v___y_1720_ = v___x_1757_;
v___y_1721_ = v___y_1738_;
v___y_1722_ = v_argsArray_1741_;
v___y_1723_ = v___y_1739_;
v___y_1724_ = v___x_1760_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1703_ = v___y_1734_;
v___y_1704_ = v___y_1742_;
v___y_1705_ = v___x_1754_;
v___y_1706_ = v___y_1735_;
v___y_1707_ = v___y_1748_;
v___y_1708_ = v___y_1744_;
v___y_1709_ = v___y_1749_;
v___y_1710_ = v___x_1758_;
v___y_1711_ = v___y_1747_;
v___y_1712_ = v___y_1746_;
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1740_;
v___y_1715_ = v___y_1745_;
v___y_1716_ = v___x_1756_;
v___y_1717_ = v___y_1736_;
v___y_1718_ = v___x_1752_;
v___y_1719_ = v___y_1737_;
v___y_1720_ = v___x_1757_;
v___y_1721_ = v___y_1738_;
v___y_1722_ = v_argsArray_1741_;
v___y_1723_ = v___y_1739_;
v___y_1724_ = v___x_1761_;
goto v___jp_1702_;
}
}
else
{
lean_object* v_ref_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_ref_1762_ = lean_ctor_get(v___y_1748_, 2);
v___x_1763_ = 0;
v___x_1764_ = l_Lean_SourceInfo_fromRef(v_ref_1762_, v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1186_);
lean_inc_ref(v___x_1185_);
lean_inc_ref(v___x_1184_);
v___x_1766_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1765_);
v___x_1767_ = l_Lean_SourceInfo_fromRef(v_tk_1199_, v___x_1183_);
v___x_1768_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1771_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1736_) == 1)
{
lean_object* v_val_1772_; lean_object* v___x_1773_; 
v_val_1772_ = lean_ctor_get(v___y_1736_, 0);
lean_inc(v_val_1772_);
v___x_1773_ = l_Array_mkArray1___redArg(v_val_1772_);
v___y_1605_ = v___y_1734_;
v___y_1606_ = v___y_1742_;
v___y_1607_ = v___x_1766_;
v___y_1608_ = v___y_1735_;
v___y_1609_ = v___y_1748_;
v___y_1610_ = v___y_1744_;
v___y_1611_ = v___y_1749_;
v___y_1612_ = v___y_1747_;
v___y_1613_ = v___y_1746_;
v___y_1614_ = v___y_1743_;
v___y_1615_ = v___y_1740_;
v___y_1616_ = v___y_1745_;
v___y_1617_ = v___y_1736_;
v___y_1618_ = v___x_1770_;
v___y_1619_ = v___y_1737_;
v___y_1620_ = v___x_1764_;
v___y_1621_ = v___x_1769_;
v___y_1622_ = v___x_1771_;
v___y_1623_ = v___y_1738_;
v___y_1624_ = v_argsArray_1741_;
v___y_1625_ = v___y_1739_;
v___y_1626_ = v___x_1773_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1605_ = v___y_1734_;
v___y_1606_ = v___y_1742_;
v___y_1607_ = v___x_1766_;
v___y_1608_ = v___y_1735_;
v___y_1609_ = v___y_1748_;
v___y_1610_ = v___y_1744_;
v___y_1611_ = v___y_1749_;
v___y_1612_ = v___y_1747_;
v___y_1613_ = v___y_1746_;
v___y_1614_ = v___y_1743_;
v___y_1615_ = v___y_1740_;
v___y_1616_ = v___y_1745_;
v___y_1617_ = v___y_1736_;
v___y_1618_ = v___x_1770_;
v___y_1619_ = v___y_1737_;
v___y_1620_ = v___x_1764_;
v___y_1621_ = v___x_1769_;
v___y_1622_ = v___x_1771_;
v___y_1623_ = v___y_1738_;
v___y_1624_ = v_argsArray_1741_;
v___y_1625_ = v___y_1739_;
v___y_1626_ = v___x_1774_;
goto v___jp_1604_;
}
}
}
v___jp_1775_:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1789_, v___y_1784_, v___y_1781_, v___y_1778_, v___y_1785_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = l_Lean_LibrarySuggestions_select(v_a_1794_, v___y_1792_, v___y_1784_, v___y_1781_, v___y_1778_, v___y_1785_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; size_t v_sz_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v_sz_1797_ = lean_array_size(v_a_1796_);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1796_, v_sz_1797_, v___x_1798_, v___y_1777_, v___y_1780_, v___y_1789_, v___y_1782_, v___y_1791_, v___y_1784_, v___y_1781_, v___y_1778_, v___y_1785_);
lean_dec(v_a_1796_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___y_1734_ = v___y_1776_;
v___y_1735_ = v___y_1779_;
v___y_1736_ = v___y_1786_;
v___y_1737_ = v___y_1787_;
v___y_1738_ = v___y_1788_;
v___y_1739_ = v___y_1790_;
v___y_1740_ = v___y_1783_;
v_argsArray_1741_ = v_a_1800_;
v___y_1742_ = v___y_1780_;
v___y_1743_ = v___y_1789_;
v___y_1744_ = v___y_1782_;
v___y_1745_ = v___y_1791_;
v___y_1746_ = v___y_1784_;
v___y_1747_ = v___y_1781_;
v___y_1748_ = v___y_1778_;
v___y_1749_ = v___y_1785_;
goto v___jp_1733_;
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v___y_1790_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1779_);
lean_dec(v___y_1776_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v_a_1801_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1799_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1799_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v___y_1790_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v_a_1809_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1795_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1795_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1790_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v_a_1817_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1793_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1793_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
v___jp_1825_:
{
lean_object* v_config_1843_; uint8_t v_suggestions_1844_; 
v_config_1843_ = lean_ctor_get(v___y_1828_, 0);
lean_inc_ref(v_config_1843_);
lean_dec_ref(v___y_1828_);
v_suggestions_1844_ = lean_ctor_get_uint8(v_config_1843_, sizeof(void*)*3 + 26);
if (v_suggestions_1844_ == 0)
{
lean_dec_ref(v_config_1843_);
lean_dec_ref(v___f_1187_);
v___y_1734_ = v___y_1826_;
v___y_1735_ = v___y_1829_;
v___y_1736_ = v___y_1836_;
v___y_1737_ = v___y_1837_;
v___y_1738_ = v___y_1838_;
v___y_1739_ = v___y_1840_;
v___y_1740_ = v___y_1833_;
v_argsArray_1741_ = v___y_1842_;
v___y_1742_ = v___y_1830_;
v___y_1743_ = v___y_1839_;
v___y_1744_ = v___y_1832_;
v___y_1745_ = v___y_1841_;
v___y_1746_ = v___y_1834_;
v___y_1747_ = v___y_1831_;
v___y_1748_ = v___y_1827_;
v___y_1749_ = v___y_1835_;
goto v___jp_1733_;
}
else
{
lean_object* v_maxSuggestions_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_maxSuggestions_1845_ = lean_ctor_get(v_config_1843_, 2);
lean_inc(v_maxSuggestions_1845_);
lean_dec_ref(v_config_1843_);
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1847_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1845_) == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_unsigned_to_nat(100u);
v___x_1849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1846_);
lean_ctor_set(v___x_1849_, 2, v___f_1187_);
lean_ctor_set(v___x_1849_, 3, v___x_1847_);
v___y_1776_ = v___y_1826_;
v___y_1777_ = v___y_1842_;
v___y_1778_ = v___y_1827_;
v___y_1779_ = v___y_1829_;
v___y_1780_ = v___y_1830_;
v___y_1781_ = v___y_1831_;
v___y_1782_ = v___y_1832_;
v___y_1783_ = v___y_1833_;
v___y_1784_ = v___y_1834_;
v___y_1785_ = v___y_1835_;
v___y_1786_ = v___y_1836_;
v___y_1787_ = v___y_1837_;
v___y_1788_ = v___y_1838_;
v___y_1789_ = v___y_1839_;
v___y_1790_ = v___y_1840_;
v___y_1791_ = v___y_1841_;
v___y_1792_ = v___x_1849_;
goto v___jp_1775_;
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1851_; 
v_val_1850_ = lean_ctor_get(v_maxSuggestions_1845_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v_maxSuggestions_1845_, 1);
v___x_1851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1851_, 0, v_val_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1846_);
lean_ctor_set(v___x_1851_, 2, v___f_1187_);
lean_ctor_set(v___x_1851_, 3, v___x_1847_);
v___y_1776_ = v___y_1826_;
v___y_1777_ = v___y_1842_;
v___y_1778_ = v___y_1827_;
v___y_1779_ = v___y_1829_;
v___y_1780_ = v___y_1830_;
v___y_1781_ = v___y_1831_;
v___y_1782_ = v___y_1832_;
v___y_1783_ = v___y_1833_;
v___y_1784_ = v___y_1834_;
v___y_1785_ = v___y_1835_;
v___y_1786_ = v___y_1836_;
v___y_1787_ = v___y_1837_;
v___y_1788_ = v___y_1838_;
v___y_1789_ = v___y_1839_;
v___y_1790_ = v___y_1840_;
v___y_1791_ = v___y_1841_;
v___y_1792_ = v___x_1851_;
goto v___jp_1775_;
}
}
}
v___jp_1852_:
{
uint8_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = 0;
lean_inc(v___y_1862_);
v___x_1868_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1862_, v___x_1867_, v___y_1853_, v___y_1859_, v___y_1855_);
if (lean_obj_tag(v___x_1868_) == 0)
{
if (lean_obj_tag(v___y_1865_) == 1)
{
lean_object* v_a_1869_; lean_object* v_val_1870_; lean_object* v___x_1871_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v_val_1870_ = lean_ctor_get(v___y_1865_, 0);
lean_inc(v_val_1870_);
lean_dec_ref_known(v___y_1865_, 1);
v___x_1871_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1870_);
lean_dec(v_val_1870_);
lean_inc(v___y_1860_);
v___y_1826_ = v___y_1860_;
v___y_1827_ = v___y_1859_;
v___y_1828_ = v_a_1869_;
v___y_1829_ = v___y_1860_;
v___y_1830_ = v___y_1853_;
v___y_1831_ = v___y_1858_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___x_1867_;
v___y_1834_ = v___y_1861_;
v___y_1835_ = v___y_1855_;
v___y_1836_ = v___y_1866_;
v___y_1837_ = v___y_1862_;
v___y_1838_ = v___y_1863_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1856_;
v___y_1841_ = v___y_1854_;
v___y_1842_ = v___x_1871_;
goto v___jp_1825_;
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
lean_dec(v___y_1865_);
v_a_1872_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1873_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1860_);
v___y_1826_ = v___y_1860_;
v___y_1827_ = v___y_1859_;
v___y_1828_ = v_a_1872_;
v___y_1829_ = v___y_1860_;
v___y_1830_ = v___y_1853_;
v___y_1831_ = v___y_1858_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___x_1867_;
v___y_1834_ = v___y_1861_;
v___y_1835_ = v___y_1855_;
v___y_1836_ = v___y_1866_;
v___y_1837_ = v___y_1862_;
v___y_1838_ = v___y_1863_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1856_;
v___y_1841_ = v___y_1854_;
v___y_1842_ = v___x_1873_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v___y_1860_);
lean_dec(v___y_1856_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v_a_1874_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1868_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1868_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
v___jp_1882_:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Syntax_getOptional_x3f(v___y_1888_);
lean_dec(v___y_1888_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_box(0);
v___y_1853_ = v___y_1884_;
v___y_1854_ = v___y_1895_;
v___y_1855_ = v___y_1889_;
v___y_1856_ = v___y_1894_;
v___y_1857_ = v___y_1893_;
v___y_1858_ = v___y_1885_;
v___y_1859_ = v___y_1883_;
v___y_1860_ = v___y_1896_;
v___y_1861_ = v___y_1890_;
v___y_1862_ = v___y_1891_;
v___y_1863_ = v___y_1892_;
v___y_1864_ = v___y_1887_;
v___y_1865_ = v___y_1886_;
v___y_1866_ = v___x_1898_;
goto v___jp_1852_;
}
else
{
lean_object* v_val_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_val_1899_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1897_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_val_1899_);
lean_dec(v___x_1897_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_val_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
v___y_1853_ = v___y_1884_;
v___y_1854_ = v___y_1895_;
v___y_1855_ = v___y_1889_;
v___y_1856_ = v___y_1894_;
v___y_1857_ = v___y_1893_;
v___y_1858_ = v___y_1885_;
v___y_1859_ = v___y_1883_;
v___y_1860_ = v___y_1896_;
v___y_1861_ = v___y_1890_;
v___y_1862_ = v___y_1891_;
v___y_1863_ = v___y_1892_;
v___y_1864_ = v___y_1887_;
v___y_1865_ = v___y_1886_;
v___y_1866_ = v___x_1904_;
goto v___jp_1852_;
}
}
}
}
v___jp_1907_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_unsigned_to_nat(4u);
v___x_1923_ = l_Lean_Syntax_getArg(v___y_1908_, v___x_1922_);
lean_dec(v___y_1908_);
v___x_1924_ = l_Lean_Syntax_getOptional_x3f(v___x_1923_);
lean_dec(v___x_1923_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_box(0);
v___y_1883_ = v___y_1920_;
v___y_1884_ = v___y_1914_;
v___y_1885_ = v___y_1919_;
v___y_1886_ = v_args_1913_;
v___y_1887_ = v___y_1916_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1921_;
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1910_;
v___y_1892_ = v___y_1911_;
v___y_1893_ = v___y_1915_;
v___y_1894_ = v___y_1912_;
v___y_1895_ = v___y_1917_;
v___y_1896_ = v___x_1925_;
goto v___jp_1882_;
}
else
{
lean_object* v_val_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_val_1926_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1924_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_val_1926_);
lean_dec(v___x_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_val_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v___y_1883_ = v___y_1920_;
v___y_1884_ = v___y_1914_;
v___y_1885_ = v___y_1919_;
v___y_1886_ = v_args_1913_;
v___y_1887_ = v___y_1916_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1921_;
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1910_;
v___y_1892_ = v___y_1911_;
v___y_1893_ = v___y_1915_;
v___y_1894_ = v___y_1912_;
v___y_1895_ = v___y_1917_;
v___y_1896_ = v___x_1931_;
goto v___jp_1882_;
}
}
}
}
v___jp_1935_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = lean_unsigned_to_nat(3u);
v___x_1950_ = l_Lean_Syntax_getArg(v___y_1936_, v___x_1949_);
v___x_1951_ = l_Lean_Syntax_isNone(v___x_1950_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; 
lean_inc(v___x_1950_);
v___x_1952_ = l_Lean_Syntax_matchesNull(v___x_1950_, v___x_1934_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
lean_dec(v___x_1950_);
lean_dec(v_o_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1954_ = l_Lean_Syntax_getArg(v___x_1950_, v___x_1198_);
lean_dec(v___x_1950_);
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1186_);
lean_inc_ref(v___x_1185_);
lean_inc_ref(v___x_1184_);
v___x_1956_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1955_);
lean_inc(v___x_1954_);
v___x_1957_ = l_Lean_Syntax_isOfKind(v___x_1954_, v___x_1956_);
lean_dec(v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_dec(v___x_1954_);
lean_dec(v_o_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1958_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v_args_1960_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_Syntax_getArg(v___x_1954_, v___x_1934_);
lean_dec(v___x_1954_);
v_args_1960_ = l_Lean_Syntax_getArgs(v___x_1959_);
lean_dec(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_args_1960_);
v___y_1908_ = v___y_1936_;
v___y_1909_ = v___y_1937_;
v___y_1910_ = v___y_1938_;
v___y_1911_ = v___y_1939_;
v___y_1912_ = v_o_1940_;
v_args_1913_ = v___x_1961_;
v___y_1914_ = v___y_1941_;
v___y_1915_ = v___y_1942_;
v___y_1916_ = v___y_1943_;
v___y_1917_ = v___y_1944_;
v___y_1918_ = v___y_1945_;
v___y_1919_ = v___y_1946_;
v___y_1920_ = v___y_1947_;
v___y_1921_ = v___y_1948_;
goto v___jp_1907_;
}
}
}
else
{
lean_object* v___x_1962_; 
lean_dec(v___x_1950_);
v___x_1962_ = lean_box(0);
v___y_1908_ = v___y_1936_;
v___y_1909_ = v___y_1937_;
v___y_1910_ = v___y_1938_;
v___y_1911_ = v___y_1939_;
v___y_1912_ = v_o_1940_;
v_args_1913_ = v___x_1962_;
v___y_1914_ = v___y_1941_;
v___y_1915_ = v___y_1942_;
v___y_1916_ = v___y_1943_;
v___y_1917_ = v___y_1944_;
v___y_1918_ = v___y_1945_;
v___y_1919_ = v___y_1946_;
v___y_1920_ = v___y_1947_;
v___y_1921_ = v___y_1948_;
goto v___jp_1907_;
}
}
v___jp_1963_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1973_ = lean_unsigned_to_nat(2u);
v___x_1974_ = l_Lean_Syntax_getArg(v_stx_1182_, v___x_1973_);
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1186_);
lean_inc_ref(v___x_1185_);
lean_inc_ref(v___x_1184_);
v___x_1976_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1975_);
lean_inc(v___x_1974_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v___x_1974_, v___x_1976_);
lean_dec(v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v___x_1974_);
lean_dec(v_bang_1964_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1978_;
}
else
{
lean_object* v_cfg_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_cfg_1979_ = l_Lean_Syntax_getArg(v___x_1974_, v___x_1198_);
v___x_1980_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1186_);
lean_inc_ref(v___x_1185_);
lean_inc_ref(v___x_1184_);
v___x_1981_ = l_Lean_Name_mkStr4(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1980_);
lean_inc(v_cfg_1979_);
v___x_1982_ = l_Lean_Syntax_isOfKind(v_cfg_1979_, v___x_1981_);
lean_dec(v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec(v_cfg_1979_);
lean_dec(v___x_1974_);
lean_dec(v_bang_1964_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1983_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = l_Lean_Syntax_getArg(v___x_1974_, v___x_1934_);
v___x_1985_ = l_Lean_Syntax_getArg(v___x_1974_, v___x_1973_);
v___x_1986_ = l_Lean_Syntax_isNone(v___x_1985_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
lean_inc(v___x_1985_);
v___x_1987_ = l_Lean_Syntax_matchesNull(v___x_1985_, v___x_1934_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec(v___x_1985_);
lean_dec(v___x_1984_);
lean_dec(v_cfg_1979_);
lean_dec(v___x_1974_);
lean_dec(v_bang_1964_);
lean_dec(v_tk_1199_);
lean_dec_ref(v___f_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
v___x_1988_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1988_;
}
else
{
lean_object* v_o_1989_; lean_object* v___x_1990_; 
v_o_1989_ = l_Lean_Syntax_getArg(v___x_1985_, v___x_1198_);
lean_dec(v___x_1985_);
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_o_1989_);
v___y_1936_ = v___x_1974_;
v___y_1937_ = v___x_1984_;
v___y_1938_ = v_cfg_1979_;
v___y_1939_ = v_bang_1964_;
v_o_1940_ = v___x_1990_;
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1966_;
v___y_1943_ = v___y_1967_;
v___y_1944_ = v___y_1968_;
v___y_1945_ = v___y_1969_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1971_;
v___y_1948_ = v___y_1972_;
goto v___jp_1935_;
}
}
else
{
lean_object* v___x_1991_; 
lean_dec(v___x_1985_);
v___x_1991_ = lean_box(0);
v___y_1936_ = v___x_1974_;
v___y_1937_ = v___x_1984_;
v___y_1938_ = v_cfg_1979_;
v___y_1939_ = v_bang_1964_;
v_o_1940_ = v___x_1991_;
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1966_;
v___y_1943_ = v___y_1967_;
v___y_1944_ = v___y_1968_;
v___y_1945_ = v___y_1969_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1971_;
v___y_1948_ = v___y_1972_;
goto v___jp_1935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_1999_, lean_object* v_stx_2000_, lean_object* v___x_2001_, lean_object* v___x_2002_, lean_object* v___x_2003_, lean_object* v___x_2004_, lean_object* v___f_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v___x_35652__boxed_2015_; uint8_t v___x_35653__boxed_2016_; lean_object* v_res_2017_; 
v___x_35652__boxed_2015_ = lean_unbox(v___x_1999_);
v___x_35653__boxed_2016_ = lean_unbox(v___x_2001_);
v_res_2017_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35652__boxed_2015_, v_stx_2000_, v___x_35653__boxed_2016_, v___x_2002_, v___x_2003_, v___x_2004_, v___f_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v_stx_2000_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; uint8_t v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___y_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2040_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2027_);
v___x_2041_ = l_Lean_Syntax_isOfKind(v_stx_2027_, v___x_2040_);
v___x_2042_ = 1;
v___f_2043_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2044_ = lean_box(v___x_2041_);
v___x_2045_ = lean_box(v___x_2042_);
v___y_2046_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2046_, 0, v___x_2044_);
lean_closure_set(v___y_2046_, 1, v_stx_2027_);
lean_closure_set(v___y_2046_, 2, v___x_2045_);
lean_closure_set(v___y_2046_, 3, v___x_2037_);
lean_closure_set(v___y_2046_, 4, v___x_2038_);
lean_closure_set(v___y_2046_, 5, v___x_2039_);
lean_closure_set(v___y_2046_, 6, v___f_2043_);
v___x_2047_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2047_, 0, v___y_2046_);
v___x_2048_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2047_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2060_, lean_object* v_as_2061_, lean_object* v_as_x27_2062_, lean_object* v_b_2063_, lean_object* v_a_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2060_, v_as_x27_2062_, v_b_2063_, v___y_2071_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2075_, lean_object* v_as_2076_, lean_object* v_as_x27_2077_, lean_object* v_b_2078_, lean_object* v_a_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2075_, v_as_2076_, v_as_x27_2077_, v_b_2078_, v_a_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v_as_x27_2077_);
lean_dec(v_as_2076_);
lean_dec(v___x_2075_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2090_, lean_object* v_ref_2091_, lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2091_, v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_ref_2104_, lean_object* v_msg_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2103_, v_ref_2104_, v_msg_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_ref_2104_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2116_, lean_object* v_ref_2117_, lean_object* v_constName_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2117_, v_constName_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_ref_2130_, lean_object* v_constName_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2129_, v_ref_2130_, v_constName_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_ref_2130_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2142_, lean_object* v_msg_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2143_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2154_, v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2166_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec_ref(v_opt_2177_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2188_, lean_object* v_ref_2189_, lean_object* v_msg_2190_, lean_object* v_declHint_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2189_, v_msg_2190_, v_declHint_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_ref_2203_, lean_object* v_msg_2204_, lean_object* v_declHint_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2202_, v_ref_2203_, v_msg_2204_, v_declHint_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v_ref_2203_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2216_, lean_object* v_declHint_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2216_, v_declHint_2217_, v___y_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2228_, lean_object* v_declHint_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2228_, v_declHint_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2240_, lean_object* v_msgData_2241_, uint8_t v_severity_2242_, uint8_t v_isSilent_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2240_, v_msgData_2241_, v_severity_2242_, v_isSilent_2243_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2254_, lean_object* v_msgData_2255_, lean_object* v_severity_2256_, lean_object* v_isSilent_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
uint8_t v_severity_boxed_2267_; uint8_t v_isSilent_boxed_2268_; lean_object* v_res_2269_; 
v_severity_boxed_2267_ = lean_unbox(v_severity_2256_);
v_isSilent_boxed_2268_ = lean_unbox(v_isSilent_2257_);
v_res_2269_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2254_, v_msgData_2255_, v_severity_boxed_2267_, v_isSilent_boxed_2268_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_ref_2254_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2277_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2278_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2280_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2281_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2277_, v___x_2278_, v___x_2279_, v___x_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2312_ = l_Lean_addBuiltinDeclarationRanges(v___x_2310_, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2315_, lean_object* v_as_x27_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_){
_start:
{
if (lean_obj_tag(v_as_x27_2316_) == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_b_2317_);
return v___x_2320_;
}
else
{
lean_object* v_head_2321_; lean_object* v_tail_2322_; lean_object* v_ref_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_head_2321_ = lean_ctor_get(v_as_x27_2316_, 0);
v_tail_2322_ = lean_ctor_get(v_as_x27_2316_, 1);
v_ref_2323_ = lean_ctor_get(v___y_2318_, 2);
v___x_2324_ = 1;
v___x_2325_ = 0;
v___x_2326_ = l_Lean_SourceInfo_fromRef(v_ref_2323_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2329_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2326_);
v___x_2330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2326_);
lean_ctor_set(v___x_2330_, 1, v___x_2328_);
lean_ctor_set(v___x_2330_, 2, v___x_2329_);
lean_inc(v_head_2321_);
v___x_2331_ = l_Lean_mkCIdentFrom(v___x_2315_, v_head_2321_, v___x_2324_);
lean_inc_ref(v___x_2330_);
v___x_2332_ = l_Lean_Syntax_node3(v___x_2326_, v___x_2327_, v___x_2330_, v___x_2330_, v___x_2331_);
v___x_2333_ = lean_array_push(v_b_2317_, v___x_2332_);
v_as_x27_2316_ = v_tail_2322_;
v_b_2317_ = v___x_2333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2335_, lean_object* v_as_x27_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2335_, v_as_x27_2336_, v_b_2337_, v___y_2338_);
lean_dec_ref(v___y_2338_);
lean_dec(v_as_x27_2336_);
lean_dec(v___x_2335_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2341_, size_t v_sz_2342_, size_t v_i_2343_, lean_object* v_b_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_lt(v_i_2343_, v_sz_2342_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_b_2344_);
return v___x_2355_;
}
else
{
lean_object* v_a_2356_; lean_object* v_name_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_a_2356_ = lean_array_uget_borrowed(v_as_2341_, v_i_2343_);
v_name_2357_ = lean_ctor_get(v_a_2356_, 0);
lean_inc(v_name_2357_);
v___x_2358_ = l_Lean_mkIdent(v_name_2357_);
lean_inc(v___x_2358_);
v___x_2359_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2358_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2358_, v_a_2360_, v_b_2344_, v___y_2351_);
lean_dec(v_a_2360_);
lean_dec(v___x_2358_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; size_t v___x_2363_; size_t v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_add(v_i_2343_, v___x_2363_);
v_i_2343_ = v___x_2364_;
v_b_2344_ = v_a_2362_;
goto _start;
}
else
{
return v___x_2361_;
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___x_2358_);
lean_dec_ref(v_b_2344_);
v_a_2366_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2359_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2359_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2374_, lean_object* v_sz_2375_, lean_object* v_i_2376_, lean_object* v_b_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
size_t v_sz_boxed_2387_; size_t v_i_boxed_2388_; lean_object* v_res_2389_; 
v_sz_boxed_2387_ = lean_unbox_usize(v_sz_2375_);
lean_dec(v_sz_2375_);
v_i_boxed_2388_ = lean_unbox_usize(v_i_2376_);
lean_dec(v_i_2376_);
v_res_2389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2374_, v_sz_boxed_2387_, v_i_boxed_2388_, v_b_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v_as_2374_);
return v_res_2389_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___x_2392_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_unsigned_to_nat(32u);
v___x_2396_ = lean_mk_empty_array_with_capacity(v___x_2395_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2398_ = ((size_t)5ULL);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_unsigned_to_nat(32u);
v___x_2401_ = lean_mk_empty_array_with_capacity(v___x_2400_);
v___x_2402_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
lean_ctor_set(v___x_2403_, 2, v___x_2399_);
lean_ctor_set(v___x_2403_, 3, v___x_2399_);
lean_ctor_set_usize(v___x_2403_, 4, v___x_2398_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2405_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
lean_ctor_set(v___x_2406_, 2, v___x_2405_);
lean_ctor_set(v___x_2406_, 3, v___x_2404_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2408_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2418_, lean_object* v_stx_2419_, uint8_t v___x_2420_, lean_object* v___x_2421_, lean_object* v___x_2422_, lean_object* v___x_2423_, lean_object* v___f_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
if (v___x_2418_ == 0)
{
lean_object* v___x_2434_; 
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_2434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; lean_object* v_tk_2436_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v_stxForSuggestion_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; uint8_t v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; uint8_t v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; uint8_t v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; uint8_t v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; uint8_t v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v_stxForExecution_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint8_t v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; uint8_t v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; uint8_t v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; uint8_t v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; uint8_t v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v_argsArray_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; uint8_t v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v_args_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___x_3306_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v_o_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v_bang_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_2435_ = lean_unsigned_to_nat(0u);
v_tk_2436_ = l_Lean_Syntax_getArg(v_stx_2419_, v___x_2435_);
v___x_3306_ = lean_unsigned_to_nat(1u);
v___x_3364_ = l_Lean_Syntax_getArg(v_stx_2419_, v___x_3306_);
v___x_3365_ = l_Lean_Syntax_isNone(v___x_3364_);
if (v___x_3365_ == 0)
{
uint8_t v___x_3366_; 
lean_inc(v___x_3364_);
v___x_3366_ = l_Lean_Syntax_matchesNull(v___x_3364_, v___x_3306_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; 
lean_dec(v___x_3364_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_3367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3367_;
}
else
{
lean_object* v_bang_3368_; lean_object* v___x_3369_; 
v_bang_3368_ = l_Lean_Syntax_getArg(v___x_3364_, v___x_2435_);
lean_dec(v___x_3364_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_bang_3368_);
v_bang_3336_ = v___x_3369_;
v___y_3337_ = v___y_2425_;
v___y_3338_ = v___y_2426_;
v___y_3339_ = v___y_2427_;
v___y_3340_ = v___y_2428_;
v___y_3341_ = v___y_2429_;
v___y_3342_ = v___y_2430_;
v___y_3343_ = v___y_2431_;
v___y_3344_ = v___y_2432_;
goto v___jp_3335_;
}
}
else
{
lean_object* v___x_3370_; 
lean_dec(v___x_3364_);
v___x_3370_ = lean_box(0);
v_bang_3336_ = v___x_3370_;
v___y_3337_ = v___y_2425_;
v___y_3338_ = v___y_2426_;
v___y_3339_ = v___y_2427_;
v___y_3340_ = v___y_2428_;
v___y_3341_ = v___y_2429_;
v___y_3342_ = v___y_2430_;
v___y_3343_ = v___y_2431_;
v___y_3344_ = v___y_2432_;
goto v___jp_3335_;
}
v___jp_2437_:
{
lean_object* v_usedTheorems_2444_; lean_object* v_diag_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2487_; 
v_usedTheorems_2444_ = lean_ctor_get(v___y_2438_, 0);
v_diag_2445_ = lean_ctor_get(v___y_2438_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___y_2438_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2447_ = v___y_2438_;
v_isShared_2448_ = v_isSharedCheck_2487_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_diag_2445_);
lean_inc(v_usedTheorems_2444_);
lean_dec(v___y_2438_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2487_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2439_, v_usedTheorems_2444_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec_ref(v_usedTheorems_2444_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_ref_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_ref_2451_ = lean_ctor_get(v___y_2442_, 2);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v_a_2450_);
lean_ctor_set(v___x_2447_, 0, v___x_2452_);
v___x_2454_ = v___x_2447_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_a_2450_);
v___x_2454_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_ctor_set(v___x_2456_, 2, v___x_2455_);
lean_ctor_set(v___x_2456_, 3, v___x_2455_);
lean_ctor_set(v___x_2456_, 4, v___x_2455_);
lean_ctor_set(v___x_2456_, 5, v___x_2455_);
lean_inc(v_ref_2451_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_ref_2451_);
v___x_2458_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2459_ = 4;
v___x_2460_ = l_Lean_MessageData_nil;
v___x_2461_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2436_, v___x_2456_, v___x_2457_, v___x_2458_, v___x_2455_, v___x_2459_, v___x_2460_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2461_, 0);
lean_dec(v_unused_2469_);
v___x_2463_ = v___x_2461_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v___x_2461_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_diag_2445_);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_diag_2445_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_diag_2445_);
v_a_2470_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2461_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2461_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_del_object(v___x_2447_);
lean_dec_ref(v_diag_2445_);
lean_dec(v_tk_2436_);
v_a_2479_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2449_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2449_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
v___jp_2488_:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2495_, v___y_2494_, v___y_2493_, v___y_2490_, v___y_2492_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2500_ = l_Lean_Meta_simpAll(v_a_2498_, v___y_2496_, v___y_2489_, v___x_2499_, v___y_2494_, v___y_2493_, v___y_2490_, v___y_2492_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v_fst_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v_fst_2502_ = lean_ctor_get(v_a_2501_, 0);
if (lean_obj_tag(v_fst_2502_) == 0)
{
lean_object* v_snd_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_snd_2503_ = lean_ctor_get(v_a_2501_, 1);
lean_inc(v_snd_2503_);
lean_dec(v_a_2501_);
v___x_2504_ = lean_box(0);
v___x_2505_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2504_, v___y_2495_, v___y_2494_, v___y_2493_, v___y_2490_, v___y_2492_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_dec_ref_known(v___x_2505_, 1);
v___y_2438_ = v_snd_2503_;
v___y_2439_ = v___y_2491_;
v___y_2440_ = v___y_2494_;
v___y_2441_ = v___y_2493_;
v___y_2442_ = v___y_2490_;
v___y_2443_ = v___y_2492_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_snd_2503_);
lean_dec(v___y_2491_);
lean_dec(v_tk_2436_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_snd_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2532_; 
lean_inc_ref(v_fst_2502_);
v_snd_2514_ = lean_ctor_get(v_a_2501_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_a_2501_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v_a_2501_, 0);
lean_dec(v_unused_2533_);
v___x_2516_ = v_a_2501_;
v_isShared_2517_ = v_isSharedCheck_2532_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snd_2514_);
lean_dec(v_a_2501_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2532_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_val_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v_val_2518_ = lean_ctor_get(v_fst_2502_, 0);
lean_inc(v_val_2518_);
lean_dec_ref_known(v_fst_2502_, 1);
v___x_2519_ = lean_box(0);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 1);
lean_ctor_set(v___x_2516_, 1, v___x_2519_);
lean_ctor_set(v___x_2516_, 0, v_val_2518_);
v___x_2521_ = v___x_2516_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_val_2518_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2521_, v___y_2495_, v___y_2494_, v___y_2493_, v___y_2490_, v___y_2492_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
v___y_2438_ = v_snd_2514_;
v___y_2439_ = v___y_2491_;
v___y_2440_ = v___y_2494_;
v___y_2441_ = v___y_2493_;
v___y_2442_ = v___y_2490_;
v___y_2443_ = v___y_2492_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_snd_2514_);
lean_dec(v___y_2491_);
lean_dec(v_tk_2436_);
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v___y_2491_);
lean_dec(v_tk_2436_);
v_a_2534_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2500_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2500_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2489_);
lean_dec(v_tk_2436_);
v_a_2542_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2497_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2497_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
v___jp_2550_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2564_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2553_, v___x_2420_, v___y_2551_, v___x_2420_, v___x_2563_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2553_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2564_, 1);
if (lean_obj_tag(v___y_2552_) == 0)
{
lean_object* v_ctx_2566_; lean_object* v_simprocs_2567_; 
v_ctx_2566_ = lean_ctor_get(v_a_2565_, 0);
lean_inc_ref(v_ctx_2566_);
v_simprocs_2567_ = lean_ctor_get(v_a_2565_, 1);
lean_inc_ref(v_simprocs_2567_);
lean_dec(v_a_2565_);
v___y_2489_ = v_simprocs_2567_;
v___y_2490_ = v___y_2561_;
v___y_2491_ = v_stxForSuggestion_2554_;
v___y_2492_ = v___y_2562_;
v___y_2493_ = v___y_2560_;
v___y_2494_ = v___y_2559_;
v___y_2495_ = v___y_2556_;
v___y_2496_ = v_ctx_2566_;
goto v___jp_2488_;
}
else
{
lean_object* v_ctx_2568_; lean_object* v_simprocs_2569_; lean_object* v___x_2570_; 
lean_dec_ref_known(v___y_2552_, 1);
v_ctx_2568_ = lean_ctor_get(v_a_2565_, 0);
lean_inc_ref(v_ctx_2568_);
v_simprocs_2569_ = lean_ctor_get(v_a_2565_, 1);
lean_inc_ref(v_simprocs_2569_);
lean_dec(v_a_2565_);
v___x_2570_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2568_);
v___y_2489_ = v_simprocs_2569_;
v___y_2490_ = v___y_2561_;
v___y_2491_ = v_stxForSuggestion_2554_;
v___y_2492_ = v___y_2562_;
v___y_2493_ = v___y_2560_;
v___y_2494_ = v___y_2559_;
v___y_2495_ = v___y_2556_;
v___y_2496_ = v___x_2570_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_stxForSuggestion_2554_);
lean_dec(v___y_2552_);
lean_dec(v_tk_2436_);
v_a_2571_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2564_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2564_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
v___jp_2579_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_inc_ref_n(v___y_2594_, 2);
v___x_2600_ = l_Array_append___redArg(v___y_2594_, v___y_2599_);
lean_dec_ref(v___y_2599_);
lean_inc_n(v___y_2586_, 3);
lean_inc_n(v___y_2596_, 5);
v___x_2601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2601_, 0, v___y_2596_);
lean_ctor_set(v___x_2601_, 1, v___y_2586_);
lean_ctor_set(v___x_2601_, 2, v___x_2600_);
v___x_2602_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___y_2596_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2605_ = l_Lean_Syntax_SepArray_ofElems(v___x_2604_, v___y_2580_);
lean_dec_ref(v___y_2580_);
v___x_2606_ = l_Array_append___redArg(v___y_2594_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2607_, 0, v___y_2596_);
lean_ctor_set(v___x_2607_, 1, v___y_2586_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
v___x_2608_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___y_2596_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = l_Lean_Syntax_node3(v___y_2596_, v___y_2586_, v___x_2603_, v___x_2607_, v___x_2609_);
v___x_2611_ = l_Lean_Syntax_node5(v___y_2596_, v___y_2583_, v___y_2582_, v___y_2591_, v___y_2597_, v___x_2601_, v___x_2610_);
v___y_2551_ = v___y_2590_;
v___y_2552_ = v___y_2584_;
v___y_2553_ = v___y_2585_;
v_stxForSuggestion_2554_ = v___x_2611_;
v___y_2555_ = v___y_2587_;
v___y_2556_ = v___y_2592_;
v___y_2557_ = v___y_2593_;
v___y_2558_ = v___y_2581_;
v___y_2559_ = v___y_2595_;
v___y_2560_ = v___y_2589_;
v___y_2561_ = v___y_2588_;
v___y_2562_ = v___y_2598_;
goto v___jp_2550_;
}
v___jp_2612_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc_ref(v___y_2628_);
v___x_2633_ = l_Array_append___redArg(v___y_2628_, v___y_2632_);
lean_dec_ref(v___y_2632_);
lean_inc(v___y_2618_);
lean_inc(v___y_2630_);
v___x_2634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2634_, 0, v___y_2630_);
lean_ctor_set(v___x_2634_, 1, v___y_2618_);
lean_ctor_set(v___x_2634_, 2, v___x_2633_);
if (lean_obj_tag(v___y_2623_) == 1)
{
lean_object* v_val_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_val_2635_ = lean_ctor_get(v___y_2623_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v___y_2623_, 1);
v___x_2636_ = l_Lean_SourceInfo_fromRef(v_val_2635_, v___x_2420_);
lean_dec(v_val_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2636_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Array_mkArray1___redArg(v___x_2638_);
v___y_2580_ = v___y_2613_;
v___y_2581_ = v___y_2614_;
v___y_2582_ = v___y_2615_;
v___y_2583_ = v___y_2616_;
v___y_2584_ = v___y_2617_;
v___y_2585_ = v___y_2619_;
v___y_2586_ = v___y_2618_;
v___y_2587_ = v___y_2620_;
v___y_2588_ = v___y_2621_;
v___y_2589_ = v___y_2622_;
v___y_2590_ = v___y_2627_;
v___y_2591_ = v___y_2626_;
v___y_2592_ = v___y_2625_;
v___y_2593_ = v___y_2624_;
v___y_2594_ = v___y_2628_;
v___y_2595_ = v___y_2629_;
v___y_2596_ = v___y_2630_;
v___y_2597_ = v___x_2634_;
v___y_2598_ = v___y_2631_;
v___y_2599_ = v___x_2639_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2640_; 
lean_dec(v___y_2623_);
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2580_ = v___y_2613_;
v___y_2581_ = v___y_2614_;
v___y_2582_ = v___y_2615_;
v___y_2583_ = v___y_2616_;
v___y_2584_ = v___y_2617_;
v___y_2585_ = v___y_2619_;
v___y_2586_ = v___y_2618_;
v___y_2587_ = v___y_2620_;
v___y_2588_ = v___y_2621_;
v___y_2589_ = v___y_2622_;
v___y_2590_ = v___y_2627_;
v___y_2591_ = v___y_2626_;
v___y_2592_ = v___y_2625_;
v___y_2593_ = v___y_2624_;
v___y_2594_ = v___y_2628_;
v___y_2595_ = v___y_2629_;
v___y_2596_ = v___y_2630_;
v___y_2597_ = v___x_2634_;
v___y_2598_ = v___y_2631_;
v___y_2599_ = v___x_2640_;
goto v___jp_2579_;
}
}
v___jp_2641_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_inc_ref_n(v___y_2644_, 2);
v___x_2662_ = l_Array_append___redArg(v___y_2644_, v___y_2661_);
lean_dec_ref(v___y_2661_);
lean_inc_n(v___y_2659_, 3);
lean_inc_n(v___y_2657_, 5);
v___x_2663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2663_, 0, v___y_2657_);
lean_ctor_set(v___x_2663_, 1, v___y_2659_);
lean_ctor_set(v___x_2663_, 2, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___y_2657_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2667_ = l_Lean_Syntax_SepArray_ofElems(v___x_2666_, v___y_2642_);
lean_dec_ref(v___y_2642_);
v___x_2668_ = l_Array_append___redArg(v___y_2644_, v___x_2667_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___y_2657_);
lean_ctor_set(v___x_2669_, 1, v___y_2659_);
lean_ctor_set(v___x_2669_, 2, v___x_2668_);
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2657_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_Syntax_node3(v___y_2657_, v___y_2659_, v___x_2665_, v___x_2669_, v___x_2671_);
v___x_2673_ = l_Lean_Syntax_node5(v___y_2657_, v___y_2646_, v___y_2645_, v___y_2654_, v___y_2651_, v___x_2663_, v___x_2672_);
v___y_2551_ = v___y_2653_;
v___y_2552_ = v___y_2647_;
v___y_2553_ = v___y_2648_;
v_stxForSuggestion_2554_ = v___x_2673_;
v___y_2555_ = v___y_2649_;
v___y_2556_ = v___y_2655_;
v___y_2557_ = v___y_2656_;
v___y_2558_ = v___y_2643_;
v___y_2559_ = v___y_2658_;
v___y_2560_ = v___y_2652_;
v___y_2561_ = v___y_2650_;
v___y_2562_ = v___y_2660_;
goto v___jp_2550_;
}
v___jp_2674_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_inc_ref(v___y_2677_);
v___x_2695_ = l_Array_append___redArg(v___y_2677_, v___y_2694_);
lean_dec_ref(v___y_2694_);
lean_inc(v___y_2692_);
lean_inc(v___y_2690_);
v___x_2696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2696_, 0, v___y_2690_);
lean_ctor_set(v___x_2696_, 1, v___y_2692_);
lean_ctor_set(v___x_2696_, 2, v___x_2695_);
if (lean_obj_tag(v___y_2685_) == 1)
{
lean_object* v_val_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_val_2697_ = lean_ctor_get(v___y_2685_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v___y_2685_, 1);
v___x_2698_ = l_Lean_SourceInfo_fromRef(v_val_2697_, v___x_2420_);
lean_dec(v_val_2697_);
v___x_2699_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Array_mkArray1___redArg(v___x_2700_);
v___y_2642_ = v___y_2675_;
v___y_2643_ = v___y_2676_;
v___y_2644_ = v___y_2677_;
v___y_2645_ = v___y_2678_;
v___y_2646_ = v___y_2679_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v___y_2682_;
v___y_2650_ = v___y_2683_;
v___y_2651_ = v___x_2696_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2689_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v___y_2687_;
v___y_2656_ = v___y_2686_;
v___y_2657_ = v___y_2690_;
v___y_2658_ = v___y_2691_;
v___y_2659_ = v___y_2692_;
v___y_2660_ = v___y_2693_;
v___y_2661_ = v___x_2701_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2702_; 
lean_dec(v___y_2685_);
v___x_2702_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2642_ = v___y_2675_;
v___y_2643_ = v___y_2676_;
v___y_2644_ = v___y_2677_;
v___y_2645_ = v___y_2678_;
v___y_2646_ = v___y_2679_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v___y_2682_;
v___y_2650_ = v___y_2683_;
v___y_2651_ = v___x_2696_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2689_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v___y_2687_;
v___y_2656_ = v___y_2686_;
v___y_2657_ = v___y_2690_;
v___y_2658_ = v___y_2691_;
v___y_2659_ = v___y_2692_;
v___y_2660_ = v___y_2693_;
v___y_2661_ = v___x_2702_;
goto v___jp_2641_;
}
}
v___jp_2703_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_inc_ref_n(v___y_2719_, 2);
v___x_2723_ = l_Array_append___redArg(v___y_2719_, v___y_2722_);
lean_dec_ref(v___y_2722_);
lean_inc_n(v___y_2704_, 2);
lean_inc_n(v___y_2709_, 2);
v___x_2724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2724_, 0, v___y_2709_);
lean_ctor_set(v___x_2724_, 1, v___y_2704_);
lean_ctor_set(v___x_2724_, 2, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2709_);
lean_ctor_set(v___x_2725_, 1, v___y_2704_);
lean_ctor_set(v___x_2725_, 2, v___y_2719_);
v___x_2726_ = l_Lean_Syntax_node5(v___y_2709_, v___y_2705_, v___y_2712_, v___y_2715_, v___y_2720_, v___x_2724_, v___x_2725_);
v___y_2551_ = v___y_2714_;
v___y_2552_ = v___y_2707_;
v___y_2553_ = v___y_2708_;
v_stxForSuggestion_2554_ = v___x_2726_;
v___y_2555_ = v___y_2710_;
v___y_2556_ = v___y_2716_;
v___y_2557_ = v___y_2717_;
v___y_2558_ = v___y_2706_;
v___y_2559_ = v___y_2718_;
v___y_2560_ = v___y_2713_;
v___y_2561_ = v___y_2711_;
v___y_2562_ = v___y_2721_;
goto v___jp_2550_;
}
v___jp_2727_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_inc_ref(v___y_2744_);
v___x_2747_ = l_Array_append___redArg(v___y_2744_, v___y_2746_);
lean_dec_ref(v___y_2746_);
lean_inc(v___y_2728_);
lean_inc(v___y_2732_);
v___x_2748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___y_2732_);
lean_ctor_set(v___x_2748_, 1, v___y_2728_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
if (lean_obj_tag(v___y_2738_) == 1)
{
lean_object* v_val_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_val_2749_ = lean_ctor_get(v___y_2738_, 0);
lean_inc(v_val_2749_);
lean_dec_ref_known(v___y_2738_, 1);
v___x_2750_ = l_Lean_SourceInfo_fromRef(v_val_2749_, v___x_2420_);
lean_dec(v_val_2749_);
v___x_2751_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l_Array_mkArray1___redArg(v___x_2752_);
v___y_2704_ = v___y_2728_;
v___y_2705_ = v___y_2729_;
v___y_2706_ = v___y_2730_;
v___y_2707_ = v___y_2731_;
v___y_2708_ = v___y_2733_;
v___y_2709_ = v___y_2732_;
v___y_2710_ = v___y_2734_;
v___y_2711_ = v___y_2735_;
v___y_2712_ = v___y_2736_;
v___y_2713_ = v___y_2737_;
v___y_2714_ = v___y_2742_;
v___y_2715_ = v___y_2741_;
v___y_2716_ = v___y_2740_;
v___y_2717_ = v___y_2739_;
v___y_2718_ = v___y_2743_;
v___y_2719_ = v___y_2744_;
v___y_2720_ = v___x_2748_;
v___y_2721_ = v___y_2745_;
v___y_2722_ = v___x_2753_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2754_; 
lean_dec(v___y_2738_);
v___x_2754_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2704_ = v___y_2728_;
v___y_2705_ = v___y_2729_;
v___y_2706_ = v___y_2730_;
v___y_2707_ = v___y_2731_;
v___y_2708_ = v___y_2733_;
v___y_2709_ = v___y_2732_;
v___y_2710_ = v___y_2734_;
v___y_2711_ = v___y_2735_;
v___y_2712_ = v___y_2736_;
v___y_2713_ = v___y_2737_;
v___y_2714_ = v___y_2742_;
v___y_2715_ = v___y_2741_;
v___y_2716_ = v___y_2740_;
v___y_2717_ = v___y_2739_;
v___y_2718_ = v___y_2743_;
v___y_2719_ = v___y_2744_;
v___y_2720_ = v___x_2748_;
v___y_2721_ = v___y_2745_;
v___y_2722_ = v___x_2754_;
goto v___jp_2703_;
}
}
v___jp_2755_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_inc_ref_n(v___y_2760_, 2);
v___x_2775_ = l_Array_append___redArg(v___y_2760_, v___y_2774_);
lean_dec_ref(v___y_2774_);
lean_inc_n(v___y_2771_, 2);
lean_inc_n(v___y_2759_, 2);
v___x_2776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2776_, 0, v___y_2759_);
lean_ctor_set(v___x_2776_, 1, v___y_2771_);
lean_ctor_set(v___x_2776_, 2, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2777_, 0, v___y_2759_);
lean_ctor_set(v___x_2777_, 1, v___y_2771_);
lean_ctor_set(v___x_2777_, 2, v___y_2760_);
v___x_2778_ = l_Lean_Syntax_node5(v___y_2759_, v___y_2772_, v___y_2757_, v___y_2766_, v___y_2769_, v___x_2776_, v___x_2777_);
v___y_2551_ = v___y_2765_;
v___y_2552_ = v___y_2758_;
v___y_2553_ = v___y_2761_;
v_stxForSuggestion_2554_ = v___x_2778_;
v___y_2555_ = v___y_2762_;
v___y_2556_ = v___y_2767_;
v___y_2557_ = v___y_2768_;
v___y_2558_ = v___y_2756_;
v___y_2559_ = v___y_2770_;
v___y_2560_ = v___y_2764_;
v___y_2561_ = v___y_2763_;
v___y_2562_ = v___y_2773_;
goto v___jp_2550_;
}
v___jp_2779_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_inc_ref(v___y_2784_);
v___x_2799_ = l_Array_append___redArg(v___y_2784_, v___y_2798_);
lean_dec_ref(v___y_2798_);
lean_inc(v___y_2796_);
lean_inc(v___y_2782_);
v___x_2800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2800_, 0, v___y_2782_);
lean_ctor_set(v___x_2800_, 1, v___y_2796_);
lean_ctor_set(v___x_2800_, 2, v___x_2799_);
if (lean_obj_tag(v___y_2789_) == 1)
{
lean_object* v_val_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_val_2801_ = lean_ctor_get(v___y_2789_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v___y_2789_, 1);
v___x_2802_ = l_Lean_SourceInfo_fromRef(v_val_2801_, v___x_2420_);
lean_dec(v_val_2801_);
v___x_2803_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Array_mkArray1___redArg(v___x_2804_);
v___y_2756_ = v___y_2780_;
v___y_2757_ = v___y_2781_;
v___y_2758_ = v___y_2783_;
v___y_2759_ = v___y_2782_;
v___y_2760_ = v___y_2784_;
v___y_2761_ = v___y_2785_;
v___y_2762_ = v___y_2786_;
v___y_2763_ = v___y_2787_;
v___y_2764_ = v___y_2788_;
v___y_2765_ = v___y_2792_;
v___y_2766_ = v___y_2793_;
v___y_2767_ = v___y_2791_;
v___y_2768_ = v___y_2790_;
v___y_2769_ = v___x_2800_;
v___y_2770_ = v___y_2794_;
v___y_2771_ = v___y_2796_;
v___y_2772_ = v___y_2795_;
v___y_2773_ = v___y_2797_;
v___y_2774_ = v___x_2805_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2806_; 
lean_dec(v___y_2789_);
v___x_2806_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2756_ = v___y_2780_;
v___y_2757_ = v___y_2781_;
v___y_2758_ = v___y_2783_;
v___y_2759_ = v___y_2782_;
v___y_2760_ = v___y_2784_;
v___y_2761_ = v___y_2785_;
v___y_2762_ = v___y_2786_;
v___y_2763_ = v___y_2787_;
v___y_2764_ = v___y_2788_;
v___y_2765_ = v___y_2792_;
v___y_2766_ = v___y_2793_;
v___y_2767_ = v___y_2791_;
v___y_2768_ = v___y_2790_;
v___y_2769_ = v___x_2800_;
v___y_2770_ = v___y_2794_;
v___y_2771_ = v___y_2796_;
v___y_2772_ = v___y_2795_;
v___y_2773_ = v___y_2797_;
v___y_2774_ = v___x_2806_;
goto v___jp_2755_;
}
}
v___jp_2807_:
{
lean_object* v___x_2823_; lean_object* v_a_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2823_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2811_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_array_get_size(v___y_2809_);
v___x_2826_ = lean_nat_dec_eq(v___x_2825_, v___x_2435_);
if (v___x_2826_ == 0)
{
if (lean_obj_tag(v___y_2812_) == 0)
{
lean_object* v_ref_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_ref_2827_ = lean_ctor_get(v___y_2821_, 2);
v___x_2828_ = l_Lean_SourceInfo_fromRef(v_ref_2827_, v___x_2826_);
v___x_2829_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2830_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_2829_);
v___x_2831_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_2832_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2835_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2813_) == 1)
{
lean_object* v_val_2836_; lean_object* v___x_2837_; 
v_val_2836_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v___y_2813_, 1);
v___x_2837_ = l_Array_mkArray1___redArg(v_val_2836_);
v___y_2613_ = v___y_2809_;
v___y_2614_ = v___y_2818_;
v___y_2615_ = v___x_2833_;
v___y_2616_ = v___x_2830_;
v___y_2617_ = v___y_2812_;
v___y_2618_ = v___x_2834_;
v___y_2619_ = v_stxForExecution_2814_;
v___y_2620_ = v___y_2815_;
v___y_2621_ = v___y_2821_;
v___y_2622_ = v___y_2820_;
v___y_2623_ = v___y_2808_;
v___y_2624_ = v___y_2817_;
v___y_2625_ = v___y_2816_;
v___y_2626_ = v_a_2824_;
v___y_2627_ = v___y_2810_;
v___y_2628_ = v___x_2835_;
v___y_2629_ = v___y_2819_;
v___y_2630_ = v___x_2828_;
v___y_2631_ = v___y_2822_;
v___y_2632_ = v___x_2837_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2838_; 
lean_dec(v___y_2813_);
v___x_2838_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2613_ = v___y_2809_;
v___y_2614_ = v___y_2818_;
v___y_2615_ = v___x_2833_;
v___y_2616_ = v___x_2830_;
v___y_2617_ = v___y_2812_;
v___y_2618_ = v___x_2834_;
v___y_2619_ = v_stxForExecution_2814_;
v___y_2620_ = v___y_2815_;
v___y_2621_ = v___y_2821_;
v___y_2622_ = v___y_2820_;
v___y_2623_ = v___y_2808_;
v___y_2624_ = v___y_2817_;
v___y_2625_ = v___y_2816_;
v___y_2626_ = v_a_2824_;
v___y_2627_ = v___y_2810_;
v___y_2628_ = v___x_2835_;
v___y_2629_ = v___y_2819_;
v___y_2630_ = v___x_2828_;
v___y_2631_ = v___y_2822_;
v___y_2632_ = v___x_2838_;
goto v___jp_2612_;
}
}
else
{
lean_object* v_ref_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_ref_2839_ = lean_ctor_get(v___y_2821_, 2);
v___x_2840_ = l_Lean_SourceInfo_fromRef(v_ref_2839_, v___x_2826_);
v___x_2841_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2842_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_2841_);
v___x_2843_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_2844_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2847_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2813_) == 1)
{
lean_object* v_val_2848_; lean_object* v___x_2849_; 
v_val_2848_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v___y_2813_, 1);
v___x_2849_ = l_Array_mkArray1___redArg(v_val_2848_);
v___y_2675_ = v___y_2809_;
v___y_2676_ = v___y_2818_;
v___y_2677_ = v___x_2847_;
v___y_2678_ = v___x_2845_;
v___y_2679_ = v___x_2842_;
v___y_2680_ = v___y_2812_;
v___y_2681_ = v_stxForExecution_2814_;
v___y_2682_ = v___y_2815_;
v___y_2683_ = v___y_2821_;
v___y_2684_ = v___y_2820_;
v___y_2685_ = v___y_2808_;
v___y_2686_ = v___y_2817_;
v___y_2687_ = v___y_2816_;
v___y_2688_ = v_a_2824_;
v___y_2689_ = v___y_2810_;
v___y_2690_ = v___x_2840_;
v___y_2691_ = v___y_2819_;
v___y_2692_ = v___x_2846_;
v___y_2693_ = v___y_2822_;
v___y_2694_ = v___x_2849_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2850_; 
lean_dec(v___y_2813_);
v___x_2850_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2675_ = v___y_2809_;
v___y_2676_ = v___y_2818_;
v___y_2677_ = v___x_2847_;
v___y_2678_ = v___x_2845_;
v___y_2679_ = v___x_2842_;
v___y_2680_ = v___y_2812_;
v___y_2681_ = v_stxForExecution_2814_;
v___y_2682_ = v___y_2815_;
v___y_2683_ = v___y_2821_;
v___y_2684_ = v___y_2820_;
v___y_2685_ = v___y_2808_;
v___y_2686_ = v___y_2817_;
v___y_2687_ = v___y_2816_;
v___y_2688_ = v_a_2824_;
v___y_2689_ = v___y_2810_;
v___y_2690_ = v___x_2840_;
v___y_2691_ = v___y_2819_;
v___y_2692_ = v___x_2846_;
v___y_2693_ = v___y_2822_;
v___y_2694_ = v___x_2850_;
goto v___jp_2674_;
}
}
}
else
{
lean_dec_ref(v___y_2809_);
if (lean_obj_tag(v___y_2812_) == 0)
{
lean_object* v_ref_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_ref_2851_ = lean_ctor_get(v___y_2821_, 2);
v___x_2852_ = 0;
v___x_2853_ = l_Lean_SourceInfo_fromRef(v_ref_2851_, v___x_2852_);
v___x_2854_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2855_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_2854_);
v___x_2856_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_2857_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2860_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2813_) == 1)
{
lean_object* v_val_2861_; lean_object* v___x_2862_; 
v_val_2861_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v___y_2813_, 1);
v___x_2862_ = l_Array_mkArray1___redArg(v_val_2861_);
v___y_2728_ = v___x_2859_;
v___y_2729_ = v___x_2855_;
v___y_2730_ = v___y_2818_;
v___y_2731_ = v___y_2812_;
v___y_2732_ = v___x_2853_;
v___y_2733_ = v_stxForExecution_2814_;
v___y_2734_ = v___y_2815_;
v___y_2735_ = v___y_2821_;
v___y_2736_ = v___x_2858_;
v___y_2737_ = v___y_2820_;
v___y_2738_ = v___y_2808_;
v___y_2739_ = v___y_2817_;
v___y_2740_ = v___y_2816_;
v___y_2741_ = v_a_2824_;
v___y_2742_ = v___y_2810_;
v___y_2743_ = v___y_2819_;
v___y_2744_ = v___x_2860_;
v___y_2745_ = v___y_2822_;
v___y_2746_ = v___x_2862_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2863_; 
lean_dec(v___y_2813_);
v___x_2863_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2728_ = v___x_2859_;
v___y_2729_ = v___x_2855_;
v___y_2730_ = v___y_2818_;
v___y_2731_ = v___y_2812_;
v___y_2732_ = v___x_2853_;
v___y_2733_ = v_stxForExecution_2814_;
v___y_2734_ = v___y_2815_;
v___y_2735_ = v___y_2821_;
v___y_2736_ = v___x_2858_;
v___y_2737_ = v___y_2820_;
v___y_2738_ = v___y_2808_;
v___y_2739_ = v___y_2817_;
v___y_2740_ = v___y_2816_;
v___y_2741_ = v_a_2824_;
v___y_2742_ = v___y_2810_;
v___y_2743_ = v___y_2819_;
v___y_2744_ = v___x_2860_;
v___y_2745_ = v___y_2822_;
v___y_2746_ = v___x_2863_;
goto v___jp_2727_;
}
}
else
{
lean_object* v_ref_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_ref_2864_ = lean_ctor_get(v___y_2821_, 2);
v___x_2865_ = 0;
v___x_2866_ = l_Lean_SourceInfo_fromRef(v_ref_2864_, v___x_2865_);
v___x_2867_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2868_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_2867_);
v___x_2869_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_2870_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2873_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2813_) == 1)
{
lean_object* v_val_2874_; lean_object* v___x_2875_; 
v_val_2874_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v___y_2813_, 1);
v___x_2875_ = l_Array_mkArray1___redArg(v_val_2874_);
v___y_2780_ = v___y_2818_;
v___y_2781_ = v___x_2871_;
v___y_2782_ = v___x_2866_;
v___y_2783_ = v___y_2812_;
v___y_2784_ = v___x_2873_;
v___y_2785_ = v_stxForExecution_2814_;
v___y_2786_ = v___y_2815_;
v___y_2787_ = v___y_2821_;
v___y_2788_ = v___y_2820_;
v___y_2789_ = v___y_2808_;
v___y_2790_ = v___y_2817_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2810_;
v___y_2793_ = v_a_2824_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___x_2868_;
v___y_2796_ = v___x_2872_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___x_2875_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2876_; 
lean_dec(v___y_2813_);
v___x_2876_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2780_ = v___y_2818_;
v___y_2781_ = v___x_2871_;
v___y_2782_ = v___x_2866_;
v___y_2783_ = v___y_2812_;
v___y_2784_ = v___x_2873_;
v___y_2785_ = v_stxForExecution_2814_;
v___y_2786_ = v___y_2815_;
v___y_2787_ = v___y_2821_;
v___y_2788_ = v___y_2820_;
v___y_2789_ = v___y_2808_;
v___y_2790_ = v___y_2817_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2810_;
v___y_2793_ = v_a_2824_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___x_2868_;
v___y_2796_ = v___x_2872_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___x_2876_;
goto v___jp_2779_;
}
}
}
}
v___jp_2877_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_inc_ref_n(v___y_2897_, 2);
v___x_2899_ = l_Array_append___redArg(v___y_2897_, v___y_2898_);
lean_dec_ref(v___y_2898_);
lean_inc_n(v___y_2883_, 3);
lean_inc_n(v___y_2878_, 5);
v___x_2900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2900_, 0, v___y_2878_);
lean_ctor_set(v___x_2900_, 1, v___y_2883_);
lean_ctor_set(v___x_2900_, 2, v___x_2899_);
v___x_2901_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___y_2878_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2904_ = l_Lean_Syntax_SepArray_ofElems(v___x_2903_, v___y_2879_);
v___x_2905_ = l_Array_append___redArg(v___y_2897_, v___x_2904_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2906_, 0, v___y_2878_);
lean_ctor_set(v___x_2906_, 1, v___y_2883_);
lean_ctor_set(v___x_2906_, 2, v___x_2905_);
v___x_2907_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___y_2878_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Lean_Syntax_node3(v___y_2878_, v___y_2883_, v___x_2902_, v___x_2906_, v___x_2908_);
lean_inc(v___y_2882_);
v___x_2910_ = l_Lean_Syntax_node5(v___y_2878_, v___y_2894_, v___y_2885_, v___y_2882_, v___y_2880_, v___x_2900_, v___x_2909_);
v___y_2808_ = v___y_2891_;
v___y_2809_ = v___y_2879_;
v___y_2810_ = v___y_2890_;
v___y_2811_ = v___y_2882_;
v___y_2812_ = v___y_2881_;
v___y_2813_ = v___y_2886_;
v_stxForExecution_2814_ = v___x_2910_;
v___y_2815_ = v___y_2889_;
v___y_2816_ = v___y_2895_;
v___y_2817_ = v___y_2892_;
v___y_2818_ = v___y_2888_;
v___y_2819_ = v___y_2884_;
v___y_2820_ = v___y_2896_;
v___y_2821_ = v___y_2893_;
v___y_2822_ = v___y_2887_;
goto v___jp_2807_;
}
v___jp_2911_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_inc_ref(v___y_2930_);
v___x_2932_ = l_Array_append___redArg(v___y_2930_, v___y_2931_);
lean_dec_ref(v___y_2931_);
lean_inc(v___y_2916_);
lean_inc(v___y_2912_);
v___x_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2933_, 0, v___y_2912_);
lean_ctor_set(v___x_2933_, 1, v___y_2916_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
if (lean_obj_tag(v___y_2924_) == 1)
{
lean_object* v_val_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_val_2934_ = lean_ctor_get(v___y_2924_, 0);
v___x_2935_ = l_Lean_SourceInfo_fromRef(v_val_2934_, v___x_2420_);
v___x_2936_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = l_Array_mkArray1___redArg(v___x_2937_);
v___y_2878_ = v___y_2912_;
v___y_2879_ = v___y_2913_;
v___y_2880_ = v___x_2933_;
v___y_2881_ = v___y_2914_;
v___y_2882_ = v___y_2915_;
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2917_;
v___y_2885_ = v___y_2918_;
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___y_2920_;
v___y_2888_ = v___y_2921_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2925_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___y_2923_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2928_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v___x_2938_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2939_; 
v___x_2939_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2878_ = v___y_2912_;
v___y_2879_ = v___y_2913_;
v___y_2880_ = v___x_2933_;
v___y_2881_ = v___y_2914_;
v___y_2882_ = v___y_2915_;
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2917_;
v___y_2885_ = v___y_2918_;
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___y_2920_;
v___y_2888_ = v___y_2921_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2925_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___y_2923_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2928_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v___x_2939_;
goto v___jp_2877_;
}
}
v___jp_2940_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_inc_ref_n(v___y_2954_, 2);
v___x_2962_ = l_Array_append___redArg(v___y_2954_, v___y_2961_);
lean_dec_ref(v___y_2961_);
lean_inc_n(v___y_2942_, 3);
lean_inc_n(v___y_2957_, 5);
v___x_2963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2963_, 0, v___y_2957_);
lean_ctor_set(v___x_2963_, 1, v___y_2942_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___y_2957_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2967_ = l_Lean_Syntax_SepArray_ofElems(v___x_2966_, v___y_2941_);
v___x_2968_ = l_Array_append___redArg(v___y_2954_, v___x_2967_);
lean_dec_ref(v___x_2967_);
v___x_2969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2969_, 0, v___y_2957_);
lean_ctor_set(v___x_2969_, 1, v___y_2942_);
lean_ctor_set(v___x_2969_, 2, v___x_2968_);
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2957_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = l_Lean_Syntax_node3(v___y_2957_, v___y_2942_, v___x_2965_, v___x_2969_, v___x_2971_);
lean_inc(v___y_2944_);
v___x_2973_ = l_Lean_Syntax_node5(v___y_2957_, v___y_2958_, v___y_2955_, v___y_2944_, v___y_2948_, v___x_2963_, v___x_2972_);
v___y_2808_ = v___y_2952_;
v___y_2809_ = v___y_2941_;
v___y_2810_ = v___y_2951_;
v___y_2811_ = v___y_2944_;
v___y_2812_ = v___y_2943_;
v___y_2813_ = v___y_2946_;
v_stxForExecution_2814_ = v___x_2973_;
v___y_2815_ = v___y_2950_;
v___y_2816_ = v___y_2959_;
v___y_2817_ = v___y_2953_;
v___y_2818_ = v___y_2949_;
v___y_2819_ = v___y_2945_;
v___y_2820_ = v___y_2960_;
v___y_2821_ = v___y_2956_;
v___y_2822_ = v___y_2947_;
goto v___jp_2807_;
}
v___jp_2974_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_inc_ref(v___y_2988_);
v___x_2995_ = l_Array_append___redArg(v___y_2988_, v___y_2994_);
lean_dec_ref(v___y_2994_);
lean_inc(v___y_2976_);
lean_inc(v___y_2990_);
v___x_2996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2996_, 0, v___y_2990_);
lean_ctor_set(v___x_2996_, 1, v___y_2976_);
lean_ctor_set(v___x_2996_, 2, v___x_2995_);
if (lean_obj_tag(v___y_2985_) == 1)
{
lean_object* v_val_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_val_2997_ = lean_ctor_get(v___y_2985_, 0);
v___x_2998_ = l_Lean_SourceInfo_fromRef(v_val_2997_, v___x_2420_);
v___x_2999_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Array_mkArray1___redArg(v___x_3000_);
v___y_2941_ = v___y_2975_;
v___y_2942_ = v___y_2976_;
v___y_2943_ = v___y_2977_;
v___y_2944_ = v___y_2978_;
v___y_2945_ = v___y_2979_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___x_2996_;
v___y_2949_ = v___y_2982_;
v___y_2950_ = v___y_2983_;
v___y_2951_ = v___y_2986_;
v___y_2952_ = v___y_2985_;
v___y_2953_ = v___y_2984_;
v___y_2954_ = v___y_2988_;
v___y_2955_ = v___y_2987_;
v___y_2956_ = v___y_2989_;
v___y_2957_ = v___y_2990_;
v___y_2958_ = v___y_2992_;
v___y_2959_ = v___y_2991_;
v___y_2960_ = v___y_2993_;
v___y_2961_ = v___x_3001_;
goto v___jp_2940_;
}
else
{
lean_object* v___x_3002_; 
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2941_ = v___y_2975_;
v___y_2942_ = v___y_2976_;
v___y_2943_ = v___y_2977_;
v___y_2944_ = v___y_2978_;
v___y_2945_ = v___y_2979_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___x_2996_;
v___y_2949_ = v___y_2982_;
v___y_2950_ = v___y_2983_;
v___y_2951_ = v___y_2986_;
v___y_2952_ = v___y_2985_;
v___y_2953_ = v___y_2984_;
v___y_2954_ = v___y_2988_;
v___y_2955_ = v___y_2987_;
v___y_2956_ = v___y_2989_;
v___y_2957_ = v___y_2990_;
v___y_2958_ = v___y_2992_;
v___y_2959_ = v___y_2991_;
v___y_2960_ = v___y_2993_;
v___y_2961_ = v___x_3002_;
goto v___jp_2940_;
}
}
v___jp_3003_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_inc_ref_n(v___y_3005_, 2);
v___x_3025_ = l_Array_append___redArg(v___y_3005_, v___y_3024_);
lean_dec_ref(v___y_3024_);
lean_inc_n(v___y_3020_, 2);
lean_inc_n(v___y_3022_, 2);
v___x_3026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3026_, 0, v___y_3022_);
lean_ctor_set(v___x_3026_, 1, v___y_3020_);
lean_ctor_set(v___x_3026_, 2, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v___y_3022_);
lean_ctor_set(v___x_3027_, 1, v___y_3020_);
lean_ctor_set(v___x_3027_, 2, v___y_3005_);
lean_inc(v___y_3008_);
v___x_3028_ = l_Lean_Syntax_node5(v___y_3022_, v___y_3021_, v___y_3018_, v___y_3008_, v___y_3006_, v___x_3026_, v___x_3027_);
v___y_2808_ = v___y_3015_;
v___y_2809_ = v___y_3004_;
v___y_2810_ = v___y_3014_;
v___y_2811_ = v___y_3008_;
v___y_2812_ = v___y_3007_;
v___y_2813_ = v___y_3010_;
v_stxForExecution_2814_ = v___x_3028_;
v___y_2815_ = v___y_3013_;
v___y_2816_ = v___y_3019_;
v___y_2817_ = v___y_3016_;
v___y_2818_ = v___y_3012_;
v___y_2819_ = v___y_3009_;
v___y_2820_ = v___y_3023_;
v___y_2821_ = v___y_3017_;
v___y_2822_ = v___y_3011_;
goto v___jp_2807_;
}
v___jp_3029_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_inc_ref(v___y_3031_);
v___x_3050_ = l_Array_append___redArg(v___y_3031_, v___y_3049_);
lean_dec_ref(v___y_3049_);
lean_inc(v___y_3046_);
lean_inc(v___y_3048_);
v___x_3051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___y_3048_);
lean_ctor_set(v___x_3051_, 1, v___y_3046_);
lean_ctor_set(v___x_3051_, 2, v___x_3050_);
if (lean_obj_tag(v___y_3040_) == 1)
{
lean_object* v_val_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_val_3052_ = lean_ctor_get(v___y_3040_, 0);
v___x_3053_ = l_Lean_SourceInfo_fromRef(v_val_3052_, v___x_2420_);
v___x_3054_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = l_Array_mkArray1___redArg(v___x_3055_);
v___y_3004_ = v___y_3030_;
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___x_3051_;
v___y_3007_ = v___y_3032_;
v___y_3008_ = v___y_3033_;
v___y_3009_ = v___y_3034_;
v___y_3010_ = v___y_3035_;
v___y_3011_ = v___y_3036_;
v___y_3012_ = v___y_3037_;
v___y_3013_ = v___y_3038_;
v___y_3014_ = v___y_3041_;
v___y_3015_ = v___y_3040_;
v___y_3016_ = v___y_3039_;
v___y_3017_ = v___y_3043_;
v___y_3018_ = v___y_3042_;
v___y_3019_ = v___y_3044_;
v___y_3020_ = v___y_3046_;
v___y_3021_ = v___y_3045_;
v___y_3022_ = v___y_3048_;
v___y_3023_ = v___y_3047_;
v___y_3024_ = v___x_3056_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3004_ = v___y_3030_;
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___x_3051_;
v___y_3007_ = v___y_3032_;
v___y_3008_ = v___y_3033_;
v___y_3009_ = v___y_3034_;
v___y_3010_ = v___y_3035_;
v___y_3011_ = v___y_3036_;
v___y_3012_ = v___y_3037_;
v___y_3013_ = v___y_3038_;
v___y_3014_ = v___y_3041_;
v___y_3015_ = v___y_3040_;
v___y_3016_ = v___y_3039_;
v___y_3017_ = v___y_3043_;
v___y_3018_ = v___y_3042_;
v___y_3019_ = v___y_3044_;
v___y_3020_ = v___y_3046_;
v___y_3021_ = v___y_3045_;
v___y_3022_ = v___y_3048_;
v___y_3023_ = v___y_3047_;
v___y_3024_ = v___x_3057_;
goto v___jp_3003_;
}
}
v___jp_3058_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc_ref_n(v___y_3078_, 2);
v___x_3080_ = l_Array_append___redArg(v___y_3078_, v___y_3079_);
lean_dec_ref(v___y_3079_);
lean_inc_n(v___y_3061_, 2);
lean_inc_n(v___y_3063_, 2);
v___x_3081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3063_);
lean_ctor_set(v___x_3081_, 1, v___y_3061_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___y_3063_);
lean_ctor_set(v___x_3082_, 1, v___y_3061_);
lean_ctor_set(v___x_3082_, 2, v___y_3078_);
lean_inc(v___y_3064_);
v___x_3083_ = l_Lean_Syntax_node5(v___y_3063_, v___y_3075_, v___y_3076_, v___y_3064_, v___y_3060_, v___x_3081_, v___x_3082_);
v___y_2808_ = v___y_3071_;
v___y_2809_ = v___y_3059_;
v___y_2810_ = v___y_3070_;
v___y_2811_ = v___y_3064_;
v___y_2812_ = v___y_3062_;
v___y_2813_ = v___y_3066_;
v_stxForExecution_2814_ = v___x_3083_;
v___y_2815_ = v___y_3069_;
v___y_2816_ = v___y_3074_;
v___y_2817_ = v___y_3072_;
v___y_2818_ = v___y_3068_;
v___y_2819_ = v___y_3065_;
v___y_2820_ = v___y_3077_;
v___y_2821_ = v___y_3073_;
v___y_2822_ = v___y_3067_;
goto v___jp_2807_;
}
v___jp_3084_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_inc_ref(v___y_3103_);
v___x_3105_ = l_Array_append___redArg(v___y_3103_, v___y_3104_);
lean_dec_ref(v___y_3104_);
lean_inc(v___y_3086_);
lean_inc(v___y_3087_);
v___x_3106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3106_, 0, v___y_3087_);
lean_ctor_set(v___x_3106_, 1, v___y_3086_);
lean_ctor_set(v___x_3106_, 2, v___x_3105_);
if (lean_obj_tag(v___y_3096_) == 1)
{
lean_object* v_val_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v_val_3107_ = lean_ctor_get(v___y_3096_, 0);
v___x_3108_ = l_Lean_SourceInfo_fromRef(v_val_3107_, v___x_2420_);
v___x_3109_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Array_mkArray1___redArg(v___x_3110_);
v___y_3059_ = v___y_3085_;
v___y_3060_ = v___x_3106_;
v___y_3061_ = v___y_3086_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3087_;
v___y_3064_ = v___y_3089_;
v___y_3065_ = v___y_3090_;
v___y_3066_ = v___y_3091_;
v___y_3067_ = v___y_3092_;
v___y_3068_ = v___y_3093_;
v___y_3069_ = v___y_3094_;
v___y_3070_ = v___y_3097_;
v___y_3071_ = v___y_3096_;
v___y_3072_ = v___y_3095_;
v___y_3073_ = v___y_3098_;
v___y_3074_ = v___y_3099_;
v___y_3075_ = v___y_3100_;
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3101_;
v___y_3078_ = v___y_3103_;
v___y_3079_ = v___x_3111_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3112_; 
v___x_3112_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3059_ = v___y_3085_;
v___y_3060_ = v___x_3106_;
v___y_3061_ = v___y_3086_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3087_;
v___y_3064_ = v___y_3089_;
v___y_3065_ = v___y_3090_;
v___y_3066_ = v___y_3091_;
v___y_3067_ = v___y_3092_;
v___y_3068_ = v___y_3093_;
v___y_3069_ = v___y_3094_;
v___y_3070_ = v___y_3097_;
v___y_3071_ = v___y_3096_;
v___y_3072_ = v___y_3095_;
v___y_3073_ = v___y_3098_;
v___y_3074_ = v___y_3099_;
v___y_3075_ = v___y_3100_;
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3101_;
v___y_3078_ = v___y_3103_;
v___y_3079_ = v___x_3112_;
goto v___jp_3058_;
}
}
v___jp_3113_:
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = lean_array_get_size(v_argsArray_3119_);
v___x_3129_ = lean_nat_dec_eq(v___x_3128_, v___x_2435_);
if (v___x_3129_ == 0)
{
if (lean_obj_tag(v___y_3116_) == 0)
{
lean_object* v_ref_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_ref_3130_ = lean_ctor_get(v___y_3126_, 2);
v___x_3131_ = l_Lean_SourceInfo_fromRef(v_ref_3130_, v___x_3129_);
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3133_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3132_);
v___x_3134_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_3135_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3138_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3118_) == 1)
{
lean_object* v_val_3139_; lean_object* v___x_3140_; 
v_val_3139_ = lean_ctor_get(v___y_3118_, 0);
lean_inc(v_val_3139_);
v___x_3140_ = l_Array_mkArray1___redArg(v_val_3139_);
v___y_2912_ = v___x_3131_;
v___y_2913_ = v_argsArray_3119_;
v___y_2914_ = v___y_3116_;
v___y_2915_ = v___y_3117_;
v___y_2916_ = v___x_3137_;
v___y_2917_ = v___y_3124_;
v___y_2918_ = v___x_3136_;
v___y_2919_ = v___y_3118_;
v___y_2920_ = v___y_3127_;
v___y_2921_ = v___y_3123_;
v___y_2922_ = v___y_3120_;
v___y_2923_ = v___y_3122_;
v___y_2924_ = v___y_3115_;
v___y_2925_ = v___y_3114_;
v___y_2926_ = v___x_3133_;
v___y_2927_ = v___y_3126_;
v___y_2928_ = v___y_3121_;
v___y_2929_ = v___y_3125_;
v___y_2930_ = v___x_3138_;
v___y_2931_ = v___x_3140_;
goto v___jp_2911_;
}
else
{
lean_object* v___x_3141_; 
v___x_3141_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2912_ = v___x_3131_;
v___y_2913_ = v_argsArray_3119_;
v___y_2914_ = v___y_3116_;
v___y_2915_ = v___y_3117_;
v___y_2916_ = v___x_3137_;
v___y_2917_ = v___y_3124_;
v___y_2918_ = v___x_3136_;
v___y_2919_ = v___y_3118_;
v___y_2920_ = v___y_3127_;
v___y_2921_ = v___y_3123_;
v___y_2922_ = v___y_3120_;
v___y_2923_ = v___y_3122_;
v___y_2924_ = v___y_3115_;
v___y_2925_ = v___y_3114_;
v___y_2926_ = v___x_3133_;
v___y_2927_ = v___y_3126_;
v___y_2928_ = v___y_3121_;
v___y_2929_ = v___y_3125_;
v___y_2930_ = v___x_3138_;
v___y_2931_ = v___x_3141_;
goto v___jp_2911_;
}
}
else
{
lean_object* v_ref_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_ref_3142_ = lean_ctor_get(v___y_3126_, 2);
v___x_3143_ = l_Lean_SourceInfo_fromRef(v_ref_3142_, v___x_3129_);
v___x_3144_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3145_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3144_);
v___x_3146_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_3147_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3150_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3118_) == 1)
{
lean_object* v_val_3151_; lean_object* v___x_3152_; 
v_val_3151_ = lean_ctor_get(v___y_3118_, 0);
lean_inc(v_val_3151_);
v___x_3152_ = l_Array_mkArray1___redArg(v_val_3151_);
v___y_2975_ = v_argsArray_3119_;
v___y_2976_ = v___x_3149_;
v___y_2977_ = v___y_3116_;
v___y_2978_ = v___y_3117_;
v___y_2979_ = v___y_3124_;
v___y_2980_ = v___y_3118_;
v___y_2981_ = v___y_3127_;
v___y_2982_ = v___y_3123_;
v___y_2983_ = v___y_3120_;
v___y_2984_ = v___y_3122_;
v___y_2985_ = v___y_3115_;
v___y_2986_ = v___y_3114_;
v___y_2987_ = v___x_3148_;
v___y_2988_ = v___x_3150_;
v___y_2989_ = v___y_3126_;
v___y_2990_ = v___x_3143_;
v___y_2991_ = v___y_3121_;
v___y_2992_ = v___x_3145_;
v___y_2993_ = v___y_3125_;
v___y_2994_ = v___x_3152_;
goto v___jp_2974_;
}
else
{
lean_object* v___x_3153_; 
v___x_3153_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2975_ = v_argsArray_3119_;
v___y_2976_ = v___x_3149_;
v___y_2977_ = v___y_3116_;
v___y_2978_ = v___y_3117_;
v___y_2979_ = v___y_3124_;
v___y_2980_ = v___y_3118_;
v___y_2981_ = v___y_3127_;
v___y_2982_ = v___y_3123_;
v___y_2983_ = v___y_3120_;
v___y_2984_ = v___y_3122_;
v___y_2985_ = v___y_3115_;
v___y_2986_ = v___y_3114_;
v___y_2987_ = v___x_3148_;
v___y_2988_ = v___x_3150_;
v___y_2989_ = v___y_3126_;
v___y_2990_ = v___x_3143_;
v___y_2991_ = v___y_3121_;
v___y_2992_ = v___x_3145_;
v___y_2993_ = v___y_3125_;
v___y_2994_ = v___x_3153_;
goto v___jp_2974_;
}
}
}
else
{
if (lean_obj_tag(v___y_3116_) == 0)
{
lean_object* v_ref_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_ref_3154_ = lean_ctor_get(v___y_3126_, 2);
v___x_3155_ = 0;
v___x_3156_ = l_Lean_SourceInfo_fromRef(v_ref_3154_, v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3158_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3157_);
v___x_3159_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_3160_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3163_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3118_) == 1)
{
lean_object* v_val_3164_; lean_object* v___x_3165_; 
v_val_3164_ = lean_ctor_get(v___y_3118_, 0);
lean_inc(v_val_3164_);
v___x_3165_ = l_Array_mkArray1___redArg(v_val_3164_);
v___y_3030_ = v_argsArray_3119_;
v___y_3031_ = v___x_3163_;
v___y_3032_ = v___y_3116_;
v___y_3033_ = v___y_3117_;
v___y_3034_ = v___y_3124_;
v___y_3035_ = v___y_3118_;
v___y_3036_ = v___y_3127_;
v___y_3037_ = v___y_3123_;
v___y_3038_ = v___y_3120_;
v___y_3039_ = v___y_3122_;
v___y_3040_ = v___y_3115_;
v___y_3041_ = v___y_3114_;
v___y_3042_ = v___x_3161_;
v___y_3043_ = v___y_3126_;
v___y_3044_ = v___y_3121_;
v___y_3045_ = v___x_3158_;
v___y_3046_ = v___x_3162_;
v___y_3047_ = v___y_3125_;
v___y_3048_ = v___x_3156_;
v___y_3049_ = v___x_3165_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3166_; 
v___x_3166_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3030_ = v_argsArray_3119_;
v___y_3031_ = v___x_3163_;
v___y_3032_ = v___y_3116_;
v___y_3033_ = v___y_3117_;
v___y_3034_ = v___y_3124_;
v___y_3035_ = v___y_3118_;
v___y_3036_ = v___y_3127_;
v___y_3037_ = v___y_3123_;
v___y_3038_ = v___y_3120_;
v___y_3039_ = v___y_3122_;
v___y_3040_ = v___y_3115_;
v___y_3041_ = v___y_3114_;
v___y_3042_ = v___x_3161_;
v___y_3043_ = v___y_3126_;
v___y_3044_ = v___y_3121_;
v___y_3045_ = v___x_3158_;
v___y_3046_ = v___x_3162_;
v___y_3047_ = v___y_3125_;
v___y_3048_ = v___x_3156_;
v___y_3049_ = v___x_3166_;
goto v___jp_3029_;
}
}
else
{
lean_object* v_ref_3167_; uint8_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_ref_3167_ = lean_ctor_get(v___y_3126_, 2);
v___x_3168_ = 0;
v___x_3169_ = l_Lean_SourceInfo_fromRef(v_ref_3167_, v___x_3168_);
v___x_3170_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3171_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3170_);
v___x_3172_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2420_);
v___x_3173_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3176_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3118_) == 1)
{
lean_object* v_val_3177_; lean_object* v___x_3178_; 
v_val_3177_ = lean_ctor_get(v___y_3118_, 0);
lean_inc(v_val_3177_);
v___x_3178_ = l_Array_mkArray1___redArg(v_val_3177_);
v___y_3085_ = v_argsArray_3119_;
v___y_3086_ = v___x_3175_;
v___y_3087_ = v___x_3169_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3118_;
v___y_3092_ = v___y_3127_;
v___y_3093_ = v___y_3123_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3122_;
v___y_3096_ = v___y_3115_;
v___y_3097_ = v___y_3114_;
v___y_3098_ = v___y_3126_;
v___y_3099_ = v___y_3121_;
v___y_3100_ = v___x_3171_;
v___y_3101_ = v___y_3125_;
v___y_3102_ = v___x_3174_;
v___y_3103_ = v___x_3176_;
v___y_3104_ = v___x_3178_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3179_; 
v___x_3179_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3085_ = v_argsArray_3119_;
v___y_3086_ = v___x_3175_;
v___y_3087_ = v___x_3169_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3124_;
v___y_3091_ = v___y_3118_;
v___y_3092_ = v___y_3127_;
v___y_3093_ = v___y_3123_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3122_;
v___y_3096_ = v___y_3115_;
v___y_3097_ = v___y_3114_;
v___y_3098_ = v___y_3126_;
v___y_3099_ = v___y_3121_;
v___y_3100_ = v___x_3171_;
v___y_3101_ = v___y_3125_;
v___y_3102_ = v___x_3174_;
v___y_3103_ = v___x_3176_;
v___y_3104_ = v___x_3179_;
goto v___jp_3084_;
}
}
}
}
v___jp_3180_:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3184_, v___y_3191_, v___y_3190_, v___y_3181_, v___y_3194_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_Lean_LibrarySuggestions_select(v_a_3197_, v___y_3195_, v___y_3191_, v___y_3190_, v___y_3181_, v___y_3194_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; size_t v_sz_3200_; size_t v___x_3201_; lean_object* v___x_3202_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v_sz_3200_ = lean_array_size(v_a_3199_);
v___x_3201_ = ((size_t)0ULL);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3199_, v_sz_3200_, v___x_3201_, v___y_3182_, v___y_3193_, v___y_3184_, v___y_3192_, v___y_3189_, v___y_3191_, v___y_3190_, v___y_3181_, v___y_3194_);
lean_dec(v_a_3199_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
v___y_3114_ = v___y_3187_;
v___y_3115_ = v___y_3188_;
v___y_3116_ = v___y_3185_;
v___y_3117_ = v___y_3183_;
v___y_3118_ = v___y_3186_;
v_argsArray_3119_ = v_a_3203_;
v___y_3120_ = v___y_3193_;
v___y_3121_ = v___y_3184_;
v___y_3122_ = v___y_3192_;
v___y_3123_ = v___y_3189_;
v___y_3124_ = v___y_3191_;
v___y_3125_ = v___y_3190_;
v___y_3126_ = v___y_3181_;
v___y_3127_ = v___y_3194_;
goto v___jp_3113_;
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3183_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v_a_3204_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3202_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3202_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v_a_3212_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3198_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3198_);
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
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v_a_3220_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3196_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3196_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
v___jp_3228_:
{
lean_object* v_config_3244_; uint8_t v_suggestions_3245_; 
v_config_3244_ = lean_ctor_get(v___y_3234_, 0);
lean_inc_ref(v_config_3244_);
lean_dec_ref(v___y_3234_);
v_suggestions_3245_ = lean_ctor_get_uint8(v_config_3244_, sizeof(void*)*3 + 26);
if (v_suggestions_3245_ == 0)
{
lean_dec_ref(v_config_3244_);
lean_dec_ref(v___f_2424_);
v___y_3114_ = v___y_3235_;
v___y_3115_ = v___y_3236_;
v___y_3116_ = v___y_3232_;
v___y_3117_ = v___y_3230_;
v___y_3118_ = v___y_3233_;
v_argsArray_3119_ = v___y_3243_;
v___y_3120_ = v___y_3241_;
v___y_3121_ = v___y_3231_;
v___y_3122_ = v___y_3240_;
v___y_3123_ = v___y_3237_;
v___y_3124_ = v___y_3239_;
v___y_3125_ = v___y_3238_;
v___y_3126_ = v___y_3229_;
v___y_3127_ = v___y_3242_;
goto v___jp_3113_;
}
else
{
lean_object* v_maxSuggestions_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_maxSuggestions_3246_ = lean_ctor_get(v_config_3244_, 2);
lean_inc(v_maxSuggestions_3246_);
lean_dec_ref(v_config_3244_);
v___x_3247_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3248_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3246_) == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_unsigned_to_nat(100u);
v___x_3250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v___x_3247_);
lean_ctor_set(v___x_3250_, 2, v___f_2424_);
lean_ctor_set(v___x_3250_, 3, v___x_3248_);
v___y_3181_ = v___y_3229_;
v___y_3182_ = v___y_3243_;
v___y_3183_ = v___y_3230_;
v___y_3184_ = v___y_3231_;
v___y_3185_ = v___y_3232_;
v___y_3186_ = v___y_3233_;
v___y_3187_ = v___y_3235_;
v___y_3188_ = v___y_3236_;
v___y_3189_ = v___y_3237_;
v___y_3190_ = v___y_3238_;
v___y_3191_ = v___y_3239_;
v___y_3192_ = v___y_3240_;
v___y_3193_ = v___y_3241_;
v___y_3194_ = v___y_3242_;
v___y_3195_ = v___x_3250_;
goto v___jp_3180_;
}
else
{
lean_object* v_val_3251_; lean_object* v___x_3252_; 
v_val_3251_ = lean_ctor_get(v_maxSuggestions_3246_, 0);
lean_inc(v_val_3251_);
lean_dec_ref_known(v_maxSuggestions_3246_, 1);
v___x_3252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3252_, 0, v_val_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3247_);
lean_ctor_set(v___x_3252_, 2, v___f_2424_);
lean_ctor_set(v___x_3252_, 3, v___x_3248_);
v___y_3181_ = v___y_3229_;
v___y_3182_ = v___y_3243_;
v___y_3183_ = v___y_3230_;
v___y_3184_ = v___y_3231_;
v___y_3185_ = v___y_3232_;
v___y_3186_ = v___y_3233_;
v___y_3187_ = v___y_3235_;
v___y_3188_ = v___y_3236_;
v___y_3189_ = v___y_3237_;
v___y_3190_ = v___y_3238_;
v___y_3191_ = v___y_3239_;
v___y_3192_ = v___y_3240_;
v___y_3193_ = v___y_3241_;
v___y_3194_ = v___y_3242_;
v___y_3195_ = v___x_3252_;
goto v___jp_3180_;
}
}
}
v___jp_3253_:
{
uint8_t v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = 1;
lean_inc(v___y_3256_);
v___x_3268_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3256_, v___x_3267_, v___y_3263_, v___y_3254_, v___y_3265_);
if (lean_obj_tag(v___x_3268_) == 0)
{
if (lean_obj_tag(v___y_3264_) == 1)
{
lean_object* v_a_3269_; lean_object* v_val_3270_; lean_object* v___x_3271_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v_val_3270_ = lean_ctor_get(v___y_3264_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v___y_3264_, 1);
v___x_3271_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3270_);
lean_dec(v_val_3270_);
v___y_3229_ = v___y_3254_;
v___y_3230_ = v___y_3256_;
v___y_3231_ = v___y_3257_;
v___y_3232_ = v___y_3255_;
v___y_3233_ = v___y_3266_;
v___y_3234_ = v_a_3269_;
v___y_3235_ = v___x_3267_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3259_;
v___y_3238_ = v___y_3260_;
v___y_3239_ = v___y_3261_;
v___y_3240_ = v___y_3262_;
v___y_3241_ = v___y_3263_;
v___y_3242_ = v___y_3265_;
v___y_3243_ = v___x_3271_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
lean_dec(v___y_3264_);
v_a_3272_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3273_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3229_ = v___y_3254_;
v___y_3230_ = v___y_3256_;
v___y_3231_ = v___y_3257_;
v___y_3232_ = v___y_3255_;
v___y_3233_ = v___y_3266_;
v___y_3234_ = v_a_3272_;
v___y_3235_ = v___x_3267_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3259_;
v___y_3238_ = v___y_3260_;
v___y_3239_ = v___y_3261_;
v___y_3240_ = v___y_3262_;
v___y_3241_ = v___y_3263_;
v___y_3242_ = v___y_3265_;
v___y_3243_ = v___x_3273_;
goto v___jp_3228_;
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec(v___y_3258_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v_a_3274_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3268_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3268_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
v___jp_3282_:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Syntax_getOptional_x3f(v___y_3283_);
lean_dec(v___y_3283_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_box(0);
v___y_3254_ = v___y_3294_;
v___y_3255_ = v___y_3286_;
v___y_3256_ = v___y_3285_;
v___y_3257_ = v___y_3289_;
v___y_3258_ = v___y_3284_;
v___y_3259_ = v___y_3291_;
v___y_3260_ = v___y_3293_;
v___y_3261_ = v___y_3292_;
v___y_3262_ = v___y_3290_;
v___y_3263_ = v___y_3288_;
v___y_3264_ = v_args_3287_;
v___y_3265_ = v___y_3295_;
v___y_3266_ = v___x_3297_;
goto v___jp_3253_;
}
else
{
lean_object* v_val_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
v_val_3298_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3296_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_val_3298_);
lean_dec(v___x_3296_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_val_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
v___y_3254_ = v___y_3294_;
v___y_3255_ = v___y_3286_;
v___y_3256_ = v___y_3285_;
v___y_3257_ = v___y_3289_;
v___y_3258_ = v___y_3284_;
v___y_3259_ = v___y_3291_;
v___y_3260_ = v___y_3293_;
v___y_3261_ = v___y_3292_;
v___y_3262_ = v___y_3290_;
v___y_3263_ = v___y_3288_;
v___y_3264_ = v_args_3287_;
v___y_3265_ = v___y_3295_;
v___y_3266_ = v___x_3303_;
goto v___jp_3253_;
}
}
}
}
v___jp_3307_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3321_ = lean_unsigned_to_nat(3u);
v___x_3322_ = l_Lean_Syntax_getArg(v___y_3311_, v___x_3321_);
lean_dec(v___y_3311_);
v___x_3323_ = l_Lean_Syntax_isNone(v___x_3322_);
if (v___x_3323_ == 0)
{
uint8_t v___x_3324_; 
lean_inc(v___x_3322_);
v___x_3324_ = l_Lean_Syntax_matchesNull(v___x_3322_, v___x_3306_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; 
lean_dec(v___x_3322_);
lean_dec(v_o_3312_);
lean_dec(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_3325_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3326_ = l_Lean_Syntax_getArg(v___x_3322_, v___x_2435_);
lean_dec(v___x_3322_);
v___x_3327_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3328_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3327_);
lean_inc(v___x_3326_);
v___x_3329_ = l_Lean_Syntax_isOfKind(v___x_3326_, v___x_3328_);
lean_dec(v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec(v___x_3326_);
lean_dec(v_o_3312_);
lean_dec(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_3330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; lean_object* v_args_3332_; lean_object* v___x_3333_; 
v___x_3331_ = l_Lean_Syntax_getArg(v___x_3326_, v___x_3306_);
lean_dec(v___x_3326_);
v_args_3332_ = l_Lean_Syntax_getArgs(v___x_3331_);
lean_dec(v___x_3331_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_args_3332_);
v___y_3283_ = v___y_3308_;
v___y_3284_ = v_o_3312_;
v___y_3285_ = v___y_3310_;
v___y_3286_ = v___y_3309_;
v_args_3287_ = v___x_3333_;
v___y_3288_ = v___y_3313_;
v___y_3289_ = v___y_3314_;
v___y_3290_ = v___y_3315_;
v___y_3291_ = v___y_3316_;
v___y_3292_ = v___y_3317_;
v___y_3293_ = v___y_3318_;
v___y_3294_ = v___y_3319_;
v___y_3295_ = v___y_3320_;
goto v___jp_3282_;
}
}
}
else
{
lean_object* v___x_3334_; 
lean_dec(v___x_3322_);
v___x_3334_ = lean_box(0);
v___y_3283_ = v___y_3308_;
v___y_3284_ = v_o_3312_;
v___y_3285_ = v___y_3310_;
v___y_3286_ = v___y_3309_;
v_args_3287_ = v___x_3334_;
v___y_3288_ = v___y_3313_;
v___y_3289_ = v___y_3314_;
v___y_3290_ = v___y_3315_;
v___y_3291_ = v___y_3316_;
v___y_3292_ = v___y_3317_;
v___y_3293_ = v___y_3318_;
v___y_3294_ = v___y_3319_;
v___y_3295_ = v___y_3320_;
goto v___jp_3282_;
}
}
v___jp_3335_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3345_ = lean_unsigned_to_nat(2u);
v___x_3346_ = l_Lean_Syntax_getArg(v_stx_2419_, v___x_3345_);
v___x_3347_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3348_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3347_);
lean_inc(v___x_3346_);
v___x_3349_ = l_Lean_Syntax_isOfKind(v___x_3346_, v___x_3348_);
lean_dec(v___x_3348_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
lean_dec(v___x_3346_);
lean_dec(v_bang_3336_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_3350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3350_;
}
else
{
lean_object* v_cfg_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v_cfg_3351_ = l_Lean_Syntax_getArg(v___x_3346_, v___x_2435_);
v___x_3352_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_3353_ = l_Lean_Name_mkStr4(v___x_2421_, v___x_2422_, v___x_2423_, v___x_3352_);
lean_inc(v_cfg_3351_);
v___x_3354_ = l_Lean_Syntax_isOfKind(v_cfg_3351_, v___x_3353_);
lean_dec(v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v_cfg_3351_);
lean_dec(v___x_3346_);
lean_dec(v_bang_3336_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_3355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = l_Lean_Syntax_getArg(v___x_3346_, v___x_3306_);
v___x_3357_ = l_Lean_Syntax_getArg(v___x_3346_, v___x_3345_);
v___x_3358_ = l_Lean_Syntax_isNone(v___x_3357_);
if (v___x_3358_ == 0)
{
uint8_t v___x_3359_; 
lean_inc(v___x_3357_);
v___x_3359_ = l_Lean_Syntax_matchesNull(v___x_3357_, v___x_3306_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_dec(v___x_3357_);
lean_dec(v___x_3356_);
lean_dec(v_cfg_3351_);
lean_dec(v___x_3346_);
lean_dec(v_bang_3336_);
lean_dec(v_tk_2436_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2421_);
v___x_3360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3360_;
}
else
{
lean_object* v_o_3361_; lean_object* v___x_3362_; 
v_o_3361_ = l_Lean_Syntax_getArg(v___x_3357_, v___x_2435_);
lean_dec(v___x_3357_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_o_3361_);
v___y_3308_ = v___x_3356_;
v___y_3309_ = v_bang_3336_;
v___y_3310_ = v_cfg_3351_;
v___y_3311_ = v___x_3346_;
v_o_3312_ = v___x_3362_;
v___y_3313_ = v___y_3337_;
v___y_3314_ = v___y_3338_;
v___y_3315_ = v___y_3339_;
v___y_3316_ = v___y_3340_;
v___y_3317_ = v___y_3341_;
v___y_3318_ = v___y_3342_;
v___y_3319_ = v___y_3343_;
v___y_3320_ = v___y_3344_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3363_; 
lean_dec(v___x_3357_);
v___x_3363_ = lean_box(0);
v___y_3308_ = v___x_3356_;
v___y_3309_ = v_bang_3336_;
v___y_3310_ = v_cfg_3351_;
v___y_3311_ = v___x_3346_;
v_o_3312_ = v___x_3363_;
v___y_3313_ = v___y_3337_;
v___y_3314_ = v___y_3338_;
v___y_3315_ = v___y_3339_;
v___y_3316_ = v___y_3340_;
v___y_3317_ = v___y_3341_;
v___y_3318_ = v___y_3342_;
v___y_3319_ = v___y_3343_;
v___y_3320_ = v___y_3344_;
goto v___jp_3307_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3371_, lean_object* v_stx_3372_, lean_object* v___x_3373_, lean_object* v___x_3374_, lean_object* v___x_3375_, lean_object* v___x_3376_, lean_object* v___f_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
uint8_t v___x_31353__boxed_3387_; uint8_t v___x_31354__boxed_3388_; lean_object* v_res_3389_; 
v___x_31353__boxed_3387_ = lean_unbox(v___x_3371_);
v___x_31354__boxed_3388_ = lean_unbox(v___x_3373_);
v_res_3389_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31353__boxed_3387_, v_stx_3372_, v___x_31354__boxed_3388_, v___x_3374_, v___x_3375_, v___x_3376_, v___f_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v_stx_3372_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; uint8_t v___x_3411_; lean_object* v___f_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___y_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3396_);
v___x_3410_ = l_Lean_Syntax_isOfKind(v_stx_3396_, v___x_3409_);
v___x_3411_ = 1;
v___f_3412_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3413_ = lean_box(v___x_3410_);
v___x_3414_ = lean_box(v___x_3411_);
v___y_3415_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3415_, 0, v___x_3413_);
lean_closure_set(v___y_3415_, 1, v_stx_3396_);
lean_closure_set(v___y_3415_, 2, v___x_3414_);
lean_closure_set(v___y_3415_, 3, v___x_3406_);
lean_closure_set(v___y_3415_, 4, v___x_3407_);
lean_closure_set(v___y_3415_, 5, v___x_3408_);
lean_closure_set(v___y_3415_, 6, v___f_3412_);
v___x_3416_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3416_, 0, v___y_3415_);
v___x_3417_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3416_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3429_, lean_object* v_as_3430_, lean_object* v_as_x27_3431_, lean_object* v_b_3432_, lean_object* v_a_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3429_, v_as_x27_3431_, v_b_3432_, v___y_3440_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3444_, lean_object* v_as_3445_, lean_object* v_as_x27_3446_, lean_object* v_b_3447_, lean_object* v_a_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3444_, v_as_3445_, v_as_x27_3446_, v_b_3447_, v_a_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v_as_x27_3446_);
lean_dec(v_as_3445_);
lean_dec(v___x_3444_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3466_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3467_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3469_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3470_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3466_, v___x_3467_, v___x_3468_, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3500_ = l_Lean_addBuiltinDeclarationRanges(v___x_3498_, v___x_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3503_, lean_object* v_simprocs_3504_, lean_object* v_fvarIdsToSimp_3505_, uint8_t v_simplifyTarget_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = lean_unsigned_to_nat(32u);
v___x_3516_ = lean_mk_empty_array_with_capacity(v___x_3515_);
lean_dec_ref(v___x_3516_);
v___x_3517_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3518_ = l_Lean_Meta_dsimpGoal(v_a_3514_, v_ctx_3503_, v_simprocs_3504_, v_simplifyTarget_3506_, v_fvarIdsToSimp_3505_, v___x_3517_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v_fst_3520_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v_fst_3520_ = lean_ctor_get(v_a_3519_, 0);
if (lean_obj_tag(v_fst_3520_) == 0)
{
lean_object* v_snd_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_snd_3521_ = lean_ctor_get(v_a_3519_, 1);
lean_inc(v_snd_3521_);
lean_dec(v_a_3519_);
v___x_3522_ = lean_box(0);
v___x_3523_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3522_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v___x_3523_, 0);
lean_dec(v_unused_3531_);
v___x_3525_ = v___x_3523_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v___x_3523_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_snd_3521_);
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_snd_3521_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v_snd_3521_);
v_a_3532_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3523_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3523_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_snd_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3566_; 
lean_inc_ref(v_fst_3520_);
v_snd_3540_ = lean_ctor_get(v_a_3519_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3519_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_a_3519_, 0);
lean_dec(v_unused_3567_);
v___x_3542_ = v_a_3519_;
v_isShared_3543_ = v_isSharedCheck_3566_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3540_);
lean_dec(v_a_3519_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3566_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_val_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v_val_3544_ = lean_ctor_get(v_fst_3520_, 0);
lean_inc(v_val_3544_);
lean_dec_ref_known(v_fst_3520_, 1);
v___x_3545_ = lean_box(0);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 1);
lean_ctor_set(v___x_3542_, 1, v___x_3545_);
lean_ctor_set(v___x_3542_, 0, v_val_3544_);
v___x_3547_ = v___x_3542_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_val_3544_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3547_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; 
v_unused_3556_ = lean_ctor_get(v___x_3548_, 0);
lean_dec(v_unused_3556_);
v___x_3550_ = v___x_3548_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v___x_3548_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v_snd_3540_);
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_snd_3540_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec(v_snd_3540_);
v_a_3557_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3548_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3548_);
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
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_a_3568_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3518_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3518_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec_ref(v_fvarIdsToSimp_3505_);
lean_dec_ref(v_simprocs_3504_);
lean_dec_ref(v_ctx_3503_);
v_a_3576_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3513_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3513_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3584_, lean_object* v_simprocs_3585_, lean_object* v_fvarIdsToSimp_3586_, lean_object* v_simplifyTarget_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
uint8_t v_simplifyTarget_boxed_3594_; lean_object* v_res_3595_; 
v_simplifyTarget_boxed_3594_ = lean_unbox(v_simplifyTarget_3587_);
v_res_3595_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3584_, v_simprocs_3585_, v_fvarIdsToSimp_3586_, v_simplifyTarget_boxed_3594_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3596_, lean_object* v_simprocs_3597_, lean_object* v_fvarIdsToSimp_3598_, uint8_t v_simplifyTarget_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3596_, v_simprocs_3597_, v_fvarIdsToSimp_3598_, v_simplifyTarget_3599_, v_a_3601_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3610_, lean_object* v_simprocs_3611_, lean_object* v_fvarIdsToSimp_3612_, lean_object* v_simplifyTarget_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
uint8_t v_simplifyTarget_boxed_3623_; lean_object* v_res_3624_; 
v_simplifyTarget_boxed_3623_ = lean_unbox(v_simplifyTarget_3613_);
v_res_3624_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3610_, v_simprocs_3611_, v_fvarIdsToSimp_3612_, v_simplifyTarget_boxed_3623_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3625_, lean_object* v_simprocs_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3628_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = l_Lean_MVarId_getNondepPropHyps(v_a_3637_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
v___x_3640_ = 1;
v___x_3641_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3625_, v_simprocs_3626_, v_a_3639_, v___x_3640_, v___y_3628_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
return v___x_3641_;
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_simprocs_3626_);
lean_dec_ref(v_ctx_3625_);
v_a_3642_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3638_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3638_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec_ref(v_simprocs_3626_);
lean_dec_ref(v_ctx_3625_);
v_a_3650_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3636_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3636_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3658_, lean_object* v_simprocs_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3658_, v_simprocs_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3670_, lean_object* v_ctx_3671_, lean_object* v_simprocs_3672_, uint8_t v_type_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3670_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v___x_3685_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3671_, v_simprocs_3672_, v_a_3684_, v_type_3673_, v___y_3675_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v___x_3685_;
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v_simprocs_3672_);
lean_dec_ref(v_ctx_3671_);
v_a_3686_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3683_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3683_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3694_, lean_object* v_ctx_3695_, lean_object* v_simprocs_3696_, lean_object* v_type_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v_type_555__boxed_3707_; lean_object* v_res_3708_; 
v_type_555__boxed_3707_ = lean_unbox(v_type_3697_);
v_res_3708_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3694_, v_ctx_3695_, v_simprocs_3696_, v_type_555__boxed_3707_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3709_, lean_object* v_simprocs_3710_, lean_object* v_loc_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
if (lean_obj_tag(v_loc_3711_) == 0)
{
lean_object* v___f_3721_; lean_object* v___x_3722_; 
v___f_3721_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3721_, 0, v_ctx_3709_);
lean_closure_set(v___f_3721_, 1, v_simprocs_3710_);
v___x_3722_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3721_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3722_;
}
else
{
lean_object* v_hypotheses_3723_; uint8_t v_type_3724_; lean_object* v___x_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; 
v_hypotheses_3723_ = lean_ctor_get(v_loc_3711_, 0);
lean_inc_ref(v_hypotheses_3723_);
v_type_3724_ = lean_ctor_get_uint8(v_loc_3711_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3711_, 1);
v___x_3725_ = lean_box(v_type_3724_);
v___f_3726_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3726_, 0, v_hypotheses_3723_);
lean_closure_set(v___f_3726_, 1, v_ctx_3709_);
lean_closure_set(v___f_3726_, 2, v_simprocs_3710_);
lean_closure_set(v___f_3726_, 3, v___x_3725_);
v___x_3727_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3726_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3728_, lean_object* v_simprocs_3729_, lean_object* v_loc_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3728_, v_simprocs_3729_, v_loc_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3745_, lean_object* v_stx_3746_, uint8_t v___x_3747_, lean_object* v___x_3748_, lean_object* v___x_3749_, lean_object* v___x_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
if (v___x_3745_ == 0)
{
lean_object* v___x_3760_; 
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_3760_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3760_;
}
else
{
lean_object* v___x_3761_; lean_object* v_tk_3762_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_stx_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v_args_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___x_4116_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v_o_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v_bang_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v_tk_3762_ = l_Lean_Syntax_getArg(v_stx_3746_, v___x_3761_);
v___x_4116_ = lean_unsigned_to_nat(1u);
v___x_4172_ = l_Lean_Syntax_getArg(v_stx_3746_, v___x_4116_);
v___x_4173_ = l_Lean_Syntax_isNone(v___x_4172_);
if (v___x_4173_ == 0)
{
uint8_t v___x_4174_; 
lean_inc(v___x_4172_);
v___x_4174_ = l_Lean_Syntax_matchesNull(v___x_4172_, v___x_4116_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; 
lean_dec(v___x_4172_);
lean_dec(v_tk_3762_);
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_4175_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4175_;
}
else
{
lean_object* v_bang_4176_; lean_object* v___x_4177_; 
v_bang_4176_ = l_Lean_Syntax_getArg(v___x_4172_, v___x_3761_);
lean_dec(v___x_4172_);
v___x_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4177_, 0, v_bang_4176_);
v_bang_4145_ = v___x_4177_;
v___y_4146_ = v___y_3751_;
v___y_4147_ = v___y_3752_;
v___y_4148_ = v___y_3753_;
v___y_4149_ = v___y_3754_;
v___y_4150_ = v___y_3755_;
v___y_4151_ = v___y_3756_;
v___y_4152_ = v___y_3757_;
v___y_4153_ = v___y_3758_;
goto v___jp_4144_;
}
}
else
{
lean_object* v___x_4178_; 
lean_dec(v___x_4172_);
v___x_4178_ = lean_box(0);
v_bang_4145_ = v___x_4178_;
v___y_4146_ = v___y_3751_;
v___y_4147_ = v___y_3752_;
v___y_4148_ = v___y_3753_;
v___y_4149_ = v___y_3754_;
v___y_4150_ = v___y_3755_;
v___y_4151_ = v___y_3756_;
v___y_4152_ = v___y_3757_;
v___y_4153_ = v___y_3758_;
goto v___jp_4144_;
}
v___jp_3763_:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3768_, v___y_3774_, v___y_3775_, v___y_3765_, v___y_3764_, v___y_3772_, v___y_3767_, v___y_3771_, v___y_3766_, v___y_3773_, v___y_3770_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v_usedTheorems_3778_; lean_object* v_diag_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3821_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v_usedTheorems_3778_ = lean_ctor_get(v_a_3777_, 0);
v_diag_3779_ = lean_ctor_get(v_a_3777_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3777_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3781_ = v_a_3777_;
v_isShared_3782_ = v_isSharedCheck_3821_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_diag_3779_);
lean_inc(v_usedTheorems_3778_);
lean_dec(v_a_3777_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3821_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3769_, v_usedTheorems_3778_, v___y_3771_, v___y_3766_, v___y_3773_, v___y_3770_);
lean_dec_ref(v_usedTheorems_3778_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v_ref_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v_ref_3785_ = lean_ctor_get(v___y_3773_, 2);
v___x_3786_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 1, v_a_3784_);
lean_ctor_set(v___x_3781_, 0, v___x_3786_);
v___x_3788_ = v___x_3781_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_a_3784_);
v___x_3788_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3789_ = lean_box(0);
v___x_3790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
lean_ctor_set(v___x_3790_, 2, v___x_3789_);
lean_ctor_set(v___x_3790_, 3, v___x_3789_);
lean_ctor_set(v___x_3790_, 4, v___x_3789_);
lean_ctor_set(v___x_3790_, 5, v___x_3789_);
lean_inc(v_ref_3785_);
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_ref_3785_);
v___x_3792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3793_ = 4;
v___x_3794_ = l_Lean_MessageData_nil;
v___x_3795_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3762_, v___x_3790_, v___x_3791_, v___x_3792_, v___x_3789_, v___x_3793_, v___x_3794_, v___y_3773_, v___y_3770_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v___x_3795_, 0);
lean_dec(v_unused_3803_);
v___x_3797_ = v___x_3795_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_dec(v___x_3795_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 0, v_diag_3779_);
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_diag_3779_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec_ref(v_diag_3779_);
v_a_3804_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3795_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3795_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_del_object(v___x_3781_);
lean_dec_ref(v_diag_3779_);
lean_dec(v_tk_3762_);
v_a_3813_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3783_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3783_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec(v___y_3769_);
lean_dec(v_tk_3762_);
v_a_3822_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3776_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3776_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
v___jp_3830_:
{
if (lean_obj_tag(v___y_3832_) == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3844_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*1, v___x_3747_);
v___y_3764_ = v___y_3831_;
v___y_3765_ = v___y_3833_;
v___y_3766_ = v___y_3834_;
v___y_3767_ = v___y_3835_;
v___y_3768_ = v___y_3842_;
v___y_3769_ = v___y_3839_;
v___y_3770_ = v___y_3838_;
v___y_3771_ = v___y_3837_;
v___y_3772_ = v___y_3836_;
v___y_3773_ = v___y_3841_;
v___y_3774_ = v___y_3840_;
v___y_3775_ = v___x_3844_;
goto v___jp_3763_;
}
else
{
lean_object* v_val_3845_; lean_object* v___x_3846_; 
v_val_3845_ = lean_ctor_get(v___y_3832_, 0);
lean_inc(v_val_3845_);
lean_dec_ref_known(v___y_3832_, 1);
v___x_3846_ = l_Lean_Elab_Tactic_expandLocation(v_val_3845_);
lean_dec(v_val_3845_);
v___y_3764_ = v___y_3831_;
v___y_3765_ = v___y_3833_;
v___y_3766_ = v___y_3834_;
v___y_3767_ = v___y_3835_;
v___y_3768_ = v___y_3842_;
v___y_3769_ = v___y_3839_;
v___y_3770_ = v___y_3838_;
v___y_3771_ = v___y_3837_;
v___y_3772_ = v___y_3836_;
v___y_3773_ = v___y_3841_;
v___y_3774_ = v___y_3840_;
v___y_3775_ = v___x_3846_;
goto v___jp_3763_;
}
}
v___jp_3847_:
{
uint8_t v___x_3859_; uint8_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3859_ = 0;
v___x_3860_ = 2;
v___x_3861_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_3862_ = lean_box(v___x_3859_);
v___x_3863_ = lean_box(v___x_3860_);
v___x_3864_ = lean_box(v___x_3859_);
lean_inc(v_stx_3850_);
v___x_3865_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3865_, 0, v_stx_3850_);
lean_closure_set(v___x_3865_, 1, v___x_3862_);
lean_closure_set(v___x_3865_, 2, v___x_3863_);
lean_closure_set(v___x_3865_, 3, v___x_3864_);
lean_closure_set(v___x_3865_, 4, v___x_3861_);
v___x_3866_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3865_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
if (lean_obj_tag(v___y_3849_) == 0)
{
lean_object* v_ctx_3868_; lean_object* v_simprocs_3869_; 
v_ctx_3868_ = lean_ctor_get(v_a_3867_, 0);
lean_inc_ref(v_ctx_3868_);
v_simprocs_3869_ = lean_ctor_get(v_a_3867_, 1);
lean_inc_ref(v_simprocs_3869_);
lean_dec(v_a_3867_);
v___y_3831_ = v___y_3852_;
v___y_3832_ = v___y_3848_;
v___y_3833_ = v___y_3851_;
v___y_3834_ = v___y_3856_;
v___y_3835_ = v___y_3854_;
v___y_3836_ = v___y_3853_;
v___y_3837_ = v___y_3855_;
v___y_3838_ = v___y_3858_;
v___y_3839_ = v_stx_3850_;
v___y_3840_ = v_simprocs_3869_;
v___y_3841_ = v___y_3857_;
v___y_3842_ = v_ctx_3868_;
goto v___jp_3830_;
}
else
{
lean_object* v_ctx_3870_; lean_object* v_simprocs_3871_; lean_object* v___x_3872_; 
lean_dec_ref_known(v___y_3849_, 1);
v_ctx_3870_ = lean_ctor_get(v_a_3867_, 0);
lean_inc_ref(v_ctx_3870_);
v_simprocs_3871_ = lean_ctor_get(v_a_3867_, 1);
lean_inc_ref(v_simprocs_3871_);
lean_dec(v_a_3867_);
v___x_3872_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3870_);
v___y_3831_ = v___y_3852_;
v___y_3832_ = v___y_3848_;
v___y_3833_ = v___y_3851_;
v___y_3834_ = v___y_3856_;
v___y_3835_ = v___y_3854_;
v___y_3836_ = v___y_3853_;
v___y_3837_ = v___y_3855_;
v___y_3838_ = v___y_3858_;
v___y_3839_ = v_stx_3850_;
v___y_3840_ = v_simprocs_3871_;
v___y_3841_ = v___y_3857_;
v___y_3842_ = v___x_3872_;
goto v___jp_3830_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v_stx_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v_tk_3762_);
v_a_3873_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3866_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3866_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
v___jp_3881_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_inc_ref(v___y_3889_);
v___x_3902_ = l_Array_append___redArg(v___y_3889_, v___y_3901_);
lean_dec_ref(v___y_3901_);
lean_inc(v___y_3891_);
lean_inc(v___y_3898_);
v___x_3903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3903_, 0, v___y_3898_);
lean_ctor_set(v___x_3903_, 1, v___y_3891_);
lean_ctor_set(v___x_3903_, 2, v___x_3902_);
v___x_3904_ = l_Lean_Syntax_node6(v___y_3898_, v___y_3884_, v___y_3895_, v___y_3900_, v___y_3892_, v___y_3887_, v___y_3888_, v___x_3903_);
v___y_3848_ = v___y_3894_;
v___y_3849_ = v___y_3890_;
v_stx_3850_ = v___x_3904_;
v___y_3851_ = v___y_3893_;
v___y_3852_ = v___y_3899_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3885_;
v___y_3855_ = v___y_3897_;
v___y_3856_ = v___y_3896_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___y_3883_;
goto v___jp_3847_;
}
v___jp_3905_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_inc_ref(v___y_3912_);
v___x_3925_ = l_Array_append___redArg(v___y_3912_, v___y_3924_);
lean_dec_ref(v___y_3924_);
lean_inc(v___y_3914_);
lean_inc(v___y_3922_);
v___x_3926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3926_, 0, v___y_3922_);
lean_ctor_set(v___x_3926_, 1, v___y_3914_);
lean_ctor_set(v___x_3926_, 2, v___x_3925_);
if (lean_obj_tag(v___y_3917_) == 0)
{
lean_object* v___x_3927_; 
v___x_3927_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3882_ = v___y_3906_;
v___y_3883_ = v___y_3907_;
v___y_3884_ = v___y_3908_;
v___y_3885_ = v___y_3909_;
v___y_3886_ = v___y_3910_;
v___y_3887_ = v___y_3911_;
v___y_3888_ = v___x_3926_;
v___y_3889_ = v___y_3912_;
v___y_3890_ = v___y_3913_;
v___y_3891_ = v___y_3914_;
v___y_3892_ = v___y_3915_;
v___y_3893_ = v___y_3916_;
v___y_3894_ = v___y_3917_;
v___y_3895_ = v___y_3918_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___y_3919_;
v___y_3898_ = v___y_3922_;
v___y_3899_ = v___y_3921_;
v___y_3900_ = v___y_3923_;
v___y_3901_ = v___x_3927_;
goto v___jp_3881_;
}
else
{
lean_object* v_val_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_val_3928_ = lean_ctor_get(v___y_3917_, 0);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_3928_);
v___x_3930_ = lean_array_push(v___x_3929_, v_val_3928_);
v___y_3882_ = v___y_3906_;
v___y_3883_ = v___y_3907_;
v___y_3884_ = v___y_3908_;
v___y_3885_ = v___y_3909_;
v___y_3886_ = v___y_3910_;
v___y_3887_ = v___y_3911_;
v___y_3888_ = v___x_3926_;
v___y_3889_ = v___y_3912_;
v___y_3890_ = v___y_3913_;
v___y_3891_ = v___y_3914_;
v___y_3892_ = v___y_3915_;
v___y_3893_ = v___y_3916_;
v___y_3894_ = v___y_3917_;
v___y_3895_ = v___y_3918_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___y_3919_;
v___y_3898_ = v___y_3922_;
v___y_3899_ = v___y_3921_;
v___y_3900_ = v___y_3923_;
v___y_3901_ = v___x_3930_;
goto v___jp_3881_;
}
}
v___jp_3931_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_inc_ref(v___y_3938_);
v___x_3951_ = l_Array_append___redArg(v___y_3938_, v___y_3950_);
lean_dec_ref(v___y_3950_);
lean_inc(v___y_3940_);
lean_inc(v___y_3948_);
v___x_3952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3952_, 0, v___y_3948_);
lean_ctor_set(v___x_3952_, 1, v___y_3940_);
lean_ctor_set(v___x_3952_, 2, v___x_3951_);
if (lean_obj_tag(v___y_3933_) == 1)
{
lean_object* v_val_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_val_3953_ = lean_ctor_get(v___y_3933_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v___y_3933_, 1);
v___x_3954_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_3948_, 3);
v___x_3955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___y_3948_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
lean_inc_ref(v___y_3938_);
v___x_3956_ = l_Array_append___redArg(v___y_3938_, v_val_3953_);
lean_dec(v_val_3953_);
lean_inc(v___y_3940_);
v___x_3957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3957_, 0, v___y_3948_);
lean_ctor_set(v___x_3957_, 1, v___y_3940_);
lean_ctor_set(v___x_3957_, 2, v___x_3956_);
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___y_3948_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = l_Array_mkArray3___redArg(v___x_3955_, v___x_3957_, v___x_3959_);
v___y_3906_ = v___y_3932_;
v___y_3907_ = v___y_3934_;
v___y_3908_ = v___y_3935_;
v___y_3909_ = v___y_3936_;
v___y_3910_ = v___y_3937_;
v___y_3911_ = v___x_3952_;
v___y_3912_ = v___y_3938_;
v___y_3913_ = v___y_3939_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3941_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3944_;
v___y_3919_ = v___y_3946_;
v___y_3920_ = v___y_3945_;
v___y_3921_ = v___y_3947_;
v___y_3922_ = v___y_3948_;
v___y_3923_ = v___y_3949_;
v___y_3924_ = v___x_3960_;
goto v___jp_3905_;
}
else
{
lean_object* v___x_3961_; 
lean_dec(v___y_3933_);
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3906_ = v___y_3932_;
v___y_3907_ = v___y_3934_;
v___y_3908_ = v___y_3935_;
v___y_3909_ = v___y_3936_;
v___y_3910_ = v___y_3937_;
v___y_3911_ = v___x_3952_;
v___y_3912_ = v___y_3938_;
v___y_3913_ = v___y_3939_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3941_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3944_;
v___y_3919_ = v___y_3946_;
v___y_3920_ = v___y_3945_;
v___y_3921_ = v___y_3947_;
v___y_3922_ = v___y_3948_;
v___y_3923_ = v___y_3949_;
v___y_3924_ = v___x_3961_;
goto v___jp_3905_;
}
}
v___jp_3962_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_inc_ref(v___y_3979_);
v___x_3983_ = l_Array_append___redArg(v___y_3979_, v___y_3982_);
lean_dec_ref(v___y_3982_);
lean_inc(v___y_3968_);
lean_inc(v___y_3966_);
v___x_3984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3984_, 0, v___y_3966_);
lean_ctor_set(v___x_3984_, 1, v___y_3968_);
lean_ctor_set(v___x_3984_, 2, v___x_3983_);
v___x_3985_ = l_Lean_Syntax_node6(v___y_3966_, v___y_3976_, v___y_3975_, v___y_3981_, v___y_3971_, v___y_3970_, v___y_3972_, v___x_3984_);
v___y_3848_ = v___y_3974_;
v___y_3849_ = v___y_3969_;
v_stx_3850_ = v___x_3985_;
v___y_3851_ = v___y_3973_;
v___y_3852_ = v___y_3980_;
v___y_3853_ = v___y_3963_;
v___y_3854_ = v___y_3965_;
v___y_3855_ = v___y_3978_;
v___y_3856_ = v___y_3977_;
v___y_3857_ = v___y_3967_;
v___y_3858_ = v___y_3964_;
goto v___jp_3847_;
}
v___jp_3986_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_inc_ref(v___y_4002_);
v___x_4006_ = l_Array_append___redArg(v___y_4002_, v___y_4005_);
lean_dec_ref(v___y_4005_);
lean_inc(v___y_3992_);
lean_inc(v___y_3990_);
v___x_4007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4007_, 0, v___y_3990_);
lean_ctor_set(v___x_4007_, 1, v___y_3992_);
lean_ctor_set(v___x_4007_, 2, v___x_4006_);
if (lean_obj_tag(v___y_3997_) == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3963_ = v___y_3987_;
v___y_3964_ = v___y_3988_;
v___y_3965_ = v___y_3989_;
v___y_3966_ = v___y_3990_;
v___y_3967_ = v___y_3991_;
v___y_3968_ = v___y_3992_;
v___y_3969_ = v___y_3993_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___x_4007_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3997_;
v___y_3975_ = v___y_3998_;
v___y_3976_ = v___y_3999_;
v___y_3977_ = v___y_4001_;
v___y_3978_ = v___y_4000_;
v___y_3979_ = v___y_4002_;
v___y_3980_ = v___y_4003_;
v___y_3981_ = v___y_4004_;
v___y_3982_ = v___x_4008_;
goto v___jp_3962_;
}
else
{
lean_object* v_val_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_val_4009_ = lean_ctor_get(v___y_3997_, 0);
v___x_4010_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4009_);
v___x_4011_ = lean_array_push(v___x_4010_, v_val_4009_);
v___y_3963_ = v___y_3987_;
v___y_3964_ = v___y_3988_;
v___y_3965_ = v___y_3989_;
v___y_3966_ = v___y_3990_;
v___y_3967_ = v___y_3991_;
v___y_3968_ = v___y_3992_;
v___y_3969_ = v___y_3993_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___x_4007_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3997_;
v___y_3975_ = v___y_3998_;
v___y_3976_ = v___y_3999_;
v___y_3977_ = v___y_4001_;
v___y_3978_ = v___y_4000_;
v___y_3979_ = v___y_4002_;
v___y_3980_ = v___y_4003_;
v___y_3981_ = v___y_4004_;
v___y_3982_ = v___x_4011_;
goto v___jp_3962_;
}
}
v___jp_4012_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_inc_ref(v___y_4028_);
v___x_4032_ = l_Array_append___redArg(v___y_4028_, v___y_4031_);
lean_dec_ref(v___y_4031_);
lean_inc(v___y_4019_);
lean_inc(v___y_4017_);
v___x_4033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4033_, 0, v___y_4017_);
lean_ctor_set(v___x_4033_, 1, v___y_4019_);
lean_ctor_set(v___x_4033_, 2, v___x_4032_);
if (lean_obj_tag(v___y_4014_) == 1)
{
lean_object* v_val_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_val_4034_ = lean_ctor_get(v___y_4014_, 0);
lean_inc(v_val_4034_);
lean_dec_ref_known(v___y_4014_, 1);
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4017_, 3);
v___x_4036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___y_4017_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
lean_inc_ref(v___y_4028_);
v___x_4037_ = l_Array_append___redArg(v___y_4028_, v_val_4034_);
lean_dec(v_val_4034_);
lean_inc(v___y_4019_);
v___x_4038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4038_, 0, v___y_4017_);
lean_ctor_set(v___x_4038_, 1, v___y_4019_);
lean_ctor_set(v___x_4038_, 2, v___x_4037_);
v___x_4039_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4017_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Array_mkArray3___redArg(v___x_4036_, v___x_4038_, v___x_4040_);
v___y_3987_ = v___y_4013_;
v___y_3988_ = v___y_4015_;
v___y_3989_ = v___y_4016_;
v___y_3990_ = v___y_4017_;
v___y_3991_ = v___y_4018_;
v___y_3992_ = v___y_4019_;
v___y_3993_ = v___y_4020_;
v___y_3994_ = v___x_4033_;
v___y_3995_ = v___y_4021_;
v___y_3996_ = v___y_4022_;
v___y_3997_ = v___y_4023_;
v___y_3998_ = v___y_4024_;
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4027_;
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4028_;
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4030_;
v___y_4005_ = v___x_4041_;
goto v___jp_3986_;
}
else
{
lean_object* v___x_4042_; 
lean_dec(v___y_4014_);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3987_ = v___y_4013_;
v___y_3988_ = v___y_4015_;
v___y_3989_ = v___y_4016_;
v___y_3990_ = v___y_4017_;
v___y_3991_ = v___y_4018_;
v___y_3992_ = v___y_4019_;
v___y_3993_ = v___y_4020_;
v___y_3994_ = v___x_4033_;
v___y_3995_ = v___y_4021_;
v___y_3996_ = v___y_4022_;
v___y_3997_ = v___y_4023_;
v___y_3998_ = v___y_4024_;
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4027_;
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4028_;
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4030_;
v___y_4005_ = v___x_4042_;
goto v___jp_3986_;
}
}
v___jp_4043_:
{
if (lean_obj_tag(v___y_4050_) == 0)
{
lean_object* v_ref_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_ref_4057_ = lean_ctor_get(v___y_4048_, 2);
v___x_4058_ = 0;
v___x_4059_ = l_Lean_SourceInfo_fromRef(v_ref_4057_, v___x_4058_);
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4061_ = l_Lean_Name_mkStr4(v___x_3748_, v___x_3749_, v___x_3750_, v___x_4060_);
v___x_4062_ = l_Lean_SourceInfo_fromRef(v_tk_3762_, v___x_3747_);
v___x_4063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
lean_ctor_set(v___x_4063_, 1, v___x_4060_);
v___x_4064_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4065_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4059_);
v___x_4066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4059_);
lean_ctor_set(v___x_4066_, 1, v___x_4064_);
lean_ctor_set(v___x_4066_, 2, v___x_4065_);
if (lean_obj_tag(v___y_4049_) == 1)
{
lean_object* v_val_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_val_4067_ = lean_ctor_get(v___y_4049_, 0);
lean_inc(v_val_4067_);
lean_dec_ref_known(v___y_4049_, 1);
v___x_4068_ = l_Lean_SourceInfo_fromRef(v_val_4067_, v___x_3747_);
lean_dec(v_val_4067_);
v___x_4069_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Array_mkArray1___redArg(v___x_4070_);
v___y_3932_ = v___y_4044_;
v___y_3933_ = v___y_4045_;
v___y_3934_ = v___y_4046_;
v___y_3935_ = v___x_4061_;
v___y_3936_ = v___y_4047_;
v___y_3937_ = v___y_4048_;
v___y_3938_ = v___x_4065_;
v___y_3939_ = v___y_4050_;
v___y_3940_ = v___x_4064_;
v___y_3941_ = v___x_4066_;
v___y_3942_ = v___y_4051_;
v___y_3943_ = v___y_4056_;
v___y_3944_ = v___x_4063_;
v___y_3945_ = v___y_4052_;
v___y_3946_ = v___y_4053_;
v___y_3947_ = v___y_4054_;
v___y_3948_ = v___x_4059_;
v___y_3949_ = v___y_4055_;
v___y_3950_ = v___x_4071_;
goto v___jp_3931_;
}
else
{
lean_object* v___x_4072_; 
lean_dec(v___y_4049_);
v___x_4072_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3932_ = v___y_4044_;
v___y_3933_ = v___y_4045_;
v___y_3934_ = v___y_4046_;
v___y_3935_ = v___x_4061_;
v___y_3936_ = v___y_4047_;
v___y_3937_ = v___y_4048_;
v___y_3938_ = v___x_4065_;
v___y_3939_ = v___y_4050_;
v___y_3940_ = v___x_4064_;
v___y_3941_ = v___x_4066_;
v___y_3942_ = v___y_4051_;
v___y_3943_ = v___y_4056_;
v___y_3944_ = v___x_4063_;
v___y_3945_ = v___y_4052_;
v___y_3946_ = v___y_4053_;
v___y_3947_ = v___y_4054_;
v___y_3948_ = v___x_4059_;
v___y_3949_ = v___y_4055_;
v___y_3950_ = v___x_4072_;
goto v___jp_3931_;
}
}
else
{
lean_object* v_ref_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_ref_4073_ = lean_ctor_get(v___y_4048_, 2);
v___x_4074_ = 0;
v___x_4075_ = l_Lean_SourceInfo_fromRef(v_ref_4073_, v___x_4074_);
v___x_4076_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4077_ = l_Lean_Name_mkStr4(v___x_3748_, v___x_3749_, v___x_3750_, v___x_4076_);
v___x_4078_ = l_Lean_SourceInfo_fromRef(v_tk_3762_, v___x_3747_);
v___x_4079_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4082_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4075_);
v___x_4083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4075_);
lean_ctor_set(v___x_4083_, 1, v___x_4081_);
lean_ctor_set(v___x_4083_, 2, v___x_4082_);
if (lean_obj_tag(v___y_4049_) == 1)
{
lean_object* v_val_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_val_4084_ = lean_ctor_get(v___y_4049_, 0);
lean_inc(v_val_4084_);
lean_dec_ref_known(v___y_4049_, 1);
v___x_4085_ = l_Lean_SourceInfo_fromRef(v_val_4084_, v___x_3747_);
lean_dec(v_val_4084_);
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4085_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = l_Array_mkArray1___redArg(v___x_4087_);
v___y_4013_ = v___y_4044_;
v___y_4014_ = v___y_4045_;
v___y_4015_ = v___y_4046_;
v___y_4016_ = v___y_4047_;
v___y_4017_ = v___x_4075_;
v___y_4018_ = v___y_4048_;
v___y_4019_ = v___x_4081_;
v___y_4020_ = v___y_4050_;
v___y_4021_ = v___x_4083_;
v___y_4022_ = v___y_4051_;
v___y_4023_ = v___y_4056_;
v___y_4024_ = v___x_4080_;
v___y_4025_ = v___x_4077_;
v___y_4026_ = v___y_4052_;
v___y_4027_ = v___y_4053_;
v___y_4028_ = v___x_4082_;
v___y_4029_ = v___y_4054_;
v___y_4030_ = v___y_4055_;
v___y_4031_ = v___x_4088_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4089_; 
lean_dec(v___y_4049_);
v___x_4089_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4013_ = v___y_4044_;
v___y_4014_ = v___y_4045_;
v___y_4015_ = v___y_4046_;
v___y_4016_ = v___y_4047_;
v___y_4017_ = v___x_4075_;
v___y_4018_ = v___y_4048_;
v___y_4019_ = v___x_4081_;
v___y_4020_ = v___y_4050_;
v___y_4021_ = v___x_4083_;
v___y_4022_ = v___y_4051_;
v___y_4023_ = v___y_4056_;
v___y_4024_ = v___x_4080_;
v___y_4025_ = v___x_4077_;
v___y_4026_ = v___y_4052_;
v___y_4027_ = v___y_4053_;
v___y_4028_ = v___x_4082_;
v___y_4029_ = v___y_4054_;
v___y_4030_ = v___y_4055_;
v___y_4031_ = v___x_4089_;
goto v___jp_4012_;
}
}
}
v___jp_4090_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = lean_unsigned_to_nat(3u);
v___x_4105_ = l_Lean_Syntax_getArg(v___y_4092_, v___x_4104_);
lean_dec(v___y_4092_);
v___x_4106_ = l_Lean_Syntax_getOptional_x3f(v___x_4105_);
lean_dec(v___x_4105_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_box(0);
v___y_4044_ = v___y_4098_;
v___y_4045_ = v_args_4095_;
v___y_4046_ = v___y_4103_;
v___y_4047_ = v___y_4099_;
v___y_4048_ = v___y_4102_;
v___y_4049_ = v___y_4091_;
v___y_4050_ = v___y_4093_;
v___y_4051_ = v___y_4096_;
v___y_4052_ = v___y_4101_;
v___y_4053_ = v___y_4100_;
v___y_4054_ = v___y_4097_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___x_4107_;
goto v___jp_4043_;
}
else
{
lean_object* v_val_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_val_4108_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4106_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_val_4108_);
lean_dec(v___x_4106_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_val_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
v___y_4044_ = v___y_4098_;
v___y_4045_ = v_args_4095_;
v___y_4046_ = v___y_4103_;
v___y_4047_ = v___y_4099_;
v___y_4048_ = v___y_4102_;
v___y_4049_ = v___y_4091_;
v___y_4050_ = v___y_4093_;
v___y_4051_ = v___y_4096_;
v___y_4052_ = v___y_4101_;
v___y_4053_ = v___y_4100_;
v___y_4054_ = v___y_4097_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___x_4113_;
goto v___jp_4043_;
}
}
}
}
v___jp_4117_:
{
lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4131_ = l_Lean_Syntax_getArg(v___y_4119_, v___y_4118_);
v___x_4132_ = l_Lean_Syntax_isNone(v___x_4131_);
if (v___x_4132_ == 0)
{
uint8_t v___x_4133_; 
lean_inc(v___x_4131_);
v___x_4133_ = l_Lean_Syntax_matchesNull(v___x_4131_, v___x_4116_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; 
lean_dec(v___x_4131_);
lean_dec(v_o_4122_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec(v_tk_3762_);
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_4134_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4134_;
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4135_ = l_Lean_Syntax_getArg(v___x_4131_, v___x_3761_);
lean_dec(v___x_4131_);
v___x_4136_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3750_);
lean_inc_ref(v___x_3749_);
lean_inc_ref(v___x_3748_);
v___x_4137_ = l_Lean_Name_mkStr4(v___x_3748_, v___x_3749_, v___x_3750_, v___x_4136_);
lean_inc(v___x_4135_);
v___x_4138_ = l_Lean_Syntax_isOfKind(v___x_4135_, v___x_4137_);
lean_dec(v___x_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; 
lean_dec(v___x_4135_);
lean_dec(v_o_4122_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec(v_tk_3762_);
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_4139_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4139_;
}
else
{
lean_object* v___x_4140_; lean_object* v_args_4141_; lean_object* v___x_4142_; 
v___x_4140_ = l_Lean_Syntax_getArg(v___x_4135_, v___x_4116_);
lean_dec(v___x_4135_);
v_args_4141_ = l_Lean_Syntax_getArgs(v___x_4140_);
lean_dec(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_args_4141_);
v___y_4091_ = v_o_4122_;
v___y_4092_ = v___y_4119_;
v___y_4093_ = v___y_4120_;
v___y_4094_ = v___y_4121_;
v_args_4095_ = v___x_4142_;
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___y_4124_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v___x_4143_; 
lean_dec(v___x_4131_);
v___x_4143_ = lean_box(0);
v___y_4091_ = v_o_4122_;
v___y_4092_ = v___y_4119_;
v___y_4093_ = v___y_4120_;
v___y_4094_ = v___y_4121_;
v_args_4095_ = v___x_4143_;
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___y_4124_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
goto v___jp_4090_;
}
}
v___jp_4144_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; 
v___x_4154_ = lean_unsigned_to_nat(2u);
v___x_4155_ = l_Lean_Syntax_getArg(v_stx_3746_, v___x_4154_);
v___x_4156_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3750_);
lean_inc_ref(v___x_3749_);
lean_inc_ref(v___x_3748_);
v___x_4157_ = l_Lean_Name_mkStr4(v___x_3748_, v___x_3749_, v___x_3750_, v___x_4156_);
lean_inc(v___x_4155_);
v___x_4158_ = l_Lean_Syntax_isOfKind(v___x_4155_, v___x_4157_);
lean_dec(v___x_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; 
lean_dec(v___x_4155_);
lean_dec(v_bang_4145_);
lean_dec(v_tk_3762_);
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_4159_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4159_;
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4160_ = l_Lean_Syntax_getArg(v___x_4155_, v___x_3761_);
v___x_4161_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3750_);
lean_inc_ref(v___x_3749_);
lean_inc_ref(v___x_3748_);
v___x_4162_ = l_Lean_Name_mkStr4(v___x_3748_, v___x_3749_, v___x_3750_, v___x_4161_);
lean_inc(v___x_4160_);
v___x_4163_ = l_Lean_Syntax_isOfKind(v___x_4160_, v___x_4162_);
lean_dec(v___x_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; 
lean_dec(v___x_4160_);
lean_dec(v___x_4155_);
lean_dec(v_bang_4145_);
lean_dec(v_tk_3762_);
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_4164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4164_;
}
else
{
lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4165_ = l_Lean_Syntax_getArg(v___x_4155_, v___x_4116_);
v___x_4166_ = l_Lean_Syntax_isNone(v___x_4165_);
if (v___x_4166_ == 0)
{
uint8_t v___x_4167_; 
lean_inc(v___x_4165_);
v___x_4167_ = l_Lean_Syntax_matchesNull(v___x_4165_, v___x_4116_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; 
lean_dec(v___x_4165_);
lean_dec(v___x_4160_);
lean_dec(v___x_4155_);
lean_dec(v_bang_4145_);
lean_dec(v_tk_3762_);
lean_dec_ref(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec_ref(v___x_3748_);
v___x_4168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4168_;
}
else
{
lean_object* v_o_4169_; lean_object* v___x_4170_; 
v_o_4169_ = l_Lean_Syntax_getArg(v___x_4165_, v___x_3761_);
lean_dec(v___x_4165_);
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v_o_4169_);
v___y_4118_ = v___x_4154_;
v___y_4119_ = v___x_4155_;
v___y_4120_ = v_bang_4145_;
v___y_4121_ = v___x_4160_;
v_o_4122_ = v___x_4170_;
v___y_4123_ = v___y_4146_;
v___y_4124_ = v___y_4147_;
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4149_;
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___y_4151_;
v___y_4129_ = v___y_4152_;
v___y_4130_ = v___y_4153_;
goto v___jp_4117_;
}
}
else
{
lean_object* v___x_4171_; 
lean_dec(v___x_4165_);
v___x_4171_ = lean_box(0);
v___y_4118_ = v___x_4154_;
v___y_4119_ = v___x_4155_;
v___y_4120_ = v_bang_4145_;
v___y_4121_ = v___x_4160_;
v_o_4122_ = v___x_4171_;
v___y_4123_ = v___y_4146_;
v___y_4124_ = v___y_4147_;
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4149_;
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___y_4151_;
v___y_4129_ = v___y_4152_;
v___y_4130_ = v___y_4153_;
goto v___jp_4117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4179_, lean_object* v_stx_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v___x_8194__boxed_4194_; uint8_t v___x_8195__boxed_4195_; lean_object* v_res_4196_; 
v___x_8194__boxed_4194_ = lean_unbox(v___x_4179_);
v___x_8195__boxed_4195_ = lean_unbox(v___x_4181_);
v_res_4196_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8194__boxed_4194_, v_stx_4180_, v___x_8195__boxed_4195_, v___x_4182_, v___x_4183_, v___x_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v_stx_4180_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; uint8_t v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___y_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4203_);
v___x_4217_ = l_Lean_Syntax_isOfKind(v_stx_4203_, v___x_4216_);
v___x_4218_ = 1;
v___x_4219_ = lean_box(v___x_4217_);
v___x_4220_ = lean_box(v___x_4218_);
v___y_4221_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4221_, 0, v___x_4219_);
lean_closure_set(v___y_4221_, 1, v_stx_4203_);
lean_closure_set(v___y_4221_, 2, v___x_4220_);
lean_closure_set(v___y_4221_, 3, v___x_4213_);
lean_closure_set(v___y_4221_, 4, v___x_4214_);
lean_closure_set(v___y_4221_, 5, v___x_4215_);
v___x_4222_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4222_, 0, v___y_4221_);
v___x_4223_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4222_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec_ref(v_a_4229_);
lean_dec(v_a_4228_);
lean_dec_ref(v_a_4227_);
lean_dec(v_a_4226_);
lean_dec_ref(v_a_4225_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4242_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4246_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4242_, v___x_4243_, v___x_4244_, v___x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4277_ = l_Lean_addBuiltinDeclarationRanges(v___x_4275_, v___x_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4279_;
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
