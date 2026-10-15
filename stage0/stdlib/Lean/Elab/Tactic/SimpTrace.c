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
uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_105_ == 0)
{
if (v___x_104_ == 0)
{
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_103_;
goto v___jp_96_;
}
else
{
size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((size_t)0ULL);
v___x_107_ = lean_usize_of_nat(v___x_102_);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_101_, v___x_106_, v___x_107_, v___x_103_);
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_108_;
goto v___jp_96_;
}
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_102_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_101_, v___x_109_, v___x_110_, v___x_103_);
lean_dec_ref(v_configItems_101_);
v___y_97_ = v___x_111_;
goto v___jp_96_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(lean_object* v_cfg_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(lean_object* v_cfg_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_115_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(lean_object* v_cfg_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(v_cfg_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* v_stx_129_, lean_object* v_usedSimps_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_stx_136_; lean_object* v___x_137_; 
v_stx_136_ = l_Lean_Syntax_unsetTrailing(v_stx_129_);
v___x_137_ = l_Lean_Elab_Tactic_mkSimpOnly(v_stx_136_, v_usedSimps_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_137_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_137_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* v_stx_154_, lean_object* v_usedSimps_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_Tactic_mkSimpCallStx(v_stx_154_, v_usedSimps_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec_ref(v_usedSimps_155_);
return v_res_161_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* v_00_u03b1_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(v_00_u03b1_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(uint8_t v___x_192_, lean_object* v_x_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(v___x_192_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(lean_object* v___x_201_, lean_object* v_x_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_33698__boxed_208_; lean_object* v_res_209_; 
v___x_33698__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33698__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v_x_202_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* v___y_210_, lean_object* v___x_211_, uint8_t v___x_212_, lean_object* v___y_213_, lean_object* v_simprocs_214_, lean_object* v_discharge_x3f_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
if (lean_obj_tag(v___y_210_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_211_);
v___x_226_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_212_);
v___x_227_ = l_Lean_Elab_Tactic_simpLocation(v___y_213_, v_simprocs_214_, v_discharge_x3f_215_, v___x_226_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_val_228_ = lean_ctor_get(v___y_210_, 0);
v___x_229_ = l_Lean_Elab_Tactic_expandLocation(v_val_228_);
v___x_230_ = l_Lean_Elab_Tactic_simpLocation(v___y_213_, v_simprocs_214_, v_discharge_x3f_215_, v___x_229_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* v___y_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v___y_234_, lean_object* v_simprocs_235_, lean_object* v_discharge_x3f_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
uint8_t v___x_33725__boxed_246_; lean_object* v_res_247_; 
v___x_33725__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33725__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___x_232_);
lean_dec(v___y_231_);
return v_res_247_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Array_mkArray0___redArg();
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(lean_object* v___x_258_, lean_object* v_as_x27_259_, lean_object* v_b_260_, lean_object* v___y_261_){
_start:
{
if (lean_obj_tag(v_as_x27_259_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_b_260_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_tail_265_; lean_object* v_ref_266_; uint8_t v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_head_264_ = lean_ctor_get(v_as_x27_259_, 0);
v_tail_265_ = lean_ctor_get(v_as_x27_259_, 1);
v_ref_266_ = lean_ctor_get(v___y_261_, 2);
v___x_267_ = 1;
v___x_268_ = 0;
v___x_269_ = l_Lean_SourceInfo_fromRef(v_ref_266_, v___x_268_);
v___x_270_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_271_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_272_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_269_);
v___x_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_273_, 0, v___x_269_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_272_);
lean_inc(v_head_264_);
v___x_274_ = l_Lean_mkCIdentFrom(v___x_258_, v_head_264_, v___x_267_);
lean_inc_ref(v___x_273_);
v___x_275_ = l_Lean_Syntax_node3(v___x_269_, v___x_270_, v___x_273_, v___x_273_, v___x_274_);
v___x_276_ = lean_array_push(v_b_260_, v___x_275_);
v_as_x27_259_ = v_tail_265_;
v_b_260_ = v___x_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(lean_object* v___x_278_, lean_object* v_as_x27_279_, lean_object* v_b_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_278_, v_as_x27_279_, v_b_280_, v___y_281_);
lean_dec_ref(v___y_281_);
lean_dec(v_as_x27_279_);
lean_dec(v___x_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v_fst_288_; uint8_t v___x_289_; 
v_head_286_ = lean_ctor_get(v_x_284_, 0);
v_tail_287_ = lean_ctor_get(v_x_284_, 1);
v_fst_288_ = lean_ctor_get(v_head_286_, 0);
v___x_289_ = l_Lean_isPrivateName(v_fst_288_);
if (v___x_289_ == 0)
{
v_x_284_ = v_tail_287_;
goto _start;
}
else
{
lean_object* v___x_291_; 
lean_inc(v_head_286_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v_head_286_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_292_);
lean_dec(v_x_292_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(lean_object* v_opts_294_, lean_object* v_opt_295_){
_start:
{
lean_object* v_name_296_; lean_object* v_defValue_297_; lean_object* v_map_298_; lean_object* v___x_299_; 
v_name_296_ = lean_ctor_get(v_opt_295_, 0);
v_defValue_297_ = lean_ctor_get(v_opt_295_, 1);
v_map_298_ = lean_ctor_get(v_opts_294_, 0);
v___x_299_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_298_, v_name_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
uint8_t v___x_300_; 
v___x_300_ = lean_unbox(v_defValue_297_);
return v___x_300_;
}
else
{
lean_object* v_val_301_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___x_299_, 1);
if (lean_obj_tag(v_val_301_) == 1)
{
uint8_t v_v_302_; 
v_v_302_ = lean_ctor_get_uint8(v_val_301_, 0);
lean_dec_ref_known(v_val_301_, 0);
return v_v_302_;
}
else
{
uint8_t v___x_303_; 
lean_dec(v_val_301_);
v___x_303_ = lean_unbox(v_defValue_297_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(lean_object* v_opts_304_, lean_object* v_opt_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_304_, v_opt_305_);
lean_dec_ref(v_opt_305_);
lean_dec_ref(v_opts_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(lean_object* v_opt_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_309_);
v___x_312_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_311_, v_opt_308_);
lean_dec_ref(v___x_311_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_315_, v___y_316_);
lean_dec_ref(v___y_316_);
lean_dec_ref(v_opt_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; uint8_t v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; lean_object* v_toCold_330_; lean_object* v_mctx_331_; lean_object* v_lctx_332_; lean_object* v_options_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = 0;
v_env_328_ = l_Lean_Environment_setRecordingDeps(v_env_326_, v___x_327_);
v___x_329_ = lean_st_ref_get(v___y_321_);
v_toCold_330_ = lean_ctor_get(v___y_322_, 0);
v_mctx_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_331_);
lean_dec(v___x_329_);
v_lctx_332_ = lean_ctor_get(v___y_320_, 2);
v_options_333_ = lean_ctor_get(v_toCold_330_, 2);
lean_inc_ref(v_options_333_);
lean_inc_ref(v_lctx_332_);
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v_env_328_);
lean_ctor_set(v___x_334_, 1, v_mctx_331_);
lean_ctor_set(v___x_334_, 2, v_lctx_332_);
lean_ctor_set(v___x_334_, 3, v_options_333_);
v___x_335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_msgData_319_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_351_, uint8_t v___y_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_353_) == 1)
{
lean_object* v_pre_354_; 
v_pre_354_ = lean_ctor_get(v_x_353_, 0);
switch(lean_obj_tag(v_pre_354_))
{
case 1:
{
lean_object* v_pre_355_; 
v_pre_355_ = lean_ctor_get(v_pre_354_, 0);
switch(lean_obj_tag(v_pre_355_))
{
case 0:
{
lean_object* v_str_356_; lean_object* v_str_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_str_356_ = lean_ctor_get(v_x_353_, 1);
v_str_357_ = lean_ctor_get(v_pre_354_, 1);
v___x_358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_359_ = lean_string_dec_eq(v_str_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_361_ = lean_string_dec_eq(v_str_357_, v___x_360_);
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_363_ = lean_string_dec_eq(v_str_356_, v___x_362_);
if (v___x_363_ == 0)
{
return v___x_363_;
}
else
{
return v_suppressElabErrors_351_;
}
}
}
else
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_365_ = lean_string_dec_eq(v_str_356_, v___x_364_);
if (v___x_365_ == 0)
{
return v___x_365_;
}
else
{
return v_suppressElabErrors_351_;
}
}
}
case 1:
{
lean_object* v_pre_366_; 
v_pre_366_ = lean_ctor_get(v_pre_355_, 0);
if (lean_obj_tag(v_pre_366_) == 0)
{
lean_object* v_str_367_; lean_object* v_str_368_; lean_object* v_str_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_str_367_ = lean_ctor_get(v_x_353_, 1);
v_str_368_ = lean_ctor_get(v_pre_354_, 1);
v_str_369_ = lean_ctor_get(v_pre_355_, 1);
v___x_370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_371_ = lean_string_dec_eq(v_str_369_, v___x_370_);
if (v___x_371_ == 0)
{
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_373_ = lean_string_dec_eq(v_str_368_, v___x_372_);
if (v___x_373_ == 0)
{
return v___x_373_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_375_ = lean_string_dec_eq(v_str_367_, v___x_374_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
return v_suppressElabErrors_351_;
}
}
}
}
else
{
return v___y_352_;
}
}
default: 
{
return v___y_352_;
}
}
}
case 0:
{
lean_object* v_str_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_str_376_ = lean_ctor_get(v_x_353_, 1);
v___x_377_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_378_ = lean_string_dec_eq(v_str_376_, v___x_377_);
if (v___x_378_ == 0)
{
return v___x_378_;
}
else
{
return v_suppressElabErrors_351_;
}
}
default: 
{
return v___y_352_;
}
}
}
else
{
return v___y_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_379_, lean_object* v___y_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_suppressElabErrors_boxed_382_; uint8_t v___y_33928__boxed_383_; uint8_t v_res_384_; lean_object* v_r_385_; 
v_suppressElabErrors_boxed_382_ = lean_unbox(v_suppressElabErrors_379_);
v___y_33928__boxed_383_ = lean_unbox(v___y_380_);
v_res_384_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_382_, v___y_33928__boxed_383_, v_x_381_);
lean_dec(v_x_381_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_387_, lean_object* v_msgData_388_, uint8_t v_severity_389_, uint8_t v_isSilent_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___y_402_; uint8_t v___y_403_; lean_object* v_toCold_404_; lean_object* v___y_405_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; uint8_t v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; uint8_t v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; uint8_t v___y_471_; uint8_t v___y_472_; uint8_t v___y_473_; uint8_t v___x_484_; uint8_t v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; uint8_t v___y_490_; uint8_t v___x_498_; 
v___x_484_ = 2;
v___x_498_ = l_Lean_instBEqMessageSeverity_beq(v_severity_389_, v___x_484_);
if (v___x_498_ == 0)
{
v___y_490_ = v___x_498_;
goto v___jp_489_;
}
else
{
uint8_t v___x_499_; 
lean_inc_ref(v_msgData_388_);
v___x_499_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_388_);
v___y_490_ = v___x_499_;
goto v___jp_489_;
}
v___jp_396_:
{
lean_object* v_currNamespace_406_; lean_object* v_openDecls_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_env_412_; lean_object* v_nextMacroScope_413_; lean_object* v_ngen_414_; lean_object* v_auxDeclNGen_415_; lean_object* v_traceState_416_; lean_object* v_cache_417_; lean_object* v_recordedDeps_418_; lean_object* v_messages_419_; lean_object* v_infoState_420_; lean_object* v_snapshotTasks_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
v_currNamespace_406_ = lean_ctor_get(v_toCold_404_, 4);
v_openDecls_407_ = lean_ctor_get(v_toCold_404_, 5);
lean_inc(v_openDecls_407_);
lean_inc(v_currNamespace_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_currNamespace_406_);
lean_ctor_set(v___x_408_, 1, v_openDecls_407_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___y_400_);
lean_inc_ref(v___y_397_);
lean_inc_ref(v___y_401_);
v___x_410_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_410_, 0, v___y_401_);
lean_ctor_set(v___x_410_, 1, v___y_399_);
lean_ctor_set(v___x_410_, 2, v___y_398_);
lean_ctor_set(v___x_410_, 3, v___y_397_);
lean_ctor_set(v___x_410_, 4, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5, v___y_403_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 1, v___y_402_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 2, v_isSilent_390_);
v___x_411_ = lean_st_ref_take(v___y_405_);
v_env_412_ = lean_ctor_get(v___x_411_, 0);
v_nextMacroScope_413_ = lean_ctor_get(v___x_411_, 1);
v_ngen_414_ = lean_ctor_get(v___x_411_, 2);
v_auxDeclNGen_415_ = lean_ctor_get(v___x_411_, 3);
v_traceState_416_ = lean_ctor_get(v___x_411_, 4);
v_cache_417_ = lean_ctor_get(v___x_411_, 5);
v_recordedDeps_418_ = lean_ctor_get(v___x_411_, 6);
v_messages_419_ = lean_ctor_get(v___x_411_, 7);
v_infoState_420_ = lean_ctor_get(v___x_411_, 8);
v_snapshotTasks_421_ = lean_ctor_get(v___x_411_, 9);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_432_ == 0)
{
v___x_423_ = v___x_411_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snapshotTasks_421_);
lean_inc(v_infoState_420_);
lean_inc(v_messages_419_);
lean_inc(v_recordedDeps_418_);
lean_inc(v_cache_417_);
lean_inc(v_traceState_416_);
lean_inc(v_auxDeclNGen_415_);
lean_inc(v_ngen_414_);
lean_inc(v_nextMacroScope_413_);
lean_inc(v_env_412_);
lean_dec(v___x_411_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_425_ = lean_box(0);
v___x_426_ = l_Lean_MessageLog_add(v___x_410_, v_messages_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 7, v___x_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_ngen_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_recordedDeps_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_infoState_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 9, v_snapshotTasks_421_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_st_ref_put(v___y_405_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_425_);
return v___x_430_;
}
}
}
v___jp_433_:
{
lean_object* v_fileName_442_; lean_object* v_fileMap_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_459_; 
v_fileName_442_ = lean_ctor_get(v___y_440_, 0);
v_fileMap_443_ = lean_ctor_get(v___y_440_, 1);
v___x_444_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_388_);
v___x_445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_444_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_459_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_459_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_inc_ref_n(v_fileMap_443_, 2);
v___x_450_ = l_Lean_FileMap_toPosition(v_fileMap_443_, v___y_437_);
lean_dec(v___y_437_);
v___x_451_ = l_Lean_FileMap_toPosition(v_fileMap_443_, v___y_441_);
lean_dec(v___y_441_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_436_ == 0)
{
lean_del_object(v___x_448_);
lean_dec_ref(v___y_434_);
v___y_397_ = v___x_453_;
v___y_398_ = v___x_452_;
v___y_399_ = v___x_450_;
v___y_400_ = v_a_446_;
v___y_401_ = v_fileName_442_;
v___y_402_ = v___y_438_;
v___y_403_ = v___y_439_;
v_toCold_404_ = v___y_435_;
v___y_405_ = v___y_394_;
goto v___jp_396_;
}
else
{
uint8_t v___x_454_; 
lean_inc(v_a_446_);
v___x_454_ = l_Lean_MessageData_hasTag(v___y_434_, v_a_446_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec_ref_known(v___x_452_, 1);
lean_dec_ref(v___x_450_);
lean_dec(v_a_446_);
v___x_455_ = lean_box(0);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_455_);
v___x_457_ = v___x_448_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_del_object(v___x_448_);
v___y_397_ = v___x_453_;
v___y_398_ = v___x_452_;
v___y_399_ = v___x_450_;
v___y_400_ = v_a_446_;
v___y_401_ = v_fileName_442_;
v___y_402_ = v___y_438_;
v___y_403_ = v___y_439_;
v_toCold_404_ = v___y_435_;
v___y_405_ = v___y_394_;
goto v___jp_396_;
}
}
}
}
v___jp_460_:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Syntax_getTailPos_x3f(v___y_464_, v___y_466_);
lean_dec(v___y_464_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_inc(v___y_467_);
v___y_434_ = v___y_462_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_467_;
v___y_438_ = v___y_465_;
v___y_439_ = v___y_466_;
v___y_440_ = v___y_463_;
v___y_441_ = v___y_467_;
goto v___jp_433_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v___y_434_ = v___y_462_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_467_;
v___y_438_ = v___y_465_;
v___y_439_ = v___y_466_;
v___y_440_ = v___y_463_;
v___y_441_ = v_val_469_;
goto v___jp_433_;
}
}
v___jp_470_:
{
lean_object* v_toCold_474_; lean_object* v_ref_475_; uint8_t v_suppressElabErrors_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v_ref_480_; lean_object* v___x_481_; 
v_toCold_474_ = lean_ctor_get(v___y_393_, 0);
v_ref_475_ = lean_ctor_get(v___y_393_, 2);
v_suppressElabErrors_476_ = lean_ctor_get_uint8(v___y_393_, sizeof(void*)*3 + 2);
v___x_477_ = lean_box(v_suppressElabErrors_476_);
v___x_478_ = lean_box(v___y_471_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_479_, 0, v___x_477_);
lean_closure_set(v___f_479_, 1, v___x_478_);
v_ref_480_ = l_Lean_replaceRef(v_ref_387_, v_ref_475_);
v___x_481_ = l_Lean_Syntax_getPos_x3f(v_ref_480_, v___y_472_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___y_461_ = v_suppressElabErrors_476_;
v___y_462_ = v___f_479_;
v___y_463_ = v_toCold_474_;
v___y_464_ = v_ref_480_;
v___y_465_ = v___y_473_;
v___y_466_ = v___y_472_;
v___y_467_ = v___x_482_;
goto v___jp_460_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_481_, 1);
v___y_461_ = v_suppressElabErrors_476_;
v___y_462_ = v___f_479_;
v___y_463_ = v_toCold_474_;
v___y_464_ = v_ref_480_;
v___y_465_ = v___y_473_;
v___y_466_ = v___y_472_;
v___y_467_ = v_val_483_;
goto v___jp_460_;
}
}
v___jp_485_:
{
if (v___y_488_ == 0)
{
v___y_471_ = v___y_486_;
v___y_472_ = v___y_487_;
v___y_473_ = v_severity_389_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___y_486_;
v___y_472_ = v___y_487_;
v___y_473_ = v___x_484_;
goto v___jp_470_;
}
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
uint8_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 1;
v___x_492_ = l_Lean_instBEqMessageSeverity_beq(v_severity_389_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_486_ = v___y_490_;
v___y_487_ = v___y_490_;
v___y_488_ = v___x_492_;
goto v___jp_485_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_393_);
v___x_494_ = l_Lean_warningAsError;
v___x_495_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_493_, v___x_494_);
lean_dec_ref(v___x_493_);
v___y_486_ = v___y_490_;
v___y_487_ = v___y_490_;
v___y_488_ = v___x_495_;
goto v___jp_485_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref(v_msgData_388_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_500_, lean_object* v_msgData_501_, lean_object* v_severity_502_, lean_object* v_isSilent_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_severity_boxed_509_; uint8_t v_isSilent_boxed_510_; lean_object* v_res_511_; 
v_severity_boxed_509_ = lean_unbox(v_severity_502_);
v_isSilent_boxed_510_ = lean_unbox(v_isSilent_503_);
v_res_511_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_500_, v_msgData_501_, v_severity_boxed_509_, v_isSilent_boxed_510_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v_ref_500_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_512_, uint8_t v_severity_513_, uint8_t v_isSilent_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_ref_524_; lean_object* v___x_525_; 
v_ref_524_ = lean_ctor_get(v___y_521_, 2);
v___x_525_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_524_, v_msgData_512_, v_severity_513_, v_isSilent_514_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_526_, lean_object* v_severity_527_, lean_object* v_isSilent_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v_severity_boxed_538_; uint8_t v_isSilent_boxed_539_; lean_object* v_res_540_; 
v_severity_boxed_538_ = lean_unbox(v_severity_527_);
v_isSilent_boxed_539_ = lean_unbox(v_isSilent_528_);
v_res_540_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_526_, v_severity_boxed_538_, v_isSilent_boxed_539_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = 1;
v___x_552_ = 0;
v___x_553_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_541_, v___x_551_, v___x_552_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_604_; 
v___x_581_ = lean_st_ref_get(v___y_579_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_env_582_);
lean_dec(v___x_581_);
v___x_583_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_584_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_583_, v___y_578_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_604_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_604_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v_isExporting_594_; 
v_isExporting_594_ = lean_ctor_get_uint8(v_env_582_, sizeof(void*)*13);
lean_dec_ref(v_env_582_);
if (v_isExporting_594_ == 0)
{
lean_dec(v_a_585_);
lean_dec(v_id_571_);
goto v___jp_589_;
}
else
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_isPrivateName(v_id_571_);
if (v___x_595_ == 0)
{
lean_dec(v_a_585_);
lean_dec(v_id_571_);
goto v___jp_589_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_596_ == 0)
{
lean_dec(v_id_571_);
goto v___jp_589_;
}
else
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_587_);
v___x_597_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_598_ = 0;
v___x_599_ = l_Lean_MessageData_ofConstName(v_id_571_, v___x_598_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_602_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_603_;
}
}
}
v___jp_589_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_box(0);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_616_, uint8_t v_enableLog_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_toCold_628_; lean_object* v_env_629_; lean_object* v_currNamespace_630_; lean_object* v_openDecls_631_; lean_object* v___x_632_; lean_object* v_res_633_; lean_object* v___x_634_; 
v___x_627_ = lean_st_ref_get(v___y_625_);
v_toCold_628_ = lean_ctor_get(v___y_624_, 0);
v_env_629_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_627_);
v_currNamespace_630_ = lean_ctor_get(v_toCold_628_, 4);
v_openDecls_631_ = lean_ctor_get(v_toCold_628_, 5);
v___x_632_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_624_);
lean_inc(v_openDecls_631_);
lean_inc(v_currNamespace_630_);
v_res_633_ = l_Lean_ResolveName_resolveGlobalName(v_env_629_, v___x_632_, v_currNamespace_630_, v_openDecls_631_, v_id_616_);
lean_dec_ref(v___x_632_);
v___x_634_ = lean_st_ref_get(v___y_625_);
if (v_enableLog_617_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v___x_634_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_res_633_);
return v___x_635_;
}
else
{
lean_object* v_env_636_; uint8_t v_isExporting_637_; 
v_env_636_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_636_);
lean_dec(v___x_634_);
v_isExporting_637_ = lean_ctor_get_uint8(v_env_636_, sizeof(void*)*13);
lean_dec_ref(v_env_636_);
if (v_isExporting_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_res_633_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_633_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v_fst_641_; lean_object* v___x_642_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v_fst_641_ = lean_ctor_get(v_val_640_, 0);
lean_inc(v_fst_641_);
lean_dec(v_val_640_);
v___x_642_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_641_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v___x_642_, 0);
lean_dec(v_unused_650_);
v___x_644_ = v___x_642_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_dec(v___x_642_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_res_633_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_res_633_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_res_633_);
v_a_651_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_642_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_642_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v___x_659_; 
lean_dec(v___x_639_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_res_633_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_660_, lean_object* v_enableLog_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_enableLog_boxed_671_; lean_object* v_res_672_; 
v_enableLog_boxed_671_ = lean_unbox(v_enableLog_661_);
v_res_672_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_660_, v_enableLog_boxed_671_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
if (lean_obj_tag(v_a_673_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = l_List_reverse___redArg(v_a_674_);
return v___x_675_;
}
else
{
lean_object* v_head_676_; lean_object* v_tail_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_688_; 
v_head_676_ = lean_ctor_get(v_a_673_, 0);
v_tail_677_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_688_ == 0)
{
v___x_679_ = v_a_673_;
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_tail_677_);
lean_inc(v_head_676_);
lean_dec(v_a_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_snd_681_; uint8_t v___x_682_; 
v_snd_681_ = lean_ctor_get(v_head_676_, 1);
v___x_682_ = l_List_isEmpty___redArg(v_snd_681_);
if (v___x_682_ == 0)
{
lean_del_object(v___x_679_);
lean_dec(v_head_676_);
v_a_673_ = v_tail_677_;
goto _start;
}
else
{
lean_object* v___x_685_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v_a_674_);
v___x_685_ = v___x_679_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_head_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_674_);
v___x_685_ = v_reuseFailAlloc_687_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v_a_673_ = v_tail_677_;
v_a_674_ = v___x_685_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
if (lean_obj_tag(v_a_689_) == 0)
{
lean_object* v___x_691_; 
v___x_691_ = l_List_reverse___redArg(v_a_690_);
return v___x_691_;
}
else
{
lean_object* v_head_692_; lean_object* v_tail_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_head_692_ = lean_ctor_get(v_a_689_, 0);
v_tail_693_ = lean_ctor_get(v_a_689_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v_a_689_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_tail_693_);
lean_inc(v_head_692_);
lean_dec(v_a_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; lean_object* v___x_699_; 
v_fst_697_ = lean_ctor_get(v_head_692_, 0);
lean_inc(v_fst_697_);
lean_dec(v_head_692_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_a_690_);
lean_ctor_set(v___x_695_, 0, v_fst_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_690_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_689_ = v_tail_693_;
v_a_690_ = v___x_699_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_ref_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_ref_709_ = lean_ctor_get(v___y_706_, 2);
v___x_710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_719_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc(v_ref_709_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_ref_709_);
lean_ctor_set(v___x_715_, 1, v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 1);
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_toCold_738_; lean_object* v_currRecDepth_739_; lean_object* v_ref_740_; uint16_t v_optionFlags_741_; uint8_t v_suppressElabErrors_742_; uint8_t v_isRecordingDeps_743_; lean_object* v_ref_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_toCold_738_ = lean_ctor_get(v___y_735_, 0);
v_currRecDepth_739_ = lean_ctor_get(v___y_735_, 1);
v_ref_740_ = lean_ctor_get(v___y_735_, 2);
v_optionFlags_741_ = lean_ctor_get_uint16(v___y_735_, sizeof(void*)*3);
v_suppressElabErrors_742_ = lean_ctor_get_uint8(v___y_735_, sizeof(void*)*3 + 2);
v_isRecordingDeps_743_ = lean_ctor_get_uint8(v___y_735_, sizeof(void*)*3 + 3);
v_ref_744_ = l_Lean_replaceRef(v_ref_727_, v_ref_740_);
lean_inc(v_currRecDepth_739_);
lean_inc_ref(v_toCold_738_);
v___x_745_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_745_, 0, v_toCold_738_);
lean_ctor_set(v___x_745_, 1, v_currRecDepth_739_);
lean_ctor_set(v___x_745_, 2, v_ref_744_);
lean_ctor_set_uint16(v___x_745_, sizeof(void*)*3, v_optionFlags_741_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 2, v_suppressElabErrors_742_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3 + 3, v_isRecordingDeps_743_);
v___x_746_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_728_, v___y_733_, v___y_734_, v___x_745_, v___y_736_);
lean_dec_ref_known(v___x_745_, 3);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_747_, lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_747_, v_msg_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v_ref_747_);
return v_res_758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
lean_ctor_set(v___x_765_, 4, v___x_763_);
lean_ctor_set(v___x_765_, 5, v___x_763_);
lean_ctor_set(v___x_765_, 6, v___x_763_);
lean_ctor_set(v___x_765_, 7, v___x_763_);
lean_ctor_set(v___x_765_, 8, v___x_763_);
lean_ctor_set(v___x_765_, 9, v___x_763_);
lean_ctor_set(v___x_765_, 10, v___x_763_);
lean_ctor_set(v___x_765_, 11, v___x_762_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(32u);
v___x_767_ = lean_mk_empty_array_with_capacity(v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((size_t)5ULL);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_unsigned_to_nat(32u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_774_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_770_);
lean_ctor_set(v___x_774_, 3, v___x_770_);
lean_ctor_set_usize(v___x_774_, 4, v___x_769_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(1);
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__20));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__22));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__24));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__26));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_812_, lean_object* v_declHint_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_env_818_; uint8_t v___x_819_; 
v___x_816_ = lean_box(0);
v___x_817_ = lean_st_ref_get(v___y_814_);
v_env_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref(v_env_818_);
lean_dec(v___x_817_);
v___x_819_ = l_Lean_Name_isAnonymous(v_declHint_813_);
if (v___x_819_ == 0)
{
uint8_t v_isExporting_820_; 
v_isExporting_820_ = lean_ctor_get_uint8(v_env_818_, sizeof(void*)*13);
if (v_isExporting_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_813_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_msg_812_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
lean_inc_ref(v_env_818_);
v___x_822_ = l_Lean_Environment_setExporting(v_env_818_, v___x_819_);
lean_inc(v_declHint_813_);
lean_inc_ref(v___x_822_);
v___x_823_ = l_Lean_Environment_contains(v___x_822_, v_declHint_813_, v_isExporting_820_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v___x_822_);
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_813_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v_msg_812_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_c_830_; lean_object* v___x_831_; 
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_827_ = l_Lean_Options_empty;
v___x_828_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_828_, 0, v___x_822_);
lean_ctor_set(v___x_828_, 1, v___x_825_);
lean_ctor_set(v___x_828_, 2, v___x_826_);
lean_ctor_set(v___x_828_, 3, v___x_827_);
lean_inc(v_declHint_813_);
v___x_829_ = l_Lean_MessageData_ofConstName(v_declHint_813_, v___x_819_);
v_c_830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_830_, 0, v___x_828_);
lean_ctor_set(v_c_830_, 1, v___x_829_);
v___x_831_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_818_, v_declHint_813_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_813_);
v___x_832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_c_830_);
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Lean_MessageData_note(v___x_835_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v_msg_812_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_895_; 
v_val_839_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_895_ == 0)
{
v___x_841_ = v___x_831_;
v_isShared_842_ = v_isSharedCheck_895_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_831_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_895_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v_modules_844_; lean_object* v_moduleNames_845_; lean_object* v_mod_846_; uint8_t v___y_848_; uint8_t v___x_878_; 
v___x_843_ = l_Lean_Environment_header(v_env_818_);
lean_dec_ref(v_env_818_);
v_modules_844_ = lean_ctor_get(v___x_843_, 3);
lean_inc_ref(v_modules_844_);
v_moduleNames_845_ = lean_ctor_get(v___x_843_, 4);
lean_inc_ref(v_moduleNames_845_);
lean_dec_ref(v___x_843_);
v_mod_846_ = lean_array_get(v___x_816_, v_moduleNames_845_, v_val_839_);
lean_dec_ref(v_moduleNames_845_);
v___x_878_ = l_Lean_isPrivateName(v_declHint_813_);
lean_dec(v_declHint_813_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_modules_844_);
v___x_880_ = lean_nat_dec_lt(v_val_839_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_modules_844_);
lean_dec(v_val_839_);
v___y_848_ = v___x_878_;
goto v___jp_847_;
}
else
{
lean_object* v___x_881_; lean_object* v_toImport_882_; uint8_t v_isExported_883_; 
v___x_881_ = lean_array_fget(v_modules_844_, v_val_839_);
lean_dec(v_val_839_);
lean_dec_ref(v_modules_844_);
v_toImport_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc_ref(v_toImport_882_);
lean_dec(v___x_881_);
v_isExported_883_ = lean_ctor_get_uint8(v_toImport_882_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_882_);
v___y_848_ = v_isExported_883_;
goto v___jp_847_;
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref(v_modules_844_);
lean_del_object(v___x_841_);
lean_dec(v_val_839_);
v___x_884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_c_830_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__25);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_ofName(v_mod_846_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__27);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_MessageData_note(v___x_891_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v_msg_812_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
v___jp_847_:
{
if (v___y_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v_c_830_);
v___x_851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_MessageData_ofName(v_mod_846_);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_MessageData_note(v___x_856_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v_msg_812_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_858_);
v___x_860_ = v___x_841_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v_c_830_);
v___x_864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_MessageData_ofName(v_mod_846_);
lean_inc_ref(v___x_866_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__21);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_866_);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__23);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_MessageData_note(v___x_872_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v_msg_812_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_874_);
v___x_876_ = v___x_841_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
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
lean_object* v___x_896_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_813_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_msg_812_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_897_, lean_object* v_declHint_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_897_, v_declHint_898_, v___y_899_);
lean_dec(v___y_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_902_, lean_object* v_declHint_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_923_; 
v___x_913_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_902_, v_declHint_903_, v___y_911_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_923_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_918_ = l_Lean_unknownIdentifierMessageTag;
v___x_919_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v_a_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_919_);
v___x_921_ = v___x_916_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_924_, lean_object* v_declHint_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_924_, v_declHint_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_936_, lean_object* v_msg_937_, lean_object* v_declHint_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_a_949_; lean_object* v___x_950_; 
v___x_948_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_937_, v_declHint_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___x_948_);
v___x_950_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_936_, v_a_949_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_951_, lean_object* v_msg_952_, lean_object* v_declHint_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_951_, v_msg_952_, v_declHint_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v_ref_951_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_970_, lean_object* v_constName_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_981_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_982_ = 0;
lean_inc(v_constName_971_);
v___x_983_ = l_Lean_MessageData_ofConstName(v_constName_971_, v___x_982_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_981_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_970_, v___x_986_, v_constName_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_988_, lean_object* v_constName_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_988_, v_constName_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v_ref_988_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_1000_, lean_object* v_cs_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_cs_1012_; uint8_t v___x_1016_; 
v___x_1011_ = lean_box(0);
v_cs_1012_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_1001_, v___x_1011_);
v___x_1016_ = l_List_isEmpty___redArg(v_cs_1012_);
if (v___x_1016_ == 0)
{
lean_dec(v_n_1000_);
goto v___jp_1013_;
}
else
{
lean_object* v_ref_1017_; lean_object* v___x_1018_; lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_cs_1012_);
v_ref_1017_ = lean_ctor_get(v___y_1008_, 2);
v___x_1018_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_1017_, v_n_1000_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
v___jp_1013_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_1012_, v___x_1011_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1027_, lean_object* v_cs_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1027_, v_cs_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = 1;
lean_inc(v_n_1039_);
v___x_1050_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1039_, v___x_1049_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1039_, v_a_1051_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_n_1039_);
v_a_1053_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1050_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
if (lean_obj_tag(v_a_1072_) == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_array_to_list(v_a_1073_);
return v___x_1074_;
}
else
{
lean_object* v_head_1075_; 
v_head_1075_ = lean_ctor_get(v_a_1072_, 0);
if (lean_obj_tag(v_head_1075_) == 1)
{
lean_object* v_fields_1076_; 
v_fields_1076_ = lean_ctor_get(v_head_1075_, 1);
if (lean_obj_tag(v_fields_1076_) == 0)
{
lean_object* v_tail_1077_; lean_object* v_n_1078_; lean_object* v___x_1079_; 
lean_inc_ref(v_head_1075_);
v_tail_1077_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_tail_1077_);
lean_dec_ref_known(v_a_1072_, 2);
v_n_1078_ = lean_ctor_get(v_head_1075_, 0);
lean_inc(v_n_1078_);
lean_dec_ref_known(v_head_1075_, 2);
v___x_1079_ = lean_array_push(v_a_1073_, v_n_1078_);
v_a_1072_ = v_tail_1077_;
v_a_1073_ = v___x_1079_;
goto _start;
}
else
{
lean_object* v_tail_1081_; 
v_tail_1081_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_tail_1081_);
lean_dec_ref_known(v_a_1072_, 2);
v_a_1072_ = v_tail_1081_;
goto _start;
}
}
else
{
lean_object* v_tail_1083_; 
v_tail_1083_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_tail_1083_);
lean_dec_ref_known(v_a_1072_, 2);
v_a_1072_ = v_tail_1083_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1091_ = l_Lean_MessageData_ofFormat(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1092_, lean_object* v_k_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
if (lean_obj_tag(v_stx_1092_) == 3)
{
lean_object* v_val_1103_; lean_object* v_preresolved_1104_; lean_object* v___x_1105_; lean_object* v_pre_1106_; uint8_t v___x_1107_; 
v_val_1103_ = lean_ctor_get(v_stx_1092_, 2);
lean_inc(v_val_1103_);
v_preresolved_1104_ = lean_ctor_get(v_stx_1092_, 3);
v___x_1105_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1104_);
v_pre_1106_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1104_, v___x_1105_);
v___x_1107_ = l_List_isEmpty___redArg(v_pre_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec_ref_known(v_stx_1092_, 4);
lean_dec(v_val_1103_);
lean_dec_ref(v_k_1093_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_pre_1106_);
return v___x_1108_;
}
else
{
lean_object* v_toCold_1109_; lean_object* v_currRecDepth_1110_; lean_object* v_ref_1111_; uint16_t v_optionFlags_1112_; uint8_t v_suppressElabErrors_1113_; uint8_t v_isRecordingDeps_1114_; lean_object* v_ref_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v_pre_1106_);
v_toCold_1109_ = lean_ctor_get(v___y_1100_, 0);
v_currRecDepth_1110_ = lean_ctor_get(v___y_1100_, 1);
v_ref_1111_ = lean_ctor_get(v___y_1100_, 2);
v_optionFlags_1112_ = lean_ctor_get_uint16(v___y_1100_, sizeof(void*)*3);
v_suppressElabErrors_1113_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1114_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*3 + 3);
v_ref_1115_ = l_Lean_replaceRef(v_stx_1092_, v_ref_1111_);
lean_dec_ref_known(v_stx_1092_, 4);
lean_inc(v_currRecDepth_1110_);
lean_inc_ref(v_toCold_1109_);
v___x_1116_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1116_, 0, v_toCold_1109_);
lean_ctor_set(v___x_1116_, 1, v_currRecDepth_1110_);
lean_ctor_set(v___x_1116_, 2, v_ref_1115_);
lean_ctor_set_uint16(v___x_1116_, sizeof(void*)*3, v_optionFlags_1112_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 2, v_suppressElabErrors_1113_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 3, v_isRecordingDeps_1114_);
lean_inc(v___y_1101_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
v___x_1117_ = lean_apply_10(v_k_1093_, v_val_1103_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___x_1116_, v___y_1101_, lean_box(0));
return v___x_1117_;
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v_k_1093_);
v___x_1118_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1119_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1092_, v___x_1118_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v_stx_1092_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1120_, lean_object* v_k_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1120_, v_k_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1144_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1133_, v___x_1143_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1156_, size_t v_sz_1157_, size_t v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_usize_dec_lt(v_i_1158_, v_sz_1157_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_b_1159_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v_name_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1171_ = lean_array_uget_borrowed(v_as_1156_, v_i_1158_);
v_name_1172_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_name_1172_);
v___x_1173_ = l_Lean_mkIdent(v_name_1172_);
lean_inc(v___x_1173_);
v___x_1174_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1173_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1173_, v_a_1175_, v_b_1159_, v___y_1166_);
lean_dec(v_a_1175_);
lean_dec(v___x_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; size_t v___x_1178_; size_t v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1158_, v___x_1178_);
v_i_1158_ = v___x_1179_;
v_b_1159_ = v_a_1177_;
goto _start;
}
else
{
return v___x_1176_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___x_1173_);
lean_dec_ref(v_b_1159_);
v_a_1181_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1174_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1174_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1189_, lean_object* v_sz_1190_, lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
size_t v_sz_boxed_1202_; size_t v_i_boxed_1203_; lean_object* v_res_1204_; 
v_sz_boxed_1202_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1203_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1189_, v_sz_boxed_1202_, v_i_boxed_1203_, v_b_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_as_1189_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1224_, lean_object* v_stx_1225_, uint8_t v___x_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v___f_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
if (v___x_1224_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_1240_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v_tk_1242_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1314_; uint8_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v_stxForSuggestion_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; uint8_t v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; uint8_t v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; uint8_t v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; uint8_t v___y_1553_; lean_object* v___y_1554_; uint8_t v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; uint8_t v___y_1563_; lean_object* v___y_1576_; uint8_t v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v_stxForExecution_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; uint8_t v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1657_; uint8_t v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; uint8_t v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; uint8_t v___y_1757_; uint8_t v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; uint8_t v___y_1851_; lean_object* v___y_1852_; lean_object* v_argsArray_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; uint8_t v___y_1886_; lean_object* v___y_1887_; uint8_t v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; uint8_t v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; uint8_t v___y_2018_; lean_object* v_args_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___x_2040_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2046_; lean_object* v_o_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v_bang_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_1241_ = lean_unsigned_to_nat(0u);
v_tk_1242_ = l_Lean_Syntax_getArg(v_stx_1225_, v___x_1241_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2099_ = l_Lean_Syntax_getArg(v_stx_1225_, v___x_2040_);
v___x_2100_ = l_Lean_Syntax_isNone(v___x_2099_);
if (v___x_2100_ == 0)
{
uint8_t v___x_2101_; 
lean_inc(v___x_2099_);
v___x_2101_ = l_Lean_Syntax_matchesNull(v___x_2099_, v___x_2040_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
lean_dec(v___x_2099_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_2102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2102_;
}
else
{
lean_object* v_bang_2103_; lean_object* v___x_2104_; 
v_bang_2103_ = l_Lean_Syntax_getArg(v___x_2099_, v___x_1241_);
lean_dec(v___x_2099_);
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_bang_2103_);
v_bang_2071_ = v___x_2104_;
v___y_2072_ = v___y_1231_;
v___y_2073_ = v___y_1232_;
v___y_2074_ = v___y_1233_;
v___y_2075_ = v___y_1234_;
v___y_2076_ = v___y_1235_;
v___y_2077_ = v___y_1236_;
v___y_2078_ = v___y_1237_;
v___y_2079_ = v___y_1238_;
goto v___jp_2070_;
}
}
else
{
lean_object* v___x_2105_; 
lean_dec(v___x_2099_);
v___x_2105_ = lean_box(0);
v_bang_2071_ = v___x_2105_;
v___y_2072_ = v___y_1231_;
v___y_2073_ = v___y_1232_;
v___y_2074_ = v___y_1233_;
v___y_2075_ = v___y_1234_;
v___y_2076_ = v___y_1235_;
v___y_2077_ = v___y_1236_;
v___y_2078_ = v___y_1237_;
v___y_2079_ = v___y_1238_;
goto v___jp_2070_;
}
v___jp_1243_:
{
lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_box(v___x_1226_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1258_, 0, v___y_1246_);
lean_closure_set(v___f_1258_, 1, v___x_1241_);
lean_closure_set(v___f_1258_, 2, v___x_1257_);
lean_closure_set(v___f_1258_, 3, v___y_1256_);
lean_closure_set(v___f_1258_, 4, v___y_1245_);
v___x_1259_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1244_, v___f_1258_, v___y_1253_, v___y_1248_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1247_, v___y_1249_, v___y_1254_);
lean_dec(v___y_1244_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_usedTheorems_1261_; lean_object* v_diag_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1304_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v_usedTheorems_1261_ = lean_ctor_get(v_a_1260_, 0);
v_diag_1262_ = lean_ctor_get(v_a_1260_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_a_1260_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1264_ = v_a_1260_;
v_isShared_1265_ = v_isSharedCheck_1304_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_diag_1262_);
lean_inc(v_usedTheorems_1261_);
lean_dec(v_a_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1304_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1255_, v_usedTheorems_1261_, v___y_1250_, v___y_1247_, v___y_1249_, v___y_1254_);
lean_dec_ref(v_usedTheorems_1261_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_ref_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_ref_1268_ = lean_ctor_get(v___y_1249_, 2);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_a_1267_);
lean_ctor_set(v___x_1264_, 0, v___x_1269_);
v___x_1271_ = v___x_1264_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_a_1267_);
v___x_1271_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
lean_ctor_set(v___x_1273_, 3, v___x_1272_);
lean_ctor_set(v___x_1273_, 4, v___x_1272_);
lean_ctor_set(v___x_1273_, 5, v___x_1272_);
lean_inc(v_ref_1268_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_ref_1268_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1276_ = 4;
v___x_1277_ = l_Lean_MessageData_nil;
v___x_1278_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1242_, v___x_1273_, v___x_1274_, v___x_1275_, v___x_1272_, v___x_1276_, v___x_1277_, v___y_1249_, v___y_1254_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1278_, 0);
lean_dec(v_unused_1286_);
v___x_1280_ = v___x_1278_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_dec(v___x_1278_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v_diag_1262_);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_diag_1262_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_diag_1262_);
v_a_1287_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1278_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1278_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_del_object(v___x_1264_);
lean_dec_ref(v_diag_1262_);
lean_dec(v_tk_1242_);
v_a_1296_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1266_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1266_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v___y_1255_);
lean_dec(v_tk_1242_);
v_a_1305_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1259_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1259_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
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
v___jp_1313_:
{
uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = 0;
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1330_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1316_, v___x_1328_, v___y_1315_, v___x_1328_, v___x_1329_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1316_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
if (lean_obj_tag(v___y_1317_) == 0)
{
lean_object* v_ctx_1332_; lean_object* v_simprocs_1333_; lean_object* v_dischargeWrapper_1334_; 
v_ctx_1332_ = lean_ctor_get(v_a_1331_, 0);
lean_inc_ref(v_ctx_1332_);
v_simprocs_1333_ = lean_ctor_get(v_a_1331_, 1);
lean_inc_ref(v_simprocs_1333_);
v_dischargeWrapper_1334_ = lean_ctor_get(v_a_1331_, 2);
lean_inc(v_dischargeWrapper_1334_);
lean_dec(v_a_1331_);
v___y_1244_ = v_dischargeWrapper_1334_;
v___y_1245_ = v_simprocs_1333_;
v___y_1246_ = v___y_1314_;
v___y_1247_ = v___y_1325_;
v___y_1248_ = v___y_1321_;
v___y_1249_ = v___y_1326_;
v___y_1250_ = v___y_1324_;
v___y_1251_ = v___y_1322_;
v___y_1252_ = v___y_1323_;
v___y_1253_ = v___y_1320_;
v___y_1254_ = v___y_1327_;
v___y_1255_ = v_stxForSuggestion_1319_;
v___y_1256_ = v_ctx_1332_;
goto v___jp_1243_;
}
else
{
lean_dec_ref_known(v___y_1317_, 1);
if (v___y_1318_ == 0)
{
lean_object* v_ctx_1335_; lean_object* v_simprocs_1336_; lean_object* v_dischargeWrapper_1337_; 
v_ctx_1335_ = lean_ctor_get(v_a_1331_, 0);
lean_inc_ref(v_ctx_1335_);
v_simprocs_1336_ = lean_ctor_get(v_a_1331_, 1);
lean_inc_ref(v_simprocs_1336_);
v_dischargeWrapper_1337_ = lean_ctor_get(v_a_1331_, 2);
lean_inc(v_dischargeWrapper_1337_);
lean_dec(v_a_1331_);
v___y_1244_ = v_dischargeWrapper_1337_;
v___y_1245_ = v_simprocs_1336_;
v___y_1246_ = v___y_1314_;
v___y_1247_ = v___y_1325_;
v___y_1248_ = v___y_1321_;
v___y_1249_ = v___y_1326_;
v___y_1250_ = v___y_1324_;
v___y_1251_ = v___y_1322_;
v___y_1252_ = v___y_1323_;
v___y_1253_ = v___y_1320_;
v___y_1254_ = v___y_1327_;
v___y_1255_ = v_stxForSuggestion_1319_;
v___y_1256_ = v_ctx_1335_;
goto v___jp_1243_;
}
else
{
lean_object* v_ctx_1338_; lean_object* v_simprocs_1339_; lean_object* v_dischargeWrapper_1340_; lean_object* v___x_1341_; 
v_ctx_1338_ = lean_ctor_get(v_a_1331_, 0);
lean_inc_ref(v_ctx_1338_);
v_simprocs_1339_ = lean_ctor_get(v_a_1331_, 1);
lean_inc_ref(v_simprocs_1339_);
v_dischargeWrapper_1340_ = lean_ctor_get(v_a_1331_, 2);
lean_inc(v_dischargeWrapper_1340_);
lean_dec(v_a_1331_);
v___x_1341_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1338_);
v___y_1244_ = v_dischargeWrapper_1340_;
v___y_1245_ = v_simprocs_1339_;
v___y_1246_ = v___y_1314_;
v___y_1247_ = v___y_1325_;
v___y_1248_ = v___y_1321_;
v___y_1249_ = v___y_1326_;
v___y_1250_ = v___y_1324_;
v___y_1251_ = v___y_1322_;
v___y_1252_ = v___y_1323_;
v___y_1253_ = v___y_1320_;
v___y_1254_ = v___y_1327_;
v___y_1255_ = v_stxForSuggestion_1319_;
v___y_1256_ = v___x_1341_;
goto v___jp_1243_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_stxForSuggestion_1319_);
lean_dec(v___y_1317_);
lean_dec(v___y_1314_);
lean_dec(v_tk_1242_);
v_a_1342_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1330_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1330_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
v___jp_1350_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc_ref(v___y_1372_);
v___x_1374_ = l_Array_append___redArg(v___y_1372_, v___y_1373_);
lean_dec_ref(v___y_1373_);
lean_inc(v___y_1358_);
lean_inc(v___y_1355_);
v___x_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1355_);
lean_ctor_set(v___x_1375_, 1, v___y_1358_);
lean_ctor_set(v___x_1375_, 2, v___x_1374_);
v___x_1376_ = l_Lean_Syntax_node6(v___y_1355_, v___y_1361_, v___y_1371_, v___y_1370_, v___y_1366_, v___y_1367_, v___y_1359_, v___x_1375_);
v___y_1314_ = v___y_1351_;
v___y_1315_ = v___y_1364_;
v___y_1316_ = v___y_1363_;
v___y_1317_ = v___y_1368_;
v___y_1318_ = v___y_1362_;
v_stxForSuggestion_1319_ = v___x_1376_;
v___y_1320_ = v___y_1354_;
v___y_1321_ = v___y_1369_;
v___y_1322_ = v___y_1357_;
v___y_1323_ = v___y_1353_;
v___y_1324_ = v___y_1365_;
v___y_1325_ = v___y_1356_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1360_;
goto v___jp_1313_;
}
v___jp_1377_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc_ref_n(v___y_1399_, 2);
v___x_1401_ = l_Array_append___redArg(v___y_1399_, v___y_1400_);
lean_dec_ref(v___y_1400_);
lean_inc_n(v___y_1385_, 3);
lean_inc_n(v___y_1382_, 5);
v___x_1402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1402_, 0, v___y_1382_);
lean_ctor_set(v___x_1402_, 1, v___y_1385_);
lean_ctor_set(v___x_1402_, 2, v___x_1401_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___y_1382_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1406_ = l_Lean_Syntax_SepArray_ofElems(v___x_1405_, v___y_1397_);
lean_dec_ref(v___y_1397_);
v___x_1407_ = l_Array_append___redArg(v___y_1399_, v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1408_, 0, v___y_1382_);
lean_ctor_set(v___x_1408_, 1, v___y_1385_);
lean_ctor_set(v___x_1408_, 2, v___x_1407_);
v___x_1409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1382_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_Syntax_node3(v___y_1382_, v___y_1385_, v___x_1404_, v___x_1408_, v___x_1410_);
if (lean_obj_tag(v___y_1394_) == 1)
{
lean_object* v_val_1412_; lean_object* v___x_1413_; 
v_val_1412_ = lean_ctor_get(v___y_1394_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___y_1394_, 1);
v___x_1413_ = l_Array_mkArray1___redArg(v_val_1412_);
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___x_1411_;
v___y_1360_ = v___y_1386_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1392_;
v___y_1364_ = v___y_1391_;
v___y_1365_ = v___y_1390_;
v___y_1366_ = v___y_1389_;
v___y_1367_ = v___x_1402_;
v___y_1368_ = v___y_1393_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1396_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v___y_1399_;
v___y_1373_ = v___x_1413_;
goto v___jp_1350_;
}
else
{
lean_object* v___x_1414_; 
lean_dec(v___y_1394_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1379_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___x_1411_;
v___y_1360_ = v___y_1386_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1392_;
v___y_1364_ = v___y_1391_;
v___y_1365_ = v___y_1390_;
v___y_1366_ = v___y_1389_;
v___y_1367_ = v___x_1402_;
v___y_1368_ = v___y_1393_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1396_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v___y_1399_;
v___y_1373_ = v___x_1414_;
goto v___jp_1350_;
}
}
v___jp_1415_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_inc_ref(v___y_1437_);
v___x_1439_ = l_Array_append___redArg(v___y_1437_, v___y_1438_);
lean_dec_ref(v___y_1438_);
lean_inc(v___y_1423_);
lean_inc(v___y_1420_);
v___x_1440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1420_);
lean_ctor_set(v___x_1440_, 1, v___y_1423_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
if (lean_obj_tag(v___y_1432_) == 1)
{
lean_object* v_val_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_val_1441_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___y_1432_, 1);
v___x_1442_ = l_Lean_SourceInfo_fromRef(v_val_1441_, v___x_1226_);
lean_dec(v_val_1441_);
v___x_1443_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Array_mkArray1___redArg(v___x_1444_);
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1423_;
v___y_1386_ = v___y_1424_;
v___y_1387_ = v___y_1425_;
v___y_1388_ = v___y_1426_;
v___y_1389_ = v___x_1440_;
v___y_1390_ = v___y_1429_;
v___y_1391_ = v___y_1428_;
v___y_1392_ = v___y_1427_;
v___y_1393_ = v___y_1430_;
v___y_1394_ = v___y_1431_;
v___y_1395_ = v___y_1433_;
v___y_1396_ = v___y_1435_;
v___y_1397_ = v___y_1434_;
v___y_1398_ = v___y_1436_;
v___y_1399_ = v___y_1437_;
v___y_1400_ = v___x_1445_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1446_; 
lean_dec(v___y_1432_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1423_;
v___y_1386_ = v___y_1424_;
v___y_1387_ = v___y_1425_;
v___y_1388_ = v___y_1426_;
v___y_1389_ = v___x_1440_;
v___y_1390_ = v___y_1429_;
v___y_1391_ = v___y_1428_;
v___y_1392_ = v___y_1427_;
v___y_1393_ = v___y_1430_;
v___y_1394_ = v___y_1431_;
v___y_1395_ = v___y_1433_;
v___y_1396_ = v___y_1435_;
v___y_1397_ = v___y_1434_;
v___y_1398_ = v___y_1436_;
v___y_1399_ = v___y_1437_;
v___y_1400_ = v___x_1446_;
goto v___jp_1377_;
}
}
v___jp_1447_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v___y_1463_);
v___x_1471_ = l_Array_append___redArg(v___y_1463_, v___y_1470_);
lean_dec_ref(v___y_1470_);
lean_inc(v___y_1455_);
lean_inc(v___y_1464_);
v___x_1472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1464_);
lean_ctor_set(v___x_1472_, 1, v___y_1455_);
lean_ctor_set(v___x_1472_, 2, v___x_1471_);
v___x_1473_ = l_Lean_Syntax_node6(v___y_1464_, v___y_1456_, v___y_1469_, v___y_1468_, v___y_1459_, v___y_1453_, v___y_1466_, v___x_1472_);
v___y_1314_ = v___y_1448_;
v___y_1315_ = v___y_1461_;
v___y_1316_ = v___y_1460_;
v___y_1317_ = v___y_1465_;
v___y_1318_ = v___y_1458_;
v_stxForSuggestion_1319_ = v___x_1473_;
v___y_1320_ = v___y_1451_;
v___y_1321_ = v___y_1467_;
v___y_1322_ = v___y_1454_;
v___y_1323_ = v___y_1450_;
v___y_1324_ = v___y_1462_;
v___y_1325_ = v___y_1452_;
v___y_1326_ = v___y_1449_;
v___y_1327_ = v___y_1457_;
goto v___jp_1313_;
}
v___jp_1474_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_inc_ref_n(v___y_1489_, 2);
v___x_1498_ = l_Array_append___redArg(v___y_1489_, v___y_1497_);
lean_dec_ref(v___y_1497_);
lean_inc_n(v___y_1481_, 3);
lean_inc_n(v___y_1490_, 5);
v___x_1499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1490_);
lean_ctor_set(v___x_1499_, 1, v___y_1481_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
v___x_1500_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___y_1490_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1503_ = l_Lean_Syntax_SepArray_ofElems(v___x_1502_, v___y_1495_);
lean_dec_ref(v___y_1495_);
v___x_1504_ = l_Array_append___redArg(v___y_1489_, v___x_1503_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1505_, 0, v___y_1490_);
lean_ctor_set(v___x_1505_, 1, v___y_1481_);
lean_ctor_set(v___x_1505_, 2, v___x_1504_);
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1490_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_Syntax_node3(v___y_1490_, v___y_1481_, v___x_1501_, v___x_1505_, v___x_1507_);
if (lean_obj_tag(v___y_1492_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_val_1509_ = lean_ctor_get(v___y_1492_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___y_1492_, 1);
v___x_1510_ = l_Array_mkArray1___redArg(v_val_1509_);
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___y_1476_;
v___y_1450_ = v___y_1477_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1479_;
v___y_1453_ = v___x_1499_;
v___y_1454_ = v___y_1480_;
v___y_1455_ = v___y_1481_;
v___y_1456_ = v___y_1482_;
v___y_1457_ = v___y_1483_;
v___y_1458_ = v___y_1484_;
v___y_1459_ = v___y_1485_;
v___y_1460_ = v___y_1488_;
v___y_1461_ = v___y_1487_;
v___y_1462_ = v___y_1486_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___x_1508_;
v___y_1467_ = v___y_1493_;
v___y_1468_ = v___y_1494_;
v___y_1469_ = v___y_1496_;
v___y_1470_ = v___x_1510_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v___y_1492_);
v___x_1511_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___y_1476_;
v___y_1450_ = v___y_1477_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1479_;
v___y_1453_ = v___x_1499_;
v___y_1454_ = v___y_1480_;
v___y_1455_ = v___y_1481_;
v___y_1456_ = v___y_1482_;
v___y_1457_ = v___y_1483_;
v___y_1458_ = v___y_1484_;
v___y_1459_ = v___y_1485_;
v___y_1460_ = v___y_1488_;
v___y_1461_ = v___y_1487_;
v___y_1462_ = v___y_1486_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___x_1508_;
v___y_1467_ = v___y_1493_;
v___y_1468_ = v___y_1494_;
v___y_1469_ = v___y_1496_;
v___y_1470_ = v___x_1511_;
goto v___jp_1447_;
}
}
v___jp_1512_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc_ref(v___y_1525_);
v___x_1536_ = l_Array_append___redArg(v___y_1525_, v___y_1535_);
lean_dec_ref(v___y_1535_);
lean_inc(v___y_1519_);
lean_inc(v___y_1526_);
v___x_1537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1537_, 0, v___y_1526_);
lean_ctor_set(v___x_1537_, 1, v___y_1519_);
lean_ctor_set(v___x_1537_, 2, v___x_1536_);
if (lean_obj_tag(v___y_1530_) == 1)
{
lean_object* v_val_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_val_1538_ = lean_ctor_get(v___y_1530_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v___y_1530_, 1);
v___x_1539_ = l_Lean_SourceInfo_fromRef(v_val_1538_, v___x_1226_);
lean_dec(v_val_1538_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Array_mkArray1___redArg(v___x_1541_);
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1515_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1517_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1522_;
v___y_1485_ = v___x_1537_;
v___y_1486_ = v___y_1527_;
v___y_1487_ = v___y_1524_;
v___y_1488_ = v___y_1523_;
v___y_1489_ = v___y_1525_;
v___y_1490_ = v___y_1526_;
v___y_1491_ = v___y_1528_;
v___y_1492_ = v___y_1529_;
v___y_1493_ = v___y_1531_;
v___y_1494_ = v___y_1533_;
v___y_1495_ = v___y_1532_;
v___y_1496_ = v___y_1534_;
v___y_1497_ = v___x_1542_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1543_; 
lean_dec(v___y_1530_);
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1515_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1517_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1522_;
v___y_1485_ = v___x_1537_;
v___y_1486_ = v___y_1527_;
v___y_1487_ = v___y_1524_;
v___y_1488_ = v___y_1523_;
v___y_1489_ = v___y_1525_;
v___y_1490_ = v___y_1526_;
v___y_1491_ = v___y_1528_;
v___y_1492_ = v___y_1529_;
v___y_1493_ = v___y_1531_;
v___y_1494_ = v___y_1533_;
v___y_1495_ = v___y_1532_;
v___y_1496_ = v___y_1534_;
v___y_1497_ = v___x_1543_;
goto v___jp_1474_;
}
}
v___jp_1544_:
{
lean_object* v_ref_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_ref_1564_ = lean_ctor_get(v___y_1546_, 2);
v___x_1565_ = l_Lean_SourceInfo_fromRef(v_ref_1564_, v___y_1563_);
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1567_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_1566_);
v___x_1568_ = l_Lean_SourceInfo_fromRef(v_tk_1242_, v___x_1226_);
v___x_1569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___x_1566_);
v___x_1570_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1571_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1552_) == 1)
{
lean_object* v_val_1572_; lean_object* v___x_1573_; 
v_val_1572_ = lean_ctor_get(v___y_1552_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___y_1552_, 1);
v___x_1573_ = l_Array_mkArray1___redArg(v_val_1572_);
v___y_1513_ = v___y_1545_;
v___y_1514_ = v___y_1546_;
v___y_1515_ = v___y_1547_;
v___y_1516_ = v___y_1548_;
v___y_1517_ = v___y_1549_;
v___y_1518_ = v___y_1550_;
v___y_1519_ = v___x_1570_;
v___y_1520_ = v___x_1567_;
v___y_1521_ = v___y_1551_;
v___y_1522_ = v___y_1553_;
v___y_1523_ = v___y_1554_;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v___x_1571_;
v___y_1526_ = v___x_1565_;
v___y_1527_ = v___y_1556_;
v___y_1528_ = v___y_1557_;
v___y_1529_ = v___y_1558_;
v___y_1530_ = v___y_1559_;
v___y_1531_ = v___y_1560_;
v___y_1532_ = v___y_1562_;
v___y_1533_ = v___y_1561_;
v___y_1534_ = v___x_1569_;
v___y_1535_ = v___x_1573_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1574_; 
lean_dec(v___y_1552_);
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1513_ = v___y_1545_;
v___y_1514_ = v___y_1546_;
v___y_1515_ = v___y_1547_;
v___y_1516_ = v___y_1548_;
v___y_1517_ = v___y_1549_;
v___y_1518_ = v___y_1550_;
v___y_1519_ = v___x_1570_;
v___y_1520_ = v___x_1567_;
v___y_1521_ = v___y_1551_;
v___y_1522_ = v___y_1553_;
v___y_1523_ = v___y_1554_;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v___x_1571_;
v___y_1526_ = v___x_1565_;
v___y_1527_ = v___y_1556_;
v___y_1528_ = v___y_1557_;
v___y_1529_ = v___y_1558_;
v___y_1530_ = v___y_1559_;
v___y_1531_ = v___y_1560_;
v___y_1532_ = v___y_1562_;
v___y_1533_ = v___y_1561_;
v___y_1534_ = v___x_1569_;
v___y_1535_ = v___x_1574_;
goto v___jp_1512_;
}
}
v___jp_1575_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1578_);
if (lean_obj_tag(v___y_1579_) == 0)
{
lean_object* v_a_1595_; uint8_t v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = 0;
v___y_1545_ = v___y_1576_;
v___y_1546_ = v___y_1592_;
v___y_1547_ = v___y_1589_;
v___y_1548_ = v___y_1586_;
v___y_1549_ = v___y_1591_;
v___y_1550_ = v___y_1588_;
v___y_1551_ = v___y_1593_;
v___y_1552_ = v___y_1583_;
v___y_1553_ = v___y_1584_;
v___y_1554_ = v_stxForExecution_1585_;
v___y_1555_ = v___y_1577_;
v___y_1556_ = v___y_1590_;
v___y_1557_ = v___y_1579_;
v___y_1558_ = v___y_1580_;
v___y_1559_ = v___y_1581_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v_a_1595_;
v___y_1562_ = v___y_1582_;
v___y_1563_ = v___x_1596_;
goto v___jp_1544_;
}
else
{
if (v___y_1584_ == 0)
{
lean_object* v_a_1597_; 
v_a_1597_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1594_);
v___y_1545_ = v___y_1576_;
v___y_1546_ = v___y_1592_;
v___y_1547_ = v___y_1589_;
v___y_1548_ = v___y_1586_;
v___y_1549_ = v___y_1591_;
v___y_1550_ = v___y_1588_;
v___y_1551_ = v___y_1593_;
v___y_1552_ = v___y_1583_;
v___y_1553_ = v___y_1584_;
v___y_1554_ = v_stxForExecution_1585_;
v___y_1555_ = v___y_1577_;
v___y_1556_ = v___y_1590_;
v___y_1557_ = v___y_1579_;
v___y_1558_ = v___y_1580_;
v___y_1559_ = v___y_1581_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v_a_1597_;
v___y_1562_ = v___y_1582_;
v___y_1563_ = v___y_1584_;
goto v___jp_1544_;
}
else
{
lean_object* v_a_1598_; lean_object* v_ref_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1598_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1594_);
v_ref_1599_ = lean_ctor_get(v___y_1592_, 2);
v___x_1600_ = 0;
v___x_1601_ = l_Lean_SourceInfo_fromRef(v_ref_1599_, v___x_1600_);
v___x_1602_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1603_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_1602_);
v___x_1604_ = l_Lean_SourceInfo_fromRef(v_tk_1242_, v___x_1226_);
v___x_1605_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1608_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1583_) == 1)
{
lean_object* v_val_1609_; lean_object* v___x_1610_; 
v_val_1609_ = lean_ctor_get(v___y_1583_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v___y_1583_, 1);
v___x_1610_ = l_Array_mkArray1___redArg(v_val_1609_);
v___y_1416_ = v___y_1576_;
v___y_1417_ = v___y_1592_;
v___y_1418_ = v___y_1589_;
v___y_1419_ = v___y_1586_;
v___y_1420_ = v___x_1601_;
v___y_1421_ = v___y_1591_;
v___y_1422_ = v___y_1588_;
v___y_1423_ = v___x_1607_;
v___y_1424_ = v___y_1593_;
v___y_1425_ = v___x_1603_;
v___y_1426_ = v___y_1584_;
v___y_1427_ = v_stxForExecution_1585_;
v___y_1428_ = v___y_1577_;
v___y_1429_ = v___y_1590_;
v___y_1430_ = v___y_1579_;
v___y_1431_ = v___y_1580_;
v___y_1432_ = v___y_1581_;
v___y_1433_ = v___y_1587_;
v___y_1434_ = v___y_1582_;
v___y_1435_ = v_a_1598_;
v___y_1436_ = v___x_1606_;
v___y_1437_ = v___x_1608_;
v___y_1438_ = v___x_1610_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1611_; 
lean_dec(v___y_1583_);
v___x_1611_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1416_ = v___y_1576_;
v___y_1417_ = v___y_1592_;
v___y_1418_ = v___y_1589_;
v___y_1419_ = v___y_1586_;
v___y_1420_ = v___x_1601_;
v___y_1421_ = v___y_1591_;
v___y_1422_ = v___y_1588_;
v___y_1423_ = v___x_1607_;
v___y_1424_ = v___y_1593_;
v___y_1425_ = v___x_1603_;
v___y_1426_ = v___y_1584_;
v___y_1427_ = v_stxForExecution_1585_;
v___y_1428_ = v___y_1577_;
v___y_1429_ = v___y_1590_;
v___y_1430_ = v___y_1579_;
v___y_1431_ = v___y_1580_;
v___y_1432_ = v___y_1581_;
v___y_1433_ = v___y_1587_;
v___y_1434_ = v___y_1582_;
v___y_1435_ = v_a_1598_;
v___y_1436_ = v___x_1606_;
v___y_1437_ = v___x_1608_;
v___y_1438_ = v___x_1611_;
goto v___jp_1415_;
}
}
}
}
v___jp_1612_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc_ref(v___y_1637_);
v___x_1639_ = l_Array_append___redArg(v___y_1637_, v___y_1638_);
lean_dec_ref(v___y_1638_);
lean_inc(v___y_1614_);
lean_inc(v___y_1630_);
v___x_1640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1630_);
lean_ctor_set(v___x_1640_, 1, v___y_1614_);
lean_ctor_set(v___x_1640_, 2, v___x_1639_);
lean_inc(v___y_1623_);
v___x_1641_ = l_Lean_Syntax_node6(v___y_1630_, v___y_1616_, v___y_1620_, v___y_1623_, v___y_1618_, v___y_1634_, v___y_1633_, v___x_1640_);
v___y_1576_ = v___y_1613_;
v___y_1577_ = v___y_1631_;
v___y_1578_ = v___y_1623_;
v___y_1579_ = v___y_1621_;
v___y_1580_ = v___y_1632_;
v___y_1581_ = v___y_1622_;
v___y_1582_ = v___y_1636_;
v___y_1583_ = v___y_1629_;
v___y_1584_ = v___y_1619_;
v_stxForExecution_1585_ = v___x_1641_;
v___y_1586_ = v___y_1626_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___y_1624_;
v___y_1589_ = v___y_1628_;
v___y_1590_ = v___y_1617_;
v___y_1591_ = v___y_1635_;
v___y_1592_ = v___y_1627_;
v___y_1593_ = v___y_1615_;
goto v___jp_1575_;
}
v___jp_1642_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_inc_ref_n(v___y_1665_, 2);
v___x_1667_ = l_Array_append___redArg(v___y_1665_, v___y_1666_);
lean_dec_ref(v___y_1666_);
lean_inc_n(v___y_1645_, 3);
lean_inc_n(v___y_1657_, 5);
v___x_1668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1668_, 0, v___y_1657_);
lean_ctor_set(v___x_1668_, 1, v___y_1645_);
lean_ctor_set(v___x_1668_, 2, v___x_1667_);
v___x_1669_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___y_1657_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1672_ = l_Lean_Syntax_SepArray_ofElems(v___x_1671_, v___y_1664_);
v___x_1673_ = l_Array_append___redArg(v___y_1665_, v___x_1672_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1657_);
lean_ctor_set(v___x_1674_, 1, v___y_1645_);
lean_ctor_set(v___x_1674_, 2, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___y_1657_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1645_, v___x_1670_, v___x_1674_, v___x_1676_);
if (lean_obj_tag(v___y_1661_) == 1)
{
lean_object* v_val_1678_; lean_object* v___x_1679_; 
v_val_1678_ = lean_ctor_get(v___y_1661_, 0);
lean_inc(v_val_1678_);
v___x_1679_ = l_Array_mkArray1___redArg(v_val_1678_);
v___y_1613_ = v___y_1643_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1653_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1662_;
v___y_1623_ = v___y_1644_;
v___y_1624_ = v___y_1651_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1649_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1655_;
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1657_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___y_1661_;
v___y_1633_ = v___x_1677_;
v___y_1634_ = v___x_1668_;
v___y_1635_ = v___y_1663_;
v___y_1636_ = v___y_1664_;
v___y_1637_ = v___y_1665_;
v___y_1638_ = v___x_1679_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1613_ = v___y_1643_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1653_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1662_;
v___y_1623_ = v___y_1644_;
v___y_1624_ = v___y_1651_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1649_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1655_;
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1657_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___y_1661_;
v___y_1633_ = v___x_1677_;
v___y_1634_ = v___x_1668_;
v___y_1635_ = v___y_1663_;
v___y_1636_ = v___y_1664_;
v___y_1637_ = v___y_1665_;
v___y_1638_ = v___x_1680_;
goto v___jp_1612_;
}
}
v___jp_1681_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_inc_ref(v___y_1703_);
v___x_1705_ = l_Array_append___redArg(v___y_1703_, v___y_1704_);
lean_dec_ref(v___y_1704_);
lean_inc(v___y_1683_);
lean_inc(v___y_1695_);
v___x_1706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1706_, 0, v___y_1695_);
lean_ctor_set(v___x_1706_, 1, v___y_1683_);
lean_ctor_set(v___x_1706_, 2, v___x_1705_);
if (lean_obj_tag(v___y_1700_) == 1)
{
lean_object* v_val_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_val_1707_ = lean_ctor_get(v___y_1700_, 0);
v___x_1708_ = l_Lean_SourceInfo_fromRef(v_val_1707_, v___x_1226_);
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = l_Array_mkArray1___redArg(v___x_1710_);
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___y_1684_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1685_;
v___y_1647_ = v___y_1686_;
v___y_1648_ = v___y_1687_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1690_;
v___y_1652_ = v___y_1691_;
v___y_1653_ = v___x_1706_;
v___y_1654_ = v___y_1693_;
v___y_1655_ = v___y_1694_;
v___y_1656_ = v___y_1692_;
v___y_1657_ = v___y_1695_;
v___y_1658_ = v___y_1696_;
v___y_1659_ = v___y_1698_;
v___y_1660_ = v___y_1697_;
v___y_1661_ = v___y_1699_;
v___y_1662_ = v___y_1700_;
v___y_1663_ = v___y_1702_;
v___y_1664_ = v___y_1701_;
v___y_1665_ = v___y_1703_;
v___y_1666_ = v___x_1711_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___y_1684_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1685_;
v___y_1647_ = v___y_1686_;
v___y_1648_ = v___y_1687_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1690_;
v___y_1652_ = v___y_1691_;
v___y_1653_ = v___x_1706_;
v___y_1654_ = v___y_1693_;
v___y_1655_ = v___y_1694_;
v___y_1656_ = v___y_1692_;
v___y_1657_ = v___y_1695_;
v___y_1658_ = v___y_1696_;
v___y_1659_ = v___y_1698_;
v___y_1660_ = v___y_1697_;
v___y_1661_ = v___y_1699_;
v___y_1662_ = v___y_1700_;
v___y_1663_ = v___y_1702_;
v___y_1664_ = v___y_1701_;
v___y_1665_ = v___y_1703_;
v___y_1666_ = v___x_1712_;
goto v___jp_1642_;
}
}
v___jp_1713_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_inc_ref(v___y_1720_);
v___x_1740_ = l_Array_append___redArg(v___y_1720_, v___y_1739_);
lean_dec_ref(v___y_1739_);
lean_inc(v___y_1724_);
lean_inc(v___y_1734_);
v___x_1741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1741_, 0, v___y_1734_);
lean_ctor_set(v___x_1741_, 1, v___y_1724_);
lean_ctor_set(v___x_1741_, 2, v___x_1740_);
lean_inc(v___y_1722_);
v___x_1742_ = l_Lean_Syntax_node6(v___y_1734_, v___y_1721_, v___y_1723_, v___y_1722_, v___y_1733_, v___y_1730_, v___y_1738_, v___x_1741_);
v___y_1576_ = v___y_1714_;
v___y_1577_ = v___y_1732_;
v___y_1578_ = v___y_1722_;
v___y_1579_ = v___y_1718_;
v___y_1580_ = v___y_1735_;
v___y_1581_ = v___y_1719_;
v___y_1582_ = v___y_1737_;
v___y_1583_ = v___y_1731_;
v___y_1584_ = v___y_1717_;
v_stxForExecution_1585_ = v___x_1742_;
v___y_1586_ = v___y_1727_;
v___y_1587_ = v___y_1726_;
v___y_1588_ = v___y_1725_;
v___y_1589_ = v___y_1729_;
v___y_1590_ = v___y_1716_;
v___y_1591_ = v___y_1736_;
v___y_1592_ = v___y_1728_;
v___y_1593_ = v___y_1715_;
goto v___jp_1575_;
}
v___jp_1743_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_inc_ref_n(v___y_1766_, 2);
v___x_1768_ = l_Array_append___redArg(v___y_1766_, v___y_1767_);
lean_dec_ref(v___y_1767_);
lean_inc_n(v___y_1747_, 3);
lean_inc_n(v___y_1760_, 5);
v___x_1769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1769_, 0, v___y_1760_);
lean_ctor_set(v___x_1769_, 1, v___y_1747_);
lean_ctor_set(v___x_1769_, 2, v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___y_1760_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1773_ = l_Lean_Syntax_SepArray_ofElems(v___x_1772_, v___y_1765_);
v___x_1774_ = l_Array_append___redArg(v___y_1766_, v___x_1773_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1775_, 0, v___y_1760_);
lean_ctor_set(v___x_1775_, 1, v___y_1747_);
lean_ctor_set(v___x_1775_, 2, v___x_1774_);
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___y_1760_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_Syntax_node3(v___y_1760_, v___y_1747_, v___x_1771_, v___x_1775_, v___x_1777_);
if (lean_obj_tag(v___y_1762_) == 1)
{
lean_object* v_val_1779_; lean_object* v___x_1780_; 
v_val_1779_ = lean_ctor_get(v___y_1762_, 0);
lean_inc(v_val_1779_);
v___x_1780_ = l_Array_mkArray1___redArg(v_val_1779_);
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1748_;
v___y_1716_ = v___y_1750_;
v___y_1717_ = v___y_1757_;
v___y_1718_ = v___y_1761_;
v___y_1719_ = v___y_1763_;
v___y_1720_ = v___y_1766_;
v___y_1721_ = v___y_1745_;
v___y_1722_ = v___y_1746_;
v___y_1723_ = v___y_1749_;
v___y_1724_ = v___y_1747_;
v___y_1725_ = v___y_1753_;
v___y_1726_ = v___y_1752_;
v___y_1727_ = v___y_1751_;
v___y_1728_ = v___y_1754_;
v___y_1729_ = v___y_1756_;
v___y_1730_ = v___x_1769_;
v___y_1731_ = v___y_1755_;
v___y_1732_ = v___y_1758_;
v___y_1733_ = v___y_1759_;
v___y_1734_ = v___y_1760_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v___y_1764_;
v___y_1737_ = v___y_1765_;
v___y_1738_ = v___x_1778_;
v___y_1739_ = v___x_1780_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1748_;
v___y_1716_ = v___y_1750_;
v___y_1717_ = v___y_1757_;
v___y_1718_ = v___y_1761_;
v___y_1719_ = v___y_1763_;
v___y_1720_ = v___y_1766_;
v___y_1721_ = v___y_1745_;
v___y_1722_ = v___y_1746_;
v___y_1723_ = v___y_1749_;
v___y_1724_ = v___y_1747_;
v___y_1725_ = v___y_1753_;
v___y_1726_ = v___y_1752_;
v___y_1727_ = v___y_1751_;
v___y_1728_ = v___y_1754_;
v___y_1729_ = v___y_1756_;
v___y_1730_ = v___x_1769_;
v___y_1731_ = v___y_1755_;
v___y_1732_ = v___y_1758_;
v___y_1733_ = v___y_1759_;
v___y_1734_ = v___y_1760_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v___y_1764_;
v___y_1737_ = v___y_1765_;
v___y_1738_ = v___x_1778_;
v___y_1739_ = v___x_1781_;
goto v___jp_1713_;
}
}
v___jp_1782_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_inc_ref(v___y_1804_);
v___x_1806_ = l_Array_append___redArg(v___y_1804_, v___y_1805_);
lean_dec_ref(v___y_1805_);
lean_inc(v___y_1786_);
lean_inc(v___y_1798_);
v___x_1807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1807_, 0, v___y_1798_);
lean_ctor_set(v___x_1807_, 1, v___y_1786_);
lean_ctor_set(v___x_1807_, 2, v___x_1806_);
if (lean_obj_tag(v___y_1801_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_val_1808_ = lean_ctor_get(v___y_1801_, 0);
v___x_1809_ = l_Lean_SourceInfo_fromRef(v_val_1808_, v___x_1226_);
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Array_mkArray1___redArg(v___x_1811_);
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___y_1787_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1790_;
v___y_1752_ = v___y_1791_;
v___y_1753_ = v___y_1792_;
v___y_1754_ = v___y_1793_;
v___y_1755_ = v___y_1796_;
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___y_1794_;
v___y_1758_ = v___y_1797_;
v___y_1759_ = v___x_1807_;
v___y_1760_ = v___y_1798_;
v___y_1761_ = v___y_1799_;
v___y_1762_ = v___y_1800_;
v___y_1763_ = v___y_1801_;
v___y_1764_ = v___y_1803_;
v___y_1765_ = v___y_1802_;
v___y_1766_ = v___y_1804_;
v___y_1767_ = v___x_1812_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___y_1787_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1790_;
v___y_1752_ = v___y_1791_;
v___y_1753_ = v___y_1792_;
v___y_1754_ = v___y_1793_;
v___y_1755_ = v___y_1796_;
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___y_1794_;
v___y_1758_ = v___y_1797_;
v___y_1759_ = v___x_1807_;
v___y_1760_ = v___y_1798_;
v___y_1761_ = v___y_1799_;
v___y_1762_ = v___y_1800_;
v___y_1763_ = v___y_1801_;
v___y_1764_ = v___y_1803_;
v___y_1765_ = v___y_1802_;
v___y_1766_ = v___y_1804_;
v___y_1767_ = v___x_1813_;
goto v___jp_1743_;
}
}
v___jp_1814_:
{
lean_object* v_ref_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_ref_1833_ = lean_ctor_get(v___y_1822_, 2);
v___x_1834_ = l_Lean_SourceInfo_fromRef(v_ref_1833_, v___y_1832_);
v___x_1835_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1229_);
lean_inc_ref(v___x_1228_);
lean_inc_ref(v___x_1227_);
v___x_1836_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_1835_);
v___x_1837_ = l_Lean_SourceInfo_fromRef(v_tk_1242_, v___x_1226_);
v___x_1838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1835_);
v___x_1839_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1840_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1825_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1842_; 
v_val_1841_ = lean_ctor_get(v___y_1825_, 0);
lean_inc(v_val_1841_);
v___x_1842_ = l_Array_mkArray1___redArg(v_val_1841_);
v___y_1783_ = v___y_1815_;
v___y_1784_ = v___x_1836_;
v___y_1785_ = v___y_1816_;
v___y_1786_ = v___x_1839_;
v___y_1787_ = v___y_1817_;
v___y_1788_ = v___x_1838_;
v___y_1789_ = v___y_1818_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1821_;
v___y_1793_ = v___y_1822_;
v___y_1794_ = v___y_1823_;
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___y_1825_;
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___x_1834_;
v___y_1799_ = v___y_1827_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1831_;
v___y_1803_ = v___y_1830_;
v___y_1804_ = v___x_1840_;
v___y_1805_ = v___x_1842_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1783_ = v___y_1815_;
v___y_1784_ = v___x_1836_;
v___y_1785_ = v___y_1816_;
v___y_1786_ = v___x_1839_;
v___y_1787_ = v___y_1817_;
v___y_1788_ = v___x_1838_;
v___y_1789_ = v___y_1818_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1820_;
v___y_1792_ = v___y_1821_;
v___y_1793_ = v___y_1822_;
v___y_1794_ = v___y_1823_;
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___y_1825_;
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___x_1834_;
v___y_1799_ = v___y_1827_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1831_;
v___y_1803_ = v___y_1830_;
v___y_1804_ = v___x_1840_;
v___y_1805_ = v___x_1843_;
goto v___jp_1782_;
}
}
v___jp_1844_:
{
if (lean_obj_tag(v___y_1848_) == 0)
{
uint8_t v___x_1862_; 
v___x_1862_ = 0;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1847_;
v___y_1817_ = v___y_1861_;
v___y_1818_ = v___y_1858_;
v___y_1819_ = v___y_1854_;
v___y_1820_ = v___y_1855_;
v___y_1821_ = v___y_1856_;
v___y_1822_ = v___y_1860_;
v___y_1823_ = v___y_1851_;
v___y_1824_ = v___y_1857_;
v___y_1825_ = v___y_1852_;
v___y_1826_ = v___y_1846_;
v___y_1827_ = v___y_1848_;
v___y_1828_ = v___y_1849_;
v___y_1829_ = v___y_1850_;
v___y_1830_ = v___y_1859_;
v___y_1831_ = v_argsArray_1853_;
v___y_1832_ = v___x_1862_;
goto v___jp_1814_;
}
else
{
if (v___y_1851_ == 0)
{
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1847_;
v___y_1817_ = v___y_1861_;
v___y_1818_ = v___y_1858_;
v___y_1819_ = v___y_1854_;
v___y_1820_ = v___y_1855_;
v___y_1821_ = v___y_1856_;
v___y_1822_ = v___y_1860_;
v___y_1823_ = v___y_1851_;
v___y_1824_ = v___y_1857_;
v___y_1825_ = v___y_1852_;
v___y_1826_ = v___y_1846_;
v___y_1827_ = v___y_1848_;
v___y_1828_ = v___y_1849_;
v___y_1829_ = v___y_1850_;
v___y_1830_ = v___y_1859_;
v___y_1831_ = v_argsArray_1853_;
v___y_1832_ = v___y_1851_;
goto v___jp_1814_;
}
else
{
lean_object* v_ref_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_ref_1863_ = lean_ctor_get(v___y_1860_, 2);
v___x_1864_ = 0;
v___x_1865_ = l_Lean_SourceInfo_fromRef(v_ref_1863_, v___x_1864_);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1229_);
lean_inc_ref(v___x_1228_);
lean_inc_ref(v___x_1227_);
v___x_1867_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_1866_);
v___x_1868_ = l_Lean_SourceInfo_fromRef(v_tk_1242_, v___x_1226_);
v___x_1869_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1872_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1852_) == 1)
{
lean_object* v_val_1873_; lean_object* v___x_1874_; 
v_val_1873_ = lean_ctor_get(v___y_1852_, 0);
lean_inc(v_val_1873_);
v___x_1874_ = l_Array_mkArray1___redArg(v_val_1873_);
v___y_1682_ = v___y_1845_;
v___y_1683_ = v___x_1871_;
v___y_1684_ = v___y_1847_;
v___y_1685_ = v___y_1861_;
v___y_1686_ = v___x_1867_;
v___y_1687_ = v___y_1858_;
v___y_1688_ = v___y_1854_;
v___y_1689_ = v___y_1855_;
v___y_1690_ = v___y_1856_;
v___y_1691_ = v___y_1860_;
v___y_1692_ = v___y_1851_;
v___y_1693_ = v___y_1852_;
v___y_1694_ = v___y_1857_;
v___y_1695_ = v___x_1865_;
v___y_1696_ = v___y_1846_;
v___y_1697_ = v___y_1848_;
v___y_1698_ = v___x_1870_;
v___y_1699_ = v___y_1849_;
v___y_1700_ = v___y_1850_;
v___y_1701_ = v_argsArray_1853_;
v___y_1702_ = v___y_1859_;
v___y_1703_ = v___x_1872_;
v___y_1704_ = v___x_1874_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1875_; 
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1682_ = v___y_1845_;
v___y_1683_ = v___x_1871_;
v___y_1684_ = v___y_1847_;
v___y_1685_ = v___y_1861_;
v___y_1686_ = v___x_1867_;
v___y_1687_ = v___y_1858_;
v___y_1688_ = v___y_1854_;
v___y_1689_ = v___y_1855_;
v___y_1690_ = v___y_1856_;
v___y_1691_ = v___y_1860_;
v___y_1692_ = v___y_1851_;
v___y_1693_ = v___y_1852_;
v___y_1694_ = v___y_1857_;
v___y_1695_ = v___x_1865_;
v___y_1696_ = v___y_1846_;
v___y_1697_ = v___y_1848_;
v___y_1698_ = v___x_1870_;
v___y_1699_ = v___y_1849_;
v___y_1700_ = v___y_1850_;
v___y_1701_ = v_argsArray_1853_;
v___y_1702_ = v___y_1859_;
v___y_1703_ = v___x_1872_;
v___y_1704_ = v___x_1875_;
goto v___jp_1681_;
}
}
}
}
v___jp_1876_:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1884_, v___y_1892_, v___y_1878_, v___y_1880_, v___y_1883_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l_Lean_LibrarySuggestions_select(v_a_1896_, v___y_1894_, v___y_1892_, v___y_1878_, v___y_1880_, v___y_1883_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; size_t v_sz_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v_sz_1899_ = lean_array_size(v_a_1898_);
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1898_, v_sz_1899_, v___x_1900_, v___y_1891_, v___y_1887_, v___y_1884_, v___y_1881_, v___y_1882_, v___y_1892_, v___y_1878_, v___y_1880_, v___y_1883_);
lean_dec(v_a_1898_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___y_1845_ = v___y_1877_;
v___y_1846_ = v___y_1888_;
v___y_1847_ = v___y_1879_;
v___y_1848_ = v___y_1889_;
v___y_1849_ = v___y_1890_;
v___y_1850_ = v___y_1893_;
v___y_1851_ = v___y_1886_;
v___y_1852_ = v___y_1885_;
v_argsArray_1853_ = v_a_1902_;
v___y_1854_ = v___y_1887_;
v___y_1855_ = v___y_1884_;
v___y_1856_ = v___y_1881_;
v___y_1857_ = v___y_1882_;
v___y_1858_ = v___y_1892_;
v___y_1859_ = v___y_1878_;
v___y_1860_ = v___y_1880_;
v___y_1861_ = v___y_1883_;
goto v___jp_1844_;
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v___y_1893_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1885_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v_a_1903_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1901_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1885_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v_a_1911_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1897_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1897_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1885_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v_a_1919_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1895_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1895_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
v___jp_1927_:
{
lean_object* v_config_1946_; uint8_t v_suggestions_1947_; 
v_config_1946_ = lean_ctor_get(v___y_1944_, 0);
lean_inc_ref(v_config_1946_);
lean_dec_ref(v___y_1944_);
v_suggestions_1947_ = lean_ctor_get_uint8(v_config_1946_, sizeof(void*)*3 + 26);
if (v_suggestions_1947_ == 0)
{
lean_dec_ref(v_config_1946_);
lean_dec_ref(v___f_1230_);
v___y_1845_ = v___y_1928_;
v___y_1846_ = v___y_1939_;
v___y_1847_ = v___y_1930_;
v___y_1848_ = v___y_1940_;
v___y_1849_ = v___y_1941_;
v___y_1850_ = v___y_1943_;
v___y_1851_ = v___y_1937_;
v___y_1852_ = v___y_1936_;
v_argsArray_1853_ = v___y_1945_;
v___y_1854_ = v___y_1938_;
v___y_1855_ = v___y_1935_;
v___y_1856_ = v___y_1932_;
v___y_1857_ = v___y_1933_;
v___y_1858_ = v___y_1942_;
v___y_1859_ = v___y_1929_;
v___y_1860_ = v___y_1931_;
v___y_1861_ = v___y_1934_;
goto v___jp_1844_;
}
else
{
lean_object* v_maxSuggestions_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_maxSuggestions_1948_ = lean_ctor_get(v_config_1946_, 2);
lean_inc(v_maxSuggestions_1948_);
lean_dec_ref(v_config_1946_);
v___x_1949_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1950_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1948_) == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_unsigned_to_nat(100u);
v___x_1952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1949_);
lean_ctor_set(v___x_1952_, 2, v___f_1230_);
lean_ctor_set(v___x_1952_, 3, v___x_1950_);
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1932_;
v___y_1882_ = v___y_1933_;
v___y_1883_ = v___y_1934_;
v___y_1884_ = v___y_1935_;
v___y_1885_ = v___y_1936_;
v___y_1886_ = v___y_1937_;
v___y_1887_ = v___y_1938_;
v___y_1888_ = v___y_1939_;
v___y_1889_ = v___y_1940_;
v___y_1890_ = v___y_1941_;
v___y_1891_ = v___y_1945_;
v___y_1892_ = v___y_1942_;
v___y_1893_ = v___y_1943_;
v___y_1894_ = v___x_1952_;
goto v___jp_1876_;
}
else
{
lean_object* v_val_1953_; lean_object* v___x_1954_; 
v_val_1953_ = lean_ctor_get(v_maxSuggestions_1948_, 0);
lean_inc(v_val_1953_);
lean_dec_ref_known(v_maxSuggestions_1948_, 1);
v___x_1954_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1954_, 0, v_val_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1949_);
lean_ctor_set(v___x_1954_, 2, v___f_1230_);
lean_ctor_set(v___x_1954_, 3, v___x_1950_);
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1932_;
v___y_1882_ = v___y_1933_;
v___y_1883_ = v___y_1934_;
v___y_1884_ = v___y_1935_;
v___y_1885_ = v___y_1936_;
v___y_1886_ = v___y_1937_;
v___y_1887_ = v___y_1938_;
v___y_1888_ = v___y_1939_;
v___y_1889_ = v___y_1940_;
v___y_1890_ = v___y_1941_;
v___y_1891_ = v___y_1945_;
v___y_1892_ = v___y_1942_;
v___y_1893_ = v___y_1943_;
v___y_1894_ = v___x_1954_;
goto v___jp_1876_;
}
}
}
v___jp_1955_:
{
uint8_t v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = 0;
lean_inc(v___y_1956_);
v___x_1972_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1956_, v___x_1971_, v___y_1966_, v___y_1958_, v___y_1964_);
if (lean_obj_tag(v___x_1972_) == 0)
{
if (lean_obj_tag(v___y_1962_) == 1)
{
lean_object* v_a_1973_; lean_object* v_val_1974_; lean_object* v___x_1975_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v_val_1974_ = lean_ctor_get(v___y_1962_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v___y_1962_, 1);
v___x_1975_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1974_);
lean_dec(v_val_1974_);
lean_inc(v___y_1961_);
v___y_1928_ = v___y_1961_;
v___y_1929_ = v___y_1957_;
v___y_1930_ = v___y_1956_;
v___y_1931_ = v___y_1958_;
v___y_1932_ = v___y_1965_;
v___y_1933_ = v___y_1959_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1967_;
v___y_1936_ = v___y_1970_;
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___x_1971_;
v___y_1940_ = v___y_1969_;
v___y_1941_ = v___y_1961_;
v___y_1942_ = v___y_1963_;
v___y_1943_ = v___y_1968_;
v___y_1944_ = v_a_1973_;
v___y_1945_ = v___x_1975_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
lean_dec(v___y_1962_);
v_a_1976_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1972_, 1);
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1961_);
v___y_1928_ = v___y_1961_;
v___y_1929_ = v___y_1957_;
v___y_1930_ = v___y_1956_;
v___y_1931_ = v___y_1958_;
v___y_1932_ = v___y_1965_;
v___y_1933_ = v___y_1959_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1967_;
v___y_1936_ = v___y_1970_;
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___x_1971_;
v___y_1940_ = v___y_1969_;
v___y_1941_ = v___y_1961_;
v___y_1942_ = v___y_1963_;
v___y_1943_ = v___y_1968_;
v___y_1944_ = v_a_1976_;
v___y_1945_ = v___x_1977_;
goto v___jp_1927_;
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v___y_1956_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v_a_1978_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1972_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1972_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
v___jp_1986_:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Syntax_getOptional_x3f(v___y_1994_);
lean_dec(v___y_1994_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_box(0);
v___y_1956_ = v___y_1988_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1991_;
v___y_1960_ = v___y_1995_;
v___y_1961_ = v___y_2001_;
v___y_1962_ = v___y_2000_;
v___y_1963_ = v___y_1998_;
v___y_1964_ = v___y_1992_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___y_1996_;
v___y_1967_ = v___y_1993_;
v___y_1968_ = v___y_1999_;
v___y_1969_ = v___y_1997_;
v___y_1970_ = v___x_2003_;
goto v___jp_1955_;
}
else
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2002_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v___x_2002_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
v___y_1956_ = v___y_1988_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1991_;
v___y_1960_ = v___y_1995_;
v___y_1961_ = v___y_2001_;
v___y_1962_ = v___y_2000_;
v___y_1963_ = v___y_1998_;
v___y_1964_ = v___y_1992_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___y_1996_;
v___y_1967_ = v___y_1993_;
v___y_1968_ = v___y_1999_;
v___y_1969_ = v___y_1997_;
v___y_1970_ = v___x_2009_;
goto v___jp_1955_;
}
}
}
}
v___jp_2012_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_unsigned_to_nat(4u);
v___x_2029_ = l_Lean_Syntax_getArg(v___y_2014_, v___x_2028_);
lean_dec(v___y_2014_);
v___x_2030_ = l_Lean_Syntax_getOptional_x3f(v___x_2029_);
lean_dec(v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_box(0);
v___y_1987_ = v___y_2025_;
v___y_1988_ = v___y_2013_;
v___y_1989_ = v___y_2026_;
v___y_1990_ = v___y_2022_;
v___y_1991_ = v___y_2023_;
v___y_1992_ = v___y_2027_;
v___y_1993_ = v___y_2021_;
v___y_1994_ = v___y_2017_;
v___y_1995_ = v___y_2018_;
v___y_1996_ = v___y_2020_;
v___y_1997_ = v___y_2015_;
v___y_1998_ = v___y_2024_;
v___y_1999_ = v___y_2016_;
v___y_2000_ = v_args_2019_;
v___y_2001_ = v___x_2031_;
goto v___jp_1986_;
}
else
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_val_2032_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2030_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v___x_2030_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_val_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v___y_1987_ = v___y_2025_;
v___y_1988_ = v___y_2013_;
v___y_1989_ = v___y_2026_;
v___y_1990_ = v___y_2022_;
v___y_1991_ = v___y_2023_;
v___y_1992_ = v___y_2027_;
v___y_1993_ = v___y_2021_;
v___y_1994_ = v___y_2017_;
v___y_1995_ = v___y_2018_;
v___y_1996_ = v___y_2020_;
v___y_1997_ = v___y_2015_;
v___y_1998_ = v___y_2024_;
v___y_1999_ = v___y_2016_;
v___y_2000_ = v_args_2019_;
v___y_2001_ = v___x_2037_;
goto v___jp_1986_;
}
}
}
}
v___jp_2041_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2056_ = lean_unsigned_to_nat(3u);
v___x_2057_ = l_Lean_Syntax_getArg(v___y_2043_, v___x_2056_);
v___x_2058_ = l_Lean_Syntax_isNone(v___x_2057_);
if (v___x_2058_ == 0)
{
uint8_t v___x_2059_; 
lean_inc(v___x_2057_);
v___x_2059_ = l_Lean_Syntax_matchesNull(v___x_2057_, v___x_2040_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec(v___x_2057_);
lean_dec(v_o_2047_);
lean_dec(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_2060_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2060_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2061_ = l_Lean_Syntax_getArg(v___x_2057_, v___x_1241_);
lean_dec(v___x_2057_);
v___x_2062_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1229_);
lean_inc_ref(v___x_1228_);
lean_inc_ref(v___x_1227_);
v___x_2063_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_2062_);
lean_inc(v___x_2061_);
v___x_2064_ = l_Lean_Syntax_isOfKind(v___x_2061_, v___x_2063_);
lean_dec(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec(v___x_2061_);
lean_dec(v_o_2047_);
lean_dec(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_2065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2065_;
}
else
{
lean_object* v___x_2066_; lean_object* v_args_2067_; lean_object* v___x_2068_; 
v___x_2066_ = l_Lean_Syntax_getArg(v___x_2061_, v___x_2040_);
lean_dec(v___x_2061_);
v_args_2067_ = l_Lean_Syntax_getArgs(v___x_2066_);
lean_dec(v___x_2066_);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_args_2067_);
v___y_2013_ = v___y_2042_;
v___y_2014_ = v___y_2043_;
v___y_2015_ = v___y_2044_;
v___y_2016_ = v_o_2047_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v___y_2046_;
v_args_2019_ = v___x_2068_;
v___y_2020_ = v___y_2048_;
v___y_2021_ = v___y_2049_;
v___y_2022_ = v___y_2050_;
v___y_2023_ = v___y_2051_;
v___y_2024_ = v___y_2052_;
v___y_2025_ = v___y_2053_;
v___y_2026_ = v___y_2054_;
v___y_2027_ = v___y_2055_;
goto v___jp_2012_;
}
}
}
else
{
lean_object* v___x_2069_; 
lean_dec(v___x_2057_);
v___x_2069_ = lean_box(0);
v___y_2013_ = v___y_2042_;
v___y_2014_ = v___y_2043_;
v___y_2015_ = v___y_2044_;
v___y_2016_ = v_o_2047_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v___y_2046_;
v_args_2019_ = v___x_2069_;
v___y_2020_ = v___y_2048_;
v___y_2021_ = v___y_2049_;
v___y_2022_ = v___y_2050_;
v___y_2023_ = v___y_2051_;
v___y_2024_ = v___y_2052_;
v___y_2025_ = v___y_2053_;
v___y_2026_ = v___y_2054_;
v___y_2027_ = v___y_2055_;
goto v___jp_2012_;
}
}
v___jp_2070_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2080_ = lean_unsigned_to_nat(2u);
v___x_2081_ = l_Lean_Syntax_getArg(v_stx_1225_, v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1229_);
lean_inc_ref(v___x_1228_);
lean_inc_ref(v___x_1227_);
v___x_2083_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_2082_);
lean_inc(v___x_2081_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v___x_2081_, v___x_2083_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v___x_2081_);
lean_dec(v_bang_2071_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_2085_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2085_;
}
else
{
lean_object* v_cfg_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_cfg_2086_ = l_Lean_Syntax_getArg(v___x_2081_, v___x_1241_);
v___x_2087_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1229_);
lean_inc_ref(v___x_1228_);
lean_inc_ref(v___x_1227_);
v___x_2088_ = l_Lean_Name_mkStr4(v___x_1227_, v___x_1228_, v___x_1229_, v___x_2087_);
lean_inc(v_cfg_2086_);
v___x_2089_ = l_Lean_Syntax_isOfKind(v_cfg_2086_, v___x_2088_);
lean_dec(v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v_cfg_2086_);
lean_dec(v___x_2081_);
lean_dec(v_bang_2071_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2091_ = l_Lean_Syntax_getArg(v___x_2081_, v___x_2040_);
v___x_2092_ = l_Lean_Syntax_getArg(v___x_2081_, v___x_2080_);
v___x_2093_ = l_Lean_Syntax_isNone(v___x_2092_);
if (v___x_2093_ == 0)
{
uint8_t v___x_2094_; 
lean_inc(v___x_2092_);
v___x_2094_ = l_Lean_Syntax_matchesNull(v___x_2092_, v___x_2040_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
lean_dec(v___x_2092_);
lean_dec(v___x_2091_);
lean_dec(v_cfg_2086_);
lean_dec(v___x_2081_);
lean_dec(v_bang_2071_);
lean_dec(v_tk_1242_);
lean_dec_ref(v___f_1230_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_2095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2095_;
}
else
{
lean_object* v_o_2096_; lean_object* v___x_2097_; 
v_o_2096_ = l_Lean_Syntax_getArg(v___x_2092_, v___x_1241_);
lean_dec(v___x_2092_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_o_2096_);
v___y_2042_ = v_cfg_2086_;
v___y_2043_ = v___x_2081_;
v___y_2044_ = v_bang_2071_;
v___y_2045_ = v___x_2091_;
v___y_2046_ = v___x_2084_;
v_o_2047_ = v___x_2097_;
v___y_2048_ = v___y_2072_;
v___y_2049_ = v___y_2073_;
v___y_2050_ = v___y_2074_;
v___y_2051_ = v___y_2075_;
v___y_2052_ = v___y_2076_;
v___y_2053_ = v___y_2077_;
v___y_2054_ = v___y_2078_;
v___y_2055_ = v___y_2079_;
goto v___jp_2041_;
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v___x_2092_);
v___x_2098_ = lean_box(0);
v___y_2042_ = v_cfg_2086_;
v___y_2043_ = v___x_2081_;
v___y_2044_ = v_bang_2071_;
v___y_2045_ = v___x_2091_;
v___y_2046_ = v___x_2084_;
v_o_2047_ = v___x_2098_;
v___y_2048_ = v___y_2072_;
v___y_2049_ = v___y_2073_;
v___y_2050_ = v___y_2074_;
v___y_2051_ = v___y_2075_;
v___y_2052_ = v___y_2076_;
v___y_2053_ = v___y_2077_;
v___y_2054_ = v___y_2078_;
v___y_2055_ = v___y_2079_;
goto v___jp_2041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2106_, lean_object* v_stx_2107_, lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v___x_2110_, lean_object* v___x_2111_, lean_object* v___f_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v___x_35450__boxed_2122_; uint8_t v___x_35451__boxed_2123_; lean_object* v_res_2124_; 
v___x_35450__boxed_2122_ = lean_unbox(v___x_2106_);
v___x_35451__boxed_2123_ = lean_unbox(v___x_2108_);
v_res_2124_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35450__boxed_2122_, v_stx_2107_, v___x_35451__boxed_2123_, v___x_2109_, v___x_2110_, v___x_2111_, v___f_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v_stx_2107_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; uint8_t v___x_2149_; lean_object* v___f_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___y_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2134_);
v___x_2148_ = l_Lean_Syntax_isOfKind(v_stx_2134_, v___x_2147_);
v___x_2149_ = 1;
v___f_2150_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2151_ = lean_box(v___x_2148_);
v___x_2152_ = lean_box(v___x_2149_);
v___y_2153_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2153_, 0, v___x_2151_);
lean_closure_set(v___y_2153_, 1, v_stx_2134_);
lean_closure_set(v___y_2153_, 2, v___x_2152_);
lean_closure_set(v___y_2153_, 3, v___x_2144_);
lean_closure_set(v___y_2153_, 4, v___x_2145_);
lean_closure_set(v___y_2153_, 5, v___x_2146_);
lean_closure_set(v___y_2153_, 6, v___f_2150_);
v___x_2154_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2154_, 0, v___y_2153_);
v___x_2155_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2154_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2167_, lean_object* v_as_2168_, lean_object* v_as_x27_2169_, lean_object* v_b_2170_, lean_object* v_a_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2167_, v_as_x27_2169_, v_b_2170_, v___y_2178_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2182_, lean_object* v_as_2183_, lean_object* v_as_x27_2184_, lean_object* v_b_2185_, lean_object* v_a_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2182_, v_as_2183_, v_as_x27_2184_, v_b_2185_, v_a_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v_as_x27_2184_);
lean_dec(v_as_2183_);
lean_dec(v___x_2182_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2197_, lean_object* v_ref_2198_, lean_object* v_msg_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2198_, v_msg_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2210_, lean_object* v_ref_2211_, lean_object* v_msg_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2210_, v_ref_2211_, v_msg_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v_ref_2211_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2223_, lean_object* v_ref_2224_, lean_object* v_constName_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2224_, v_constName_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_ref_2237_, lean_object* v_constName_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2236_, v_ref_2237_, v_constName_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v_ref_2237_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2249_, lean_object* v_msg_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2250_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_msg_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2261_, v_msg_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2273_, v___y_2280_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec_ref(v_opt_2284_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2295_, lean_object* v_ref_2296_, lean_object* v_msg_2297_, lean_object* v_declHint_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2296_, v_msg_2297_, v_declHint_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_ref_2310_, lean_object* v_msg_2311_, lean_object* v_declHint_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2309_, v_ref_2310_, v_msg_2311_, v_declHint_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_ref_2310_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2323_, lean_object* v_declHint_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2323_, v_declHint_2324_, v___y_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2335_, lean_object* v_declHint_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2335_, v_declHint_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2347_, lean_object* v_msgData_2348_, uint8_t v_severity_2349_, uint8_t v_isSilent_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2347_, v_msgData_2348_, v_severity_2349_, v_isSilent_2350_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2361_, lean_object* v_msgData_2362_, lean_object* v_severity_2363_, lean_object* v_isSilent_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_severity_boxed_2374_; uint8_t v_isSilent_boxed_2375_; lean_object* v_res_2376_; 
v_severity_boxed_2374_ = lean_unbox(v_severity_2363_);
v_isSilent_boxed_2375_ = lean_unbox(v_isSilent_2364_);
v_res_2376_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2361_, v_msgData_2362_, v_severity_boxed_2374_, v_isSilent_boxed_2375_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v_ref_2361_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2384_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2385_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2387_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2388_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2384_, v___x_2385_, v___x_2386_, v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2419_ = l_Lean_addBuiltinDeclarationRanges(v___x_2417_, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2422_, lean_object* v_as_x27_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_){
_start:
{
if (lean_obj_tag(v_as_x27_2423_) == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_b_2424_);
return v___x_2427_;
}
else
{
lean_object* v_head_2428_; lean_object* v_tail_2429_; lean_object* v_ref_2430_; uint8_t v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_head_2428_ = lean_ctor_get(v_as_x27_2423_, 0);
v_tail_2429_ = lean_ctor_get(v_as_x27_2423_, 1);
v_ref_2430_ = lean_ctor_get(v___y_2425_, 2);
v___x_2431_ = 1;
v___x_2432_ = 0;
v___x_2433_ = l_Lean_SourceInfo_fromRef(v_ref_2430_, v___x_2432_);
v___x_2434_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2435_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2436_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2433_);
v___x_2437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2433_);
lean_ctor_set(v___x_2437_, 1, v___x_2435_);
lean_ctor_set(v___x_2437_, 2, v___x_2436_);
lean_inc(v_head_2428_);
v___x_2438_ = l_Lean_mkCIdentFrom(v___x_2422_, v_head_2428_, v___x_2431_);
lean_inc_ref(v___x_2437_);
v___x_2439_ = l_Lean_Syntax_node3(v___x_2433_, v___x_2434_, v___x_2437_, v___x_2437_, v___x_2438_);
v___x_2440_ = lean_array_push(v_b_2424_, v___x_2439_);
v_as_x27_2423_ = v_tail_2429_;
v_b_2424_ = v___x_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2442_, lean_object* v_as_x27_2443_, lean_object* v_b_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2442_, v_as_x27_2443_, v_b_2444_, v___y_2445_);
lean_dec_ref(v___y_2445_);
lean_dec(v_as_x27_2443_);
lean_dec(v___x_2442_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2448_, size_t v_sz_2449_, size_t v_i_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_lt(v_i_2450_, v_sz_2449_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_b_2451_);
return v___x_2462_;
}
else
{
lean_object* v_a_2463_; lean_object* v_name_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_a_2463_ = lean_array_uget_borrowed(v_as_2448_, v_i_2450_);
v_name_2464_ = lean_ctor_get(v_a_2463_, 0);
lean_inc(v_name_2464_);
v___x_2465_ = l_Lean_mkIdent(v_name_2464_);
lean_inc(v___x_2465_);
v___x_2466_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2465_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2465_, v_a_2467_, v_b_2451_, v___y_2458_);
lean_dec(v_a_2467_);
lean_dec(v___x_2465_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; size_t v___x_2470_; size_t v___x_2471_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2450_, v___x_2470_);
v_i_2450_ = v___x_2471_;
v_b_2451_ = v_a_2469_;
goto _start;
}
else
{
return v___x_2468_;
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v___x_2465_);
lean_dec_ref(v_b_2451_);
v_a_2473_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2466_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2466_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2481_, lean_object* v_sz_2482_, lean_object* v_i_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
size_t v_sz_boxed_2494_; size_t v_i_boxed_2495_; lean_object* v_res_2496_; 
v_sz_boxed_2494_ = lean_unbox_usize(v_sz_2482_);
lean_dec(v_sz_2482_);
v_i_boxed_2495_ = lean_unbox_usize(v_i_2483_);
lean_dec(v_i_2483_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2481_, v_sz_boxed_2494_, v_i_boxed_2495_, v_b_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_as_2481_);
return v_res_2496_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_unsigned_to_nat(0u);
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2499_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_unsigned_to_nat(32u);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2505_ = ((size_t)5ULL);
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2507_ = lean_unsigned_to_nat(32u);
v___x_2508_ = lean_mk_empty_array_with_capacity(v___x_2507_);
v___x_2509_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2510_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2508_);
lean_ctor_set(v___x_2510_, 2, v___x_2506_);
lean_ctor_set(v___x_2510_, 3, v___x_2506_);
lean_ctor_set_usize(v___x_2510_, 4, v___x_2505_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2512_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
lean_ctor_set(v___x_2513_, 3, v___x_2511_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2515_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___x_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2525_, lean_object* v_stx_2526_, uint8_t v___x_2527_, lean_object* v___x_2528_, lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v___f_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
if (v___x_2525_ == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_2541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v_tk_2543_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2658_; uint8_t v___y_2659_; lean_object* v___y_2660_; uint8_t v___y_2661_; lean_object* v_stxForSuggestion_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2690_; uint8_t v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; uint8_t v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2724_; lean_object* v___y_2725_; uint8_t v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; uint8_t v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; uint8_t v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; uint8_t v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; uint8_t v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2843_; uint8_t v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; uint8_t v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2872_; uint8_t v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; uint8_t v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; uint8_t v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; uint8_t v___y_2959_; uint8_t v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_stxForExecution_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; uint8_t v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; uint8_t v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint8_t v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; uint8_t v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; uint8_t v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; uint8_t v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; uint8_t v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; uint8_t v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; uint8_t v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; uint8_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; uint8_t v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; uint8_t v___y_3274_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; uint8_t v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v_argsArray_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; uint8_t v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; uint8_t v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; uint8_t v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; uint8_t v___y_3453_; lean_object* v_args_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___x_3473_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3479_; lean_object* v_o_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_bang_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v_tk_2543_ = l_Lean_Syntax_getArg(v_stx_2526_, v___x_2542_);
v___x_3473_ = lean_unsigned_to_nat(1u);
v___x_3532_ = l_Lean_Syntax_getArg(v_stx_2526_, v___x_3473_);
v___x_3533_ = l_Lean_Syntax_isNone(v___x_3532_);
if (v___x_3533_ == 0)
{
uint8_t v___x_3534_; 
lean_inc(v___x_3532_);
v___x_3534_ = l_Lean_Syntax_matchesNull(v___x_3532_, v___x_3473_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; 
lean_dec(v___x_3532_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_3535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3535_;
}
else
{
lean_object* v_bang_3536_; lean_object* v___x_3537_; 
v_bang_3536_ = l_Lean_Syntax_getArg(v___x_3532_, v___x_2542_);
lean_dec(v___x_3532_);
v___x_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3537_, 0, v_bang_3536_);
v_bang_3504_ = v___x_3537_;
v___y_3505_ = v___y_2532_;
v___y_3506_ = v___y_2533_;
v___y_3507_ = v___y_2534_;
v___y_3508_ = v___y_2535_;
v___y_3509_ = v___y_2536_;
v___y_3510_ = v___y_2537_;
v___y_3511_ = v___y_2538_;
v___y_3512_ = v___y_2539_;
goto v___jp_3503_;
}
}
else
{
lean_object* v___x_3538_; 
lean_dec(v___x_3532_);
v___x_3538_ = lean_box(0);
v_bang_3504_ = v___x_3538_;
v___y_3505_ = v___y_2532_;
v___y_3506_ = v___y_2533_;
v___y_3507_ = v___y_2534_;
v___y_3508_ = v___y_2535_;
v___y_3509_ = v___y_2536_;
v___y_3510_ = v___y_2537_;
v___y_3511_ = v___y_2538_;
v___y_3512_ = v___y_2539_;
goto v___jp_3503_;
}
v___jp_2544_:
{
lean_object* v_usedTheorems_2551_; lean_object* v_diag_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2594_; 
v_usedTheorems_2551_ = lean_ctor_get(v___y_2545_, 0);
v_diag_2552_ = lean_ctor_get(v___y_2545_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___y_2545_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2554_ = v___y_2545_;
v_isShared_2555_ = v_isSharedCheck_2594_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_diag_2552_);
lean_inc(v_usedTheorems_2551_);
lean_dec(v___y_2545_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2594_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2546_, v_usedTheorems_2551_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v_usedTheorems_2551_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v_ref_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v_ref_2558_ = lean_ctor_get(v___y_2549_, 2);
v___x_2559_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 1, v_a_2557_);
lean_ctor_set(v___x_2554_, 0, v___x_2559_);
v___x_2561_ = v___x_2554_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_a_2557_);
v___x_2561_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
lean_ctor_set(v___x_2563_, 2, v___x_2562_);
lean_ctor_set(v___x_2563_, 3, v___x_2562_);
lean_ctor_set(v___x_2563_, 4, v___x_2562_);
lean_ctor_set(v___x_2563_, 5, v___x_2562_);
lean_inc(v_ref_2558_);
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_ref_2558_);
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2566_ = 4;
v___x_2567_ = l_Lean_MessageData_nil;
v___x_2568_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2543_, v___x_2563_, v___x_2564_, v___x_2565_, v___x_2562_, v___x_2566_, v___x_2567_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2568_, 0);
lean_dec(v_unused_2576_);
v___x_2570_ = v___x_2568_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___x_2568_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v_diag_2552_);
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_diag_2552_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_diag_2552_);
v_a_2577_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2568_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2568_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_del_object(v___x_2554_);
lean_dec_ref(v_diag_2552_);
lean_dec(v_tk_2543_);
v_a_2586_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2556_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2556_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
v___jp_2595_:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2596_, v___y_2601_, v___y_2602_, v___y_2597_, v___y_2599_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2607_ = l_Lean_Meta_simpAll(v_a_2605_, v___y_2603_, v___y_2598_, v___x_2606_, v___y_2601_, v___y_2602_, v___y_2597_, v___y_2599_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v_fst_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v_fst_2609_ = lean_ctor_get(v_a_2608_, 0);
if (lean_obj_tag(v_fst_2609_) == 0)
{
lean_object* v_snd_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_snd_2610_ = lean_ctor_get(v_a_2608_, 1);
lean_inc(v_snd_2610_);
lean_dec(v_a_2608_);
v___x_2611_ = lean_box(0);
v___x_2612_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2611_, v___y_2596_, v___y_2601_, v___y_2602_, v___y_2597_, v___y_2599_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref_known(v___x_2612_, 1);
v___y_2545_ = v_snd_2610_;
v___y_2546_ = v___y_2600_;
v___y_2547_ = v___y_2601_;
v___y_2548_ = v___y_2602_;
v___y_2549_ = v___y_2597_;
v___y_2550_ = v___y_2599_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_snd_2610_);
lean_dec(v___y_2600_);
lean_dec(v_tk_2543_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_snd_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2639_; 
lean_inc_ref(v_fst_2609_);
v_snd_2621_ = lean_ctor_get(v_a_2608_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_a_2608_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; 
v_unused_2640_ = lean_ctor_get(v_a_2608_, 0);
lean_dec(v_unused_2640_);
v___x_2623_ = v_a_2608_;
v_isShared_2624_ = v_isSharedCheck_2639_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_snd_2621_);
lean_dec(v_a_2608_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2639_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_val_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v_val_2625_ = lean_ctor_get(v_fst_2609_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v_fst_2609_, 1);
v___x_2626_ = lean_box(0);
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 1);
lean_ctor_set(v___x_2623_, 1, v___x_2626_);
lean_ctor_set(v___x_2623_, 0, v_val_2625_);
v___x_2628_ = v___x_2623_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_val_2625_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2628_, v___y_2596_, v___y_2601_, v___y_2602_, v___y_2597_, v___y_2599_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_dec_ref_known(v___x_2629_, 1);
v___y_2545_ = v_snd_2621_;
v___y_2546_ = v___y_2600_;
v___y_2547_ = v___y_2601_;
v___y_2548_ = v___y_2602_;
v___y_2549_ = v___y_2597_;
v___y_2550_ = v___y_2599_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_snd_2621_);
lean_dec(v___y_2600_);
lean_dec(v_tk_2543_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v___y_2600_);
lean_dec(v_tk_2543_);
v_a_2641_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2607_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2607_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2598_);
lean_dec(v_tk_2543_);
v_a_2649_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2604_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2604_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
v___jp_2657_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2672_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2660_, v___x_2527_, v___y_2659_, v___x_2527_, v___x_2671_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2660_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
if (lean_obj_tag(v___y_2658_) == 0)
{
lean_object* v_ctx_2674_; lean_object* v_simprocs_2675_; 
v_ctx_2674_ = lean_ctor_get(v_a_2673_, 0);
lean_inc_ref(v_ctx_2674_);
v_simprocs_2675_ = lean_ctor_get(v_a_2673_, 1);
lean_inc_ref(v_simprocs_2675_);
lean_dec(v_a_2673_);
v___y_2596_ = v___y_2664_;
v___y_2597_ = v___y_2669_;
v___y_2598_ = v_simprocs_2675_;
v___y_2599_ = v___y_2670_;
v___y_2600_ = v_stxForSuggestion_2662_;
v___y_2601_ = v___y_2667_;
v___y_2602_ = v___y_2668_;
v___y_2603_ = v_ctx_2674_;
goto v___jp_2595_;
}
else
{
lean_dec_ref_known(v___y_2658_, 1);
if (v___y_2661_ == 0)
{
lean_object* v_ctx_2676_; lean_object* v_simprocs_2677_; 
v_ctx_2676_ = lean_ctor_get(v_a_2673_, 0);
lean_inc_ref(v_ctx_2676_);
v_simprocs_2677_ = lean_ctor_get(v_a_2673_, 1);
lean_inc_ref(v_simprocs_2677_);
lean_dec(v_a_2673_);
v___y_2596_ = v___y_2664_;
v___y_2597_ = v___y_2669_;
v___y_2598_ = v_simprocs_2677_;
v___y_2599_ = v___y_2670_;
v___y_2600_ = v_stxForSuggestion_2662_;
v___y_2601_ = v___y_2667_;
v___y_2602_ = v___y_2668_;
v___y_2603_ = v_ctx_2676_;
goto v___jp_2595_;
}
else
{
lean_object* v_ctx_2678_; lean_object* v_simprocs_2679_; lean_object* v___x_2680_; 
v_ctx_2678_ = lean_ctor_get(v_a_2673_, 0);
lean_inc_ref(v_ctx_2678_);
v_simprocs_2679_ = lean_ctor_get(v_a_2673_, 1);
lean_inc_ref(v_simprocs_2679_);
lean_dec(v_a_2673_);
v___x_2680_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2678_);
v___y_2596_ = v___y_2664_;
v___y_2597_ = v___y_2669_;
v___y_2598_ = v_simprocs_2679_;
v___y_2599_ = v___y_2670_;
v___y_2600_ = v_stxForSuggestion_2662_;
v___y_2601_ = v___y_2667_;
v___y_2602_ = v___y_2668_;
v___y_2603_ = v___x_2680_;
goto v___jp_2595_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_stxForSuggestion_2662_);
lean_dec(v___y_2658_);
lean_dec(v_tk_2543_);
v_a_2681_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2672_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2672_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
v___jp_2689_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_inc_ref_n(v___y_2699_, 2);
v___x_2711_ = l_Array_append___redArg(v___y_2699_, v___y_2710_);
lean_dec_ref(v___y_2710_);
lean_inc_n(v___y_2690_, 3);
lean_inc_n(v___y_2707_, 5);
v___x_2712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2712_, 0, v___y_2707_);
lean_ctor_set(v___x_2712_, 1, v___y_2690_);
lean_ctor_set(v___x_2712_, 2, v___x_2711_);
v___x_2713_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___y_2707_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2716_ = l_Lean_Syntax_SepArray_ofElems(v___x_2715_, v___y_2709_);
lean_dec_ref(v___y_2709_);
v___x_2717_ = l_Array_append___redArg(v___y_2699_, v___x_2716_);
lean_dec_ref(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___y_2707_);
lean_ctor_set(v___x_2718_, 1, v___y_2690_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
v___x_2719_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___y_2707_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_Syntax_node3(v___y_2707_, v___y_2690_, v___x_2714_, v___x_2718_, v___x_2720_);
v___x_2722_ = l_Lean_Syntax_node5(v___y_2707_, v___y_2693_, v___y_2696_, v___y_2698_, v___y_2694_, v___x_2712_, v___x_2721_);
v___y_2658_ = v___y_2702_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2708_;
v___y_2661_ = v___y_2697_;
v_stxForSuggestion_2662_ = v___x_2722_;
v___y_2663_ = v___y_2705_;
v___y_2664_ = v___y_2701_;
v___y_2665_ = v___y_2695_;
v___y_2666_ = v___y_2700_;
v___y_2667_ = v___y_2706_;
v___y_2668_ = v___y_2704_;
v___y_2669_ = v___y_2692_;
v___y_2670_ = v___y_2703_;
goto v___jp_2657_;
}
v___jp_2723_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_inc_ref(v___y_2733_);
v___x_2745_ = l_Array_append___redArg(v___y_2733_, v___y_2744_);
lean_dec_ref(v___y_2744_);
lean_inc(v___y_2724_);
lean_inc(v___y_2741_);
v___x_2746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2746_, 0, v___y_2741_);
lean_ctor_set(v___x_2746_, 1, v___y_2724_);
lean_ctor_set(v___x_2746_, 2, v___x_2745_);
if (lean_obj_tag(v___y_2725_) == 1)
{
lean_object* v_val_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_val_2747_ = lean_ctor_get(v___y_2725_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v___y_2725_, 1);
v___x_2748_ = l_Lean_SourceInfo_fromRef(v_val_2747_, v___x_2527_);
lean_dec(v_val_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Array_mkArray1___redArg(v___x_2750_);
v___y_2690_ = v___y_2724_;
v___y_2691_ = v___y_2726_;
v___y_2692_ = v___y_2727_;
v___y_2693_ = v___y_2728_;
v___y_2694_ = v___x_2746_;
v___y_2695_ = v___y_2729_;
v___y_2696_ = v___y_2730_;
v___y_2697_ = v___y_2731_;
v___y_2698_ = v___y_2732_;
v___y_2699_ = v___y_2733_;
v___y_2700_ = v___y_2734_;
v___y_2701_ = v___y_2735_;
v___y_2702_ = v___y_2740_;
v___y_2703_ = v___y_2739_;
v___y_2704_ = v___y_2738_;
v___y_2705_ = v___y_2737_;
v___y_2706_ = v___y_2736_;
v___y_2707_ = v___y_2741_;
v___y_2708_ = v___y_2742_;
v___y_2709_ = v___y_2743_;
v___y_2710_ = v___x_2751_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2752_; 
lean_dec(v___y_2725_);
v___x_2752_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2690_ = v___y_2724_;
v___y_2691_ = v___y_2726_;
v___y_2692_ = v___y_2727_;
v___y_2693_ = v___y_2728_;
v___y_2694_ = v___x_2746_;
v___y_2695_ = v___y_2729_;
v___y_2696_ = v___y_2730_;
v___y_2697_ = v___y_2731_;
v___y_2698_ = v___y_2732_;
v___y_2699_ = v___y_2733_;
v___y_2700_ = v___y_2734_;
v___y_2701_ = v___y_2735_;
v___y_2702_ = v___y_2740_;
v___y_2703_ = v___y_2739_;
v___y_2704_ = v___y_2738_;
v___y_2705_ = v___y_2737_;
v___y_2706_ = v___y_2736_;
v___y_2707_ = v___y_2741_;
v___y_2708_ = v___y_2742_;
v___y_2709_ = v___y_2743_;
v___y_2710_ = v___x_2752_;
goto v___jp_2689_;
}
}
v___jp_2753_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_inc_ref_n(v___y_2758_, 2);
v___x_2775_ = l_Array_append___redArg(v___y_2758_, v___y_2774_);
lean_dec_ref(v___y_2774_);
lean_inc_n(v___y_2755_, 3);
lean_inc_n(v___y_2754_, 5);
v___x_2776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2776_, 0, v___y_2754_);
lean_ctor_set(v___x_2776_, 1, v___y_2755_);
lean_ctor_set(v___x_2776_, 2, v___x_2775_);
v___x_2777_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___y_2754_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2780_ = l_Lean_Syntax_SepArray_ofElems(v___x_2779_, v___y_2772_);
lean_dec_ref(v___y_2772_);
v___x_2781_ = l_Array_append___redArg(v___y_2758_, v___x_2780_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2782_, 0, v___y_2754_);
lean_ctor_set(v___x_2782_, 1, v___y_2755_);
lean_ctor_set(v___x_2782_, 2, v___x_2781_);
v___x_2783_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___y_2754_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = l_Lean_Syntax_node3(v___y_2754_, v___y_2755_, v___x_2778_, v___x_2782_, v___x_2784_);
v___x_2786_ = l_Lean_Syntax_node5(v___y_2754_, v___y_2765_, v___y_2759_, v___y_2762_, v___y_2773_, v___x_2776_, v___x_2785_);
v___y_2658_ = v___y_2766_;
v___y_2659_ = v___y_2756_;
v___y_2660_ = v___y_2771_;
v___y_2661_ = v___y_2761_;
v_stxForSuggestion_2662_ = v___x_2786_;
v___y_2663_ = v___y_2769_;
v___y_2664_ = v___y_2764_;
v___y_2665_ = v___y_2760_;
v___y_2666_ = v___y_2763_;
v___y_2667_ = v___y_2770_;
v___y_2668_ = v___y_2768_;
v___y_2669_ = v___y_2757_;
v___y_2670_ = v___y_2767_;
goto v___jp_2657_;
}
v___jp_2787_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_inc_ref(v___y_2793_);
v___x_2809_ = l_Array_append___redArg(v___y_2793_, v___y_2808_);
lean_dec_ref(v___y_2808_);
lean_inc(v___y_2790_);
lean_inc(v___y_2788_);
v___x_2810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2810_, 0, v___y_2788_);
lean_ctor_set(v___x_2810_, 1, v___y_2790_);
lean_ctor_set(v___x_2810_, 2, v___x_2809_);
if (lean_obj_tag(v___y_2789_) == 1)
{
lean_object* v_val_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_val_2811_ = lean_ctor_get(v___y_2789_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v___y_2789_, 1);
v___x_2812_ = l_Lean_SourceInfo_fromRef(v_val_2811_, v___x_2527_);
lean_dec(v_val_2811_);
v___x_2813_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = l_Array_mkArray1___redArg(v___x_2814_);
v___y_2754_ = v___y_2788_;
v___y_2755_ = v___y_2790_;
v___y_2756_ = v___y_2791_;
v___y_2757_ = v___y_2792_;
v___y_2758_ = v___y_2793_;
v___y_2759_ = v___y_2794_;
v___y_2760_ = v___y_2795_;
v___y_2761_ = v___y_2796_;
v___y_2762_ = v___y_2797_;
v___y_2763_ = v___y_2798_;
v___y_2764_ = v___y_2799_;
v___y_2765_ = v___y_2800_;
v___y_2766_ = v___y_2805_;
v___y_2767_ = v___y_2804_;
v___y_2768_ = v___y_2803_;
v___y_2769_ = v___y_2802_;
v___y_2770_ = v___y_2801_;
v___y_2771_ = v___y_2806_;
v___y_2772_ = v___y_2807_;
v___y_2773_ = v___x_2810_;
v___y_2774_ = v___x_2815_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2816_; 
lean_dec(v___y_2789_);
v___x_2816_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2754_ = v___y_2788_;
v___y_2755_ = v___y_2790_;
v___y_2756_ = v___y_2791_;
v___y_2757_ = v___y_2792_;
v___y_2758_ = v___y_2793_;
v___y_2759_ = v___y_2794_;
v___y_2760_ = v___y_2795_;
v___y_2761_ = v___y_2796_;
v___y_2762_ = v___y_2797_;
v___y_2763_ = v___y_2798_;
v___y_2764_ = v___y_2799_;
v___y_2765_ = v___y_2800_;
v___y_2766_ = v___y_2805_;
v___y_2767_ = v___y_2804_;
v___y_2768_ = v___y_2803_;
v___y_2769_ = v___y_2802_;
v___y_2770_ = v___y_2801_;
v___y_2771_ = v___y_2806_;
v___y_2772_ = v___y_2807_;
v___y_2773_ = v___x_2810_;
v___y_2774_ = v___x_2816_;
goto v___jp_2753_;
}
}
v___jp_2817_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_inc_ref_n(v___y_2826_, 2);
v___x_2838_ = l_Array_append___redArg(v___y_2826_, v___y_2837_);
lean_dec_ref(v___y_2837_);
lean_inc_n(v___y_2832_, 2);
lean_inc_n(v___y_2820_, 2);
v___x_2839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2839_, 0, v___y_2820_);
lean_ctor_set(v___x_2839_, 1, v___y_2832_);
lean_ctor_set(v___x_2839_, 2, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2840_, 0, v___y_2820_);
lean_ctor_set(v___x_2840_, 1, v___y_2832_);
lean_ctor_set(v___x_2840_, 2, v___y_2826_);
v___x_2841_ = l_Lean_Syntax_node5(v___y_2820_, v___y_2834_, v___y_2833_, v___y_2823_, v___y_2836_, v___x_2839_, v___x_2840_);
v___y_2658_ = v___y_2827_;
v___y_2659_ = v___y_2818_;
v___y_2660_ = v___y_2835_;
v___y_2661_ = v___y_2822_;
v_stxForSuggestion_2662_ = v___x_2841_;
v___y_2663_ = v___y_2829_;
v___y_2664_ = v___y_2825_;
v___y_2665_ = v___y_2821_;
v___y_2666_ = v___y_2824_;
v___y_2667_ = v___y_2830_;
v___y_2668_ = v___y_2831_;
v___y_2669_ = v___y_2819_;
v___y_2670_ = v___y_2828_;
goto v___jp_2657_;
}
v___jp_2842_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_inc_ref(v___y_2852_);
v___x_2863_ = l_Array_append___redArg(v___y_2852_, v___y_2862_);
lean_dec_ref(v___y_2862_);
lean_inc(v___y_2859_);
lean_inc(v___y_2846_);
v___x_2864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2864_, 0, v___y_2846_);
lean_ctor_set(v___x_2864_, 1, v___y_2859_);
lean_ctor_set(v___x_2864_, 2, v___x_2863_);
if (lean_obj_tag(v___y_2843_) == 1)
{
lean_object* v_val_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_val_2865_ = lean_ctor_get(v___y_2843_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v___y_2843_, 1);
v___x_2866_ = l_Lean_SourceInfo_fromRef(v_val_2865_, v___x_2527_);
lean_dec(v_val_2865_);
v___x_2867_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Array_mkArray1___redArg(v___x_2868_);
v___y_2818_ = v___y_2844_;
v___y_2819_ = v___y_2845_;
v___y_2820_ = v___y_2846_;
v___y_2821_ = v___y_2847_;
v___y_2822_ = v___y_2848_;
v___y_2823_ = v___y_2849_;
v___y_2824_ = v___y_2850_;
v___y_2825_ = v___y_2851_;
v___y_2826_ = v___y_2852_;
v___y_2827_ = v___y_2856_;
v___y_2828_ = v___y_2857_;
v___y_2829_ = v___y_2855_;
v___y_2830_ = v___y_2854_;
v___y_2831_ = v___y_2853_;
v___y_2832_ = v___y_2859_;
v___y_2833_ = v___y_2858_;
v___y_2834_ = v___y_2860_;
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___x_2864_;
v___y_2837_ = v___x_2869_;
goto v___jp_2817_;
}
else
{
lean_object* v___x_2870_; 
lean_dec(v___y_2843_);
v___x_2870_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2818_ = v___y_2844_;
v___y_2819_ = v___y_2845_;
v___y_2820_ = v___y_2846_;
v___y_2821_ = v___y_2847_;
v___y_2822_ = v___y_2848_;
v___y_2823_ = v___y_2849_;
v___y_2824_ = v___y_2850_;
v___y_2825_ = v___y_2851_;
v___y_2826_ = v___y_2852_;
v___y_2827_ = v___y_2856_;
v___y_2828_ = v___y_2857_;
v___y_2829_ = v___y_2855_;
v___y_2830_ = v___y_2854_;
v___y_2831_ = v___y_2853_;
v___y_2832_ = v___y_2859_;
v___y_2833_ = v___y_2858_;
v___y_2834_ = v___y_2860_;
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___x_2864_;
v___y_2837_ = v___x_2870_;
goto v___jp_2817_;
}
}
v___jp_2871_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_inc_ref_n(v___y_2887_, 2);
v___x_2892_ = l_Array_append___redArg(v___y_2887_, v___y_2891_);
lean_dec_ref(v___y_2891_);
lean_inc_n(v___y_2881_, 2);
lean_inc_n(v___y_2872_, 2);
v___x_2893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2893_, 0, v___y_2872_);
lean_ctor_set(v___x_2893_, 1, v___y_2881_);
lean_ctor_set(v___x_2893_, 2, v___x_2892_);
v___x_2894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2894_, 0, v___y_2872_);
lean_ctor_set(v___x_2894_, 1, v___y_2881_);
lean_ctor_set(v___x_2894_, 2, v___y_2887_);
v___x_2895_ = l_Lean_Syntax_node5(v___y_2872_, v___y_2889_, v___y_2877_, v___y_2878_, v___y_2890_, v___x_2893_, v___x_2894_);
v___y_2658_ = v___y_2882_;
v___y_2659_ = v___y_2873_;
v___y_2660_ = v___y_2888_;
v___y_2661_ = v___y_2876_;
v_stxForSuggestion_2662_ = v___x_2895_;
v___y_2663_ = v___y_2884_;
v___y_2664_ = v___y_2880_;
v___y_2665_ = v___y_2875_;
v___y_2666_ = v___y_2879_;
v___y_2667_ = v___y_2885_;
v___y_2668_ = v___y_2886_;
v___y_2669_ = v___y_2874_;
v___y_2670_ = v___y_2883_;
goto v___jp_2657_;
}
v___jp_2896_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_inc_ref(v___y_2913_);
v___x_2917_ = l_Array_append___redArg(v___y_2913_, v___y_2916_);
lean_dec_ref(v___y_2916_);
lean_inc(v___y_2907_);
lean_inc(v___y_2898_);
v___x_2918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2918_, 0, v___y_2898_);
lean_ctor_set(v___x_2918_, 1, v___y_2907_);
lean_ctor_set(v___x_2918_, 2, v___x_2917_);
if (lean_obj_tag(v___y_2897_) == 1)
{
lean_object* v_val_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_val_2919_ = lean_ctor_get(v___y_2897_, 0);
lean_inc(v_val_2919_);
lean_dec_ref_known(v___y_2897_, 1);
v___x_2920_ = l_Lean_SourceInfo_fromRef(v_val_2919_, v___x_2527_);
lean_dec(v_val_2919_);
v___x_2921_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = l_Array_mkArray1___redArg(v___x_2922_);
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___y_2899_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2901_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2903_;
v___y_2878_ = v___y_2904_;
v___y_2879_ = v___y_2905_;
v___y_2880_ = v___y_2906_;
v___y_2881_ = v___y_2907_;
v___y_2882_ = v___y_2912_;
v___y_2883_ = v___y_2911_;
v___y_2884_ = v___y_2910_;
v___y_2885_ = v___y_2909_;
v___y_2886_ = v___y_2908_;
v___y_2887_ = v___y_2913_;
v___y_2888_ = v___y_2914_;
v___y_2889_ = v___y_2915_;
v___y_2890_ = v___x_2918_;
v___y_2891_ = v___x_2923_;
goto v___jp_2871_;
}
else
{
lean_object* v___x_2924_; 
lean_dec(v___y_2897_);
v___x_2924_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___y_2899_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2901_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2903_;
v___y_2878_ = v___y_2904_;
v___y_2879_ = v___y_2905_;
v___y_2880_ = v___y_2906_;
v___y_2881_ = v___y_2907_;
v___y_2882_ = v___y_2912_;
v___y_2883_ = v___y_2911_;
v___y_2884_ = v___y_2910_;
v___y_2885_ = v___y_2909_;
v___y_2886_ = v___y_2908_;
v___y_2887_ = v___y_2913_;
v___y_2888_ = v___y_2914_;
v___y_2889_ = v___y_2915_;
v___y_2890_ = v___x_2918_;
v___y_2891_ = v___x_2924_;
goto v___jp_2871_;
}
}
v___jp_2925_:
{
lean_object* v_ref_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_ref_2943_ = lean_ctor_get(v___y_2927_, 2);
v___x_2944_ = l_Lean_SourceInfo_fromRef(v_ref_2943_, v___y_2942_);
v___x_2945_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2946_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_2945_);
v___x_2947_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_2948_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2947_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2951_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2933_) == 1)
{
lean_object* v_val_2952_; lean_object* v___x_2953_; 
v_val_2952_ = lean_ctor_get(v___y_2933_, 0);
lean_inc(v_val_2952_);
lean_dec_ref_known(v___y_2933_, 1);
v___x_2953_ = l_Array_mkArray1___redArg(v_val_2952_);
v___y_2724_ = v___x_2950_;
v___y_2725_ = v___y_2926_;
v___y_2726_ = v___y_2928_;
v___y_2727_ = v___y_2927_;
v___y_2728_ = v___x_2946_;
v___y_2729_ = v___y_2929_;
v___y_2730_ = v___x_2949_;
v___y_2731_ = v___y_2930_;
v___y_2732_ = v___y_2931_;
v___y_2733_ = v___x_2951_;
v___y_2734_ = v___y_2932_;
v___y_2735_ = v___y_2934_;
v___y_2736_ = v___y_2936_;
v___y_2737_ = v___y_2937_;
v___y_2738_ = v___y_2938_;
v___y_2739_ = v___y_2939_;
v___y_2740_ = v___y_2935_;
v___y_2741_ = v___x_2944_;
v___y_2742_ = v___y_2940_;
v___y_2743_ = v___y_2941_;
v___y_2744_ = v___x_2953_;
goto v___jp_2723_;
}
else
{
lean_object* v___x_2954_; 
lean_dec(v___y_2933_);
v___x_2954_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2724_ = v___x_2950_;
v___y_2725_ = v___y_2926_;
v___y_2726_ = v___y_2928_;
v___y_2727_ = v___y_2927_;
v___y_2728_ = v___x_2946_;
v___y_2729_ = v___y_2929_;
v___y_2730_ = v___x_2949_;
v___y_2731_ = v___y_2930_;
v___y_2732_ = v___y_2931_;
v___y_2733_ = v___x_2951_;
v___y_2734_ = v___y_2932_;
v___y_2735_ = v___y_2934_;
v___y_2736_ = v___y_2936_;
v___y_2737_ = v___y_2937_;
v___y_2738_ = v___y_2938_;
v___y_2739_ = v___y_2939_;
v___y_2740_ = v___y_2935_;
v___y_2741_ = v___x_2944_;
v___y_2742_ = v___y_2940_;
v___y_2743_ = v___y_2941_;
v___y_2744_ = v___x_2954_;
goto v___jp_2723_;
}
}
v___jp_2955_:
{
lean_object* v___x_2972_; lean_object* v_a_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2972_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2956_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2972_);
v___x_2974_ = lean_array_get_size(v___y_2961_);
v___x_2975_ = lean_nat_dec_eq(v___x_2974_, v___x_2542_);
if (v___x_2975_ == 0)
{
if (lean_obj_tag(v___y_2958_) == 0)
{
v___y_2926_ = v___y_2957_;
v___y_2927_ = v___y_2970_;
v___y_2928_ = v___y_2959_;
v___y_2929_ = v___y_2966_;
v___y_2930_ = v___y_2960_;
v___y_2931_ = v_a_2973_;
v___y_2932_ = v___y_2967_;
v___y_2933_ = v___y_2962_;
v___y_2934_ = v___y_2965_;
v___y_2935_ = v___y_2958_;
v___y_2936_ = v___y_2968_;
v___y_2937_ = v___y_2964_;
v___y_2938_ = v___y_2969_;
v___y_2939_ = v___y_2971_;
v___y_2940_ = v_stxForExecution_2963_;
v___y_2941_ = v___y_2961_;
v___y_2942_ = v___x_2975_;
goto v___jp_2925_;
}
else
{
if (v___y_2960_ == 0)
{
v___y_2926_ = v___y_2957_;
v___y_2927_ = v___y_2970_;
v___y_2928_ = v___y_2959_;
v___y_2929_ = v___y_2966_;
v___y_2930_ = v___y_2960_;
v___y_2931_ = v_a_2973_;
v___y_2932_ = v___y_2967_;
v___y_2933_ = v___y_2962_;
v___y_2934_ = v___y_2965_;
v___y_2935_ = v___y_2958_;
v___y_2936_ = v___y_2968_;
v___y_2937_ = v___y_2964_;
v___y_2938_ = v___y_2969_;
v___y_2939_ = v___y_2971_;
v___y_2940_ = v_stxForExecution_2963_;
v___y_2941_ = v___y_2961_;
v___y_2942_ = v___y_2960_;
goto v___jp_2925_;
}
else
{
lean_object* v_ref_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_ref_2976_ = lean_ctor_get(v___y_2970_, 2);
v___x_2977_ = l_Lean_SourceInfo_fromRef(v_ref_2976_, v___x_2975_);
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2979_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_2978_);
v___x_2980_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_2981_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2984_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2962_) == 1)
{
lean_object* v_val_2985_; lean_object* v___x_2986_; 
v_val_2985_ = lean_ctor_get(v___y_2962_, 0);
lean_inc(v_val_2985_);
lean_dec_ref_known(v___y_2962_, 1);
v___x_2986_ = l_Array_mkArray1___redArg(v_val_2985_);
v___y_2788_ = v___x_2977_;
v___y_2789_ = v___y_2957_;
v___y_2790_ = v___x_2983_;
v___y_2791_ = v___y_2959_;
v___y_2792_ = v___y_2970_;
v___y_2793_ = v___x_2984_;
v___y_2794_ = v___x_2982_;
v___y_2795_ = v___y_2966_;
v___y_2796_ = v___y_2960_;
v___y_2797_ = v_a_2973_;
v___y_2798_ = v___y_2967_;
v___y_2799_ = v___y_2965_;
v___y_2800_ = v___x_2979_;
v___y_2801_ = v___y_2968_;
v___y_2802_ = v___y_2964_;
v___y_2803_ = v___y_2969_;
v___y_2804_ = v___y_2971_;
v___y_2805_ = v___y_2958_;
v___y_2806_ = v_stxForExecution_2963_;
v___y_2807_ = v___y_2961_;
v___y_2808_ = v___x_2986_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2987_; 
lean_dec(v___y_2962_);
v___x_2987_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2788_ = v___x_2977_;
v___y_2789_ = v___y_2957_;
v___y_2790_ = v___x_2983_;
v___y_2791_ = v___y_2959_;
v___y_2792_ = v___y_2970_;
v___y_2793_ = v___x_2984_;
v___y_2794_ = v___x_2982_;
v___y_2795_ = v___y_2966_;
v___y_2796_ = v___y_2960_;
v___y_2797_ = v_a_2973_;
v___y_2798_ = v___y_2967_;
v___y_2799_ = v___y_2965_;
v___y_2800_ = v___x_2979_;
v___y_2801_ = v___y_2968_;
v___y_2802_ = v___y_2964_;
v___y_2803_ = v___y_2969_;
v___y_2804_ = v___y_2971_;
v___y_2805_ = v___y_2958_;
v___y_2806_ = v_stxForExecution_2963_;
v___y_2807_ = v___y_2961_;
v___y_2808_ = v___x_2987_;
goto v___jp_2787_;
}
}
}
}
else
{
lean_dec_ref(v___y_2961_);
if (lean_obj_tag(v___y_2958_) == 0)
{
lean_object* v_ref_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_ref_2988_ = lean_ctor_get(v___y_2970_, 2);
v___x_2989_ = 0;
v___x_2990_ = l_Lean_SourceInfo_fromRef(v_ref_2988_, v___x_2989_);
v___x_2991_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2992_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_2991_);
v___x_2993_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_2994_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2997_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2962_) == 1)
{
lean_object* v_val_2998_; lean_object* v___x_2999_; 
v_val_2998_ = lean_ctor_get(v___y_2962_, 0);
lean_inc(v_val_2998_);
lean_dec_ref_known(v___y_2962_, 1);
v___x_2999_ = l_Array_mkArray1___redArg(v_val_2998_);
v___y_2843_ = v___y_2957_;
v___y_2844_ = v___y_2959_;
v___y_2845_ = v___y_2970_;
v___y_2846_ = v___x_2990_;
v___y_2847_ = v___y_2966_;
v___y_2848_ = v___y_2960_;
v___y_2849_ = v_a_2973_;
v___y_2850_ = v___y_2967_;
v___y_2851_ = v___y_2965_;
v___y_2852_ = v___x_2997_;
v___y_2853_ = v___y_2969_;
v___y_2854_ = v___y_2968_;
v___y_2855_ = v___y_2964_;
v___y_2856_ = v___y_2958_;
v___y_2857_ = v___y_2971_;
v___y_2858_ = v___x_2995_;
v___y_2859_ = v___x_2996_;
v___y_2860_ = v___x_2992_;
v___y_2861_ = v_stxForExecution_2963_;
v___y_2862_ = v___x_2999_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_3000_; 
lean_dec(v___y_2962_);
v___x_3000_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2843_ = v___y_2957_;
v___y_2844_ = v___y_2959_;
v___y_2845_ = v___y_2970_;
v___y_2846_ = v___x_2990_;
v___y_2847_ = v___y_2966_;
v___y_2848_ = v___y_2960_;
v___y_2849_ = v_a_2973_;
v___y_2850_ = v___y_2967_;
v___y_2851_ = v___y_2965_;
v___y_2852_ = v___x_2997_;
v___y_2853_ = v___y_2969_;
v___y_2854_ = v___y_2968_;
v___y_2855_ = v___y_2964_;
v___y_2856_ = v___y_2958_;
v___y_2857_ = v___y_2971_;
v___y_2858_ = v___x_2995_;
v___y_2859_ = v___x_2996_;
v___y_2860_ = v___x_2992_;
v___y_2861_ = v_stxForExecution_2963_;
v___y_2862_ = v___x_3000_;
goto v___jp_2842_;
}
}
else
{
lean_object* v_ref_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_ref_3001_ = lean_ctor_get(v___y_2970_, 2);
v___x_3002_ = 0;
v___x_3003_ = l_Lean_SourceInfo_fromRef(v_ref_3001_, v___x_3002_);
v___x_3004_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3005_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3004_);
v___x_3006_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_3007_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3010_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2962_) == 1)
{
lean_object* v_val_3011_; lean_object* v___x_3012_; 
v_val_3011_ = lean_ctor_get(v___y_2962_, 0);
lean_inc(v_val_3011_);
lean_dec_ref_known(v___y_2962_, 1);
v___x_3012_ = l_Array_mkArray1___redArg(v_val_3011_);
v___y_2897_ = v___y_2957_;
v___y_2898_ = v___x_3003_;
v___y_2899_ = v___y_2959_;
v___y_2900_ = v___y_2970_;
v___y_2901_ = v___y_2966_;
v___y_2902_ = v___y_2960_;
v___y_2903_ = v___x_3008_;
v___y_2904_ = v_a_2973_;
v___y_2905_ = v___y_2967_;
v___y_2906_ = v___y_2965_;
v___y_2907_ = v___x_3009_;
v___y_2908_ = v___y_2969_;
v___y_2909_ = v___y_2968_;
v___y_2910_ = v___y_2964_;
v___y_2911_ = v___y_2971_;
v___y_2912_ = v___y_2958_;
v___y_2913_ = v___x_3010_;
v___y_2914_ = v_stxForExecution_2963_;
v___y_2915_ = v___x_3005_;
v___y_2916_ = v___x_3012_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_3013_; 
lean_dec(v___y_2962_);
v___x_3013_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2897_ = v___y_2957_;
v___y_2898_ = v___x_3003_;
v___y_2899_ = v___y_2959_;
v___y_2900_ = v___y_2970_;
v___y_2901_ = v___y_2966_;
v___y_2902_ = v___y_2960_;
v___y_2903_ = v___x_3008_;
v___y_2904_ = v_a_2973_;
v___y_2905_ = v___y_2967_;
v___y_2906_ = v___y_2965_;
v___y_2907_ = v___x_3009_;
v___y_2908_ = v___y_2969_;
v___y_2909_ = v___y_2968_;
v___y_2910_ = v___y_2964_;
v___y_2911_ = v___y_2971_;
v___y_2912_ = v___y_2958_;
v___y_2913_ = v___x_3010_;
v___y_2914_ = v_stxForExecution_2963_;
v___y_2915_ = v___x_3005_;
v___y_2916_ = v___x_3013_;
goto v___jp_2896_;
}
}
}
}
v___jp_3014_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_inc_ref_n(v___y_3022_, 2);
v___x_3037_ = l_Array_append___redArg(v___y_3022_, v___y_3036_);
lean_dec_ref(v___y_3036_);
lean_inc_n(v___y_3034_, 3);
lean_inc_n(v___y_3023_, 5);
v___x_3038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3038_, 0, v___y_3023_);
lean_ctor_set(v___x_3038_, 1, v___y_3034_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
v___x_3039_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3023_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3042_ = l_Lean_Syntax_SepArray_ofElems(v___x_3041_, v___y_3035_);
v___x_3043_ = l_Array_append___redArg(v___y_3022_, v___x_3042_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3044_, 0, v___y_3023_);
lean_ctor_set(v___x_3044_, 1, v___y_3034_);
lean_ctor_set(v___x_3044_, 2, v___x_3043_);
v___x_3045_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3023_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_Syntax_node3(v___y_3023_, v___y_3034_, v___x_3040_, v___x_3044_, v___x_3046_);
lean_inc(v___y_3015_);
v___x_3048_ = l_Lean_Syntax_node5(v___y_3023_, v___y_3033_, v___y_3025_, v___y_3015_, v___y_3032_, v___x_3038_, v___x_3047_);
v___y_2956_ = v___y_3015_;
v___y_2957_ = v___y_3017_;
v___y_2958_ = v___y_3028_;
v___y_2959_ = v___y_3019_;
v___y_2960_ = v___y_3024_;
v___y_2961_ = v___y_3035_;
v___y_2962_ = v___y_3026_;
v_stxForExecution_2963_ = v___x_3048_;
v___y_2964_ = v___y_3030_;
v___y_2965_ = v___y_3018_;
v___y_2966_ = v___y_3016_;
v___y_2967_ = v___y_3027_;
v___y_2968_ = v___y_3029_;
v___y_2969_ = v___y_3020_;
v___y_2970_ = v___y_3031_;
v___y_2971_ = v___y_3021_;
goto v___jp_2955_;
}
v___jp_3049_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_inc_ref(v___y_3056_);
v___x_3071_ = l_Array_append___redArg(v___y_3056_, v___y_3070_);
lean_dec_ref(v___y_3070_);
lean_inc(v___y_3068_);
lean_inc(v___y_3057_);
v___x_3072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3072_, 0, v___y_3057_);
lean_ctor_set(v___x_3072_, 1, v___y_3068_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
if (lean_obj_tag(v___y_3052_) == 1)
{
lean_object* v_val_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_val_3073_ = lean_ctor_get(v___y_3052_, 0);
v___x_3074_ = l_Lean_SourceInfo_fromRef(v_val_3073_, v___x_2527_);
v___x_3075_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = l_Array_mkArray1___redArg(v___x_3076_);
v___y_3015_ = v___y_3050_;
v___y_3016_ = v___y_3051_;
v___y_3017_ = v___y_3052_;
v___y_3018_ = v___y_3053_;
v___y_3019_ = v___y_3054_;
v___y_3020_ = v___y_3055_;
v___y_3021_ = v___y_3058_;
v___y_3022_ = v___y_3056_;
v___y_3023_ = v___y_3057_;
v___y_3024_ = v___y_3059_;
v___y_3025_ = v___y_3060_;
v___y_3026_ = v___y_3062_;
v___y_3027_ = v___y_3061_;
v___y_3028_ = v___y_3064_;
v___y_3029_ = v___y_3063_;
v___y_3030_ = v___y_3065_;
v___y_3031_ = v___y_3066_;
v___y_3032_ = v___x_3072_;
v___y_3033_ = v___y_3067_;
v___y_3034_ = v___y_3068_;
v___y_3035_ = v___y_3069_;
v___y_3036_ = v___x_3077_;
goto v___jp_3014_;
}
else
{
lean_object* v___x_3078_; 
v___x_3078_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3015_ = v___y_3050_;
v___y_3016_ = v___y_3051_;
v___y_3017_ = v___y_3052_;
v___y_3018_ = v___y_3053_;
v___y_3019_ = v___y_3054_;
v___y_3020_ = v___y_3055_;
v___y_3021_ = v___y_3058_;
v___y_3022_ = v___y_3056_;
v___y_3023_ = v___y_3057_;
v___y_3024_ = v___y_3059_;
v___y_3025_ = v___y_3060_;
v___y_3026_ = v___y_3062_;
v___y_3027_ = v___y_3061_;
v___y_3028_ = v___y_3064_;
v___y_3029_ = v___y_3063_;
v___y_3030_ = v___y_3065_;
v___y_3031_ = v___y_3066_;
v___y_3032_ = v___x_3072_;
v___y_3033_ = v___y_3067_;
v___y_3034_ = v___y_3068_;
v___y_3035_ = v___y_3069_;
v___y_3036_ = v___x_3078_;
goto v___jp_3014_;
}
}
v___jp_3079_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_inc_ref_n(v___y_3095_, 2);
v___x_3102_ = l_Array_append___redArg(v___y_3095_, v___y_3101_);
lean_dec_ref(v___y_3101_);
lean_inc_n(v___y_3089_, 3);
lean_inc_n(v___y_3088_, 5);
v___x_3103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3088_);
lean_ctor_set(v___x_3103_, 1, v___y_3089_);
lean_ctor_set(v___x_3103_, 2, v___x_3102_);
v___x_3104_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3088_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3107_ = l_Lean_Syntax_SepArray_ofElems(v___x_3106_, v___y_3099_);
v___x_3108_ = l_Array_append___redArg(v___y_3095_, v___x_3107_);
lean_dec_ref(v___x_3107_);
v___x_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3088_);
lean_ctor_set(v___x_3109_, 1, v___y_3089_);
lean_ctor_set(v___x_3109_, 2, v___x_3108_);
v___x_3110_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3088_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_Syntax_node3(v___y_3088_, v___y_3089_, v___x_3105_, v___x_3109_, v___x_3111_);
lean_inc(v___y_3080_);
v___x_3113_ = l_Lean_Syntax_node5(v___y_3088_, v___y_3100_, v___y_3098_, v___y_3080_, v___y_3090_, v___x_3103_, v___x_3112_);
v___y_2956_ = v___y_3080_;
v___y_2957_ = v___y_3082_;
v___y_2958_ = v___y_3093_;
v___y_2959_ = v___y_3084_;
v___y_2960_ = v___y_3087_;
v___y_2961_ = v___y_3099_;
v___y_2962_ = v___y_3091_;
v_stxForExecution_2963_ = v___x_3113_;
v___y_2964_ = v___y_3096_;
v___y_2965_ = v___y_3083_;
v___y_2966_ = v___y_3081_;
v___y_2967_ = v___y_3092_;
v___y_2968_ = v___y_3094_;
v___y_2969_ = v___y_3085_;
v___y_2970_ = v___y_3097_;
v___y_2971_ = v___y_3086_;
goto v___jp_2955_;
}
v___jp_3114_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_inc_ref(v___y_3130_);
v___x_3136_ = l_Array_append___redArg(v___y_3130_, v___y_3135_);
lean_dec_ref(v___y_3135_);
lean_inc(v___y_3124_);
lean_inc(v___y_3123_);
v___x_3137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3137_, 0, v___y_3123_);
lean_ctor_set(v___x_3137_, 1, v___y_3124_);
lean_ctor_set(v___x_3137_, 2, v___x_3136_);
if (lean_obj_tag(v___y_3117_) == 1)
{
lean_object* v_val_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_val_3138_ = lean_ctor_get(v___y_3117_, 0);
v___x_3139_ = l_Lean_SourceInfo_fromRef(v_val_3138_, v___x_2527_);
v___x_3140_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = l_Array_mkArray1___redArg(v___x_3141_);
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___y_3123_;
v___y_3089_ = v___y_3124_;
v___y_3090_ = v___x_3137_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3129_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___x_3142_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3143_; 
v___x_3143_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___y_3123_;
v___y_3089_ = v___y_3124_;
v___y_3090_ = v___x_3137_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3129_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___x_3143_;
goto v___jp_3079_;
}
}
v___jp_3144_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_inc_ref_n(v___y_3159_, 2);
v___x_3167_ = l_Array_append___redArg(v___y_3159_, v___y_3166_);
lean_dec_ref(v___y_3166_);
lean_inc_n(v___y_3148_, 2);
lean_inc_n(v___y_3162_, 2);
v___x_3168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3168_, 0, v___y_3162_);
lean_ctor_set(v___x_3168_, 1, v___y_3148_);
lean_ctor_set(v___x_3168_, 2, v___x_3167_);
v___x_3169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3169_, 0, v___y_3162_);
lean_ctor_set(v___x_3169_, 1, v___y_3148_);
lean_ctor_set(v___x_3169_, 2, v___y_3159_);
lean_inc(v___y_3146_);
v___x_3170_ = l_Lean_Syntax_node5(v___y_3162_, v___y_3145_, v___y_3165_, v___y_3146_, v___y_3163_, v___x_3168_, v___x_3169_);
v___y_2956_ = v___y_3146_;
v___y_2957_ = v___y_3149_;
v___y_2958_ = v___y_3157_;
v___y_2959_ = v___y_3151_;
v___y_2960_ = v___y_3154_;
v___y_2961_ = v___y_3164_;
v___y_2962_ = v___y_3155_;
v_stxForExecution_2963_ = v___x_3170_;
v___y_2964_ = v___y_3160_;
v___y_2965_ = v___y_3150_;
v___y_2966_ = v___y_3147_;
v___y_2967_ = v___y_3156_;
v___y_2968_ = v___y_3158_;
v___y_2969_ = v___y_3152_;
v___y_2970_ = v___y_3161_;
v___y_2971_ = v___y_3153_;
goto v___jp_2955_;
}
v___jp_3171_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_inc_ref(v___y_3186_);
v___x_3193_ = l_Array_append___redArg(v___y_3186_, v___y_3192_);
lean_dec_ref(v___y_3192_);
lean_inc(v___y_3175_);
lean_inc(v___y_3189_);
v___x_3194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3194_, 0, v___y_3189_);
lean_ctor_set(v___x_3194_, 1, v___y_3175_);
lean_ctor_set(v___x_3194_, 2, v___x_3193_);
if (lean_obj_tag(v___y_3176_) == 1)
{
lean_object* v_val_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_val_3195_ = lean_ctor_get(v___y_3176_, 0);
v___x_3196_ = l_Lean_SourceInfo_fromRef(v_val_3195_, v___x_2527_);
v___x_3197_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Array_mkArray1___redArg(v___x_3198_);
v___y_3145_ = v___y_3172_;
v___y_3146_ = v___y_3173_;
v___y_3147_ = v___y_3174_;
v___y_3148_ = v___y_3175_;
v___y_3149_ = v___y_3176_;
v___y_3150_ = v___y_3177_;
v___y_3151_ = v___y_3178_;
v___y_3152_ = v___y_3179_;
v___y_3153_ = v___y_3180_;
v___y_3154_ = v___y_3181_;
v___y_3155_ = v___y_3183_;
v___y_3156_ = v___y_3182_;
v___y_3157_ = v___y_3185_;
v___y_3158_ = v___y_3184_;
v___y_3159_ = v___y_3186_;
v___y_3160_ = v___y_3187_;
v___y_3161_ = v___y_3188_;
v___y_3162_ = v___y_3189_;
v___y_3163_ = v___x_3194_;
v___y_3164_ = v___y_3190_;
v___y_3165_ = v___y_3191_;
v___y_3166_ = v___x_3199_;
goto v___jp_3144_;
}
else
{
lean_object* v___x_3200_; 
v___x_3200_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3145_ = v___y_3172_;
v___y_3146_ = v___y_3173_;
v___y_3147_ = v___y_3174_;
v___y_3148_ = v___y_3175_;
v___y_3149_ = v___y_3176_;
v___y_3150_ = v___y_3177_;
v___y_3151_ = v___y_3178_;
v___y_3152_ = v___y_3179_;
v___y_3153_ = v___y_3180_;
v___y_3154_ = v___y_3181_;
v___y_3155_ = v___y_3183_;
v___y_3156_ = v___y_3182_;
v___y_3157_ = v___y_3185_;
v___y_3158_ = v___y_3184_;
v___y_3159_ = v___y_3186_;
v___y_3160_ = v___y_3187_;
v___y_3161_ = v___y_3188_;
v___y_3162_ = v___y_3189_;
v___y_3163_ = v___x_3194_;
v___y_3164_ = v___y_3190_;
v___y_3165_ = v___y_3191_;
v___y_3166_ = v___x_3200_;
goto v___jp_3144_;
}
}
v___jp_3201_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_inc_ref_n(v___y_3210_, 2);
v___x_3224_ = l_Array_append___redArg(v___y_3210_, v___y_3223_);
lean_dec_ref(v___y_3223_);
lean_inc_n(v___y_3222_, 2);
lean_inc_n(v___y_3215_, 2);
v___x_3225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3225_, 0, v___y_3215_);
lean_ctor_set(v___x_3225_, 1, v___y_3222_);
lean_ctor_set(v___x_3225_, 2, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3226_, 0, v___y_3215_);
lean_ctor_set(v___x_3226_, 1, v___y_3222_);
lean_ctor_set(v___x_3226_, 2, v___y_3210_);
lean_inc(v___y_3202_);
v___x_3227_ = l_Lean_Syntax_node5(v___y_3215_, v___y_3218_, v___y_3212_, v___y_3202_, v___y_3220_, v___x_3225_, v___x_3226_);
v___y_2956_ = v___y_3202_;
v___y_2957_ = v___y_3204_;
v___y_2958_ = v___y_3214_;
v___y_2959_ = v___y_3206_;
v___y_2960_ = v___y_3209_;
v___y_2961_ = v___y_3221_;
v___y_2962_ = v___y_3211_;
v_stxForExecution_2963_ = v___x_3227_;
v___y_2964_ = v___y_3217_;
v___y_2965_ = v___y_3205_;
v___y_2966_ = v___y_3203_;
v___y_2967_ = v___y_3213_;
v___y_2968_ = v___y_3216_;
v___y_2969_ = v___y_3207_;
v___y_2970_ = v___y_3219_;
v___y_2971_ = v___y_3208_;
goto v___jp_2955_;
}
v___jp_3228_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_inc_ref(v___y_3237_);
v___x_3250_ = l_Array_append___redArg(v___y_3237_, v___y_3249_);
lean_dec_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc(v___y_3243_);
v___x_3251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3251_, 0, v___y_3243_);
lean_ctor_set(v___x_3251_, 1, v___y_3248_);
lean_ctor_set(v___x_3251_, 2, v___x_3250_);
if (lean_obj_tag(v___y_3231_) == 1)
{
lean_object* v_val_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_val_3252_ = lean_ctor_get(v___y_3231_, 0);
v___x_3253_ = l_Lean_SourceInfo_fromRef(v_val_3252_, v___x_2527_);
v___x_3254_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Array_mkArray1___redArg(v___x_3255_);
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v___y_3238_;
v___y_3214_ = v___y_3242_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3241_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3245_;
v___y_3219_ = v___y_3246_;
v___y_3220_ = v___x_3251_;
v___y_3221_ = v___y_3247_;
v___y_3222_ = v___y_3248_;
v___y_3223_ = v___x_3256_;
goto v___jp_3201_;
}
else
{
lean_object* v___x_3257_; 
v___x_3257_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v___y_3238_;
v___y_3214_ = v___y_3242_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3241_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3245_;
v___y_3219_ = v___y_3246_;
v___y_3220_ = v___x_3251_;
v___y_3221_ = v___y_3247_;
v___y_3222_ = v___y_3248_;
v___y_3223_ = v___x_3257_;
goto v___jp_3201_;
}
}
v___jp_3258_:
{
lean_object* v_ref_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_ref_3275_ = lean_ctor_get(v___y_3272_, 2);
v___x_3276_ = l_Lean_SourceInfo_fromRef(v_ref_3275_, v___y_3274_);
v___x_3277_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3278_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3277_);
v___x_3279_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_3280_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3283_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3268_) == 1)
{
lean_object* v_val_3284_; lean_object* v___x_3285_; 
v_val_3284_ = lean_ctor_get(v___y_3268_, 0);
lean_inc(v_val_3284_);
v___x_3285_ = l_Array_mkArray1___redArg(v_val_3284_);
v___y_3050_ = v___y_3259_;
v___y_3051_ = v___y_3260_;
v___y_3052_ = v___y_3261_;
v___y_3053_ = v___y_3262_;
v___y_3054_ = v___y_3263_;
v___y_3055_ = v___y_3264_;
v___y_3056_ = v___x_3283_;
v___y_3057_ = v___x_3276_;
v___y_3058_ = v___y_3265_;
v___y_3059_ = v___y_3266_;
v___y_3060_ = v___x_3281_;
v___y_3061_ = v___y_3267_;
v___y_3062_ = v___y_3268_;
v___y_3063_ = v___y_3269_;
v___y_3064_ = v___y_3270_;
v___y_3065_ = v___y_3271_;
v___y_3066_ = v___y_3272_;
v___y_3067_ = v___x_3278_;
v___y_3068_ = v___x_3282_;
v___y_3069_ = v___y_3273_;
v___y_3070_ = v___x_3285_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3050_ = v___y_3259_;
v___y_3051_ = v___y_3260_;
v___y_3052_ = v___y_3261_;
v___y_3053_ = v___y_3262_;
v___y_3054_ = v___y_3263_;
v___y_3055_ = v___y_3264_;
v___y_3056_ = v___x_3283_;
v___y_3057_ = v___x_3276_;
v___y_3058_ = v___y_3265_;
v___y_3059_ = v___y_3266_;
v___y_3060_ = v___x_3281_;
v___y_3061_ = v___y_3267_;
v___y_3062_ = v___y_3268_;
v___y_3063_ = v___y_3269_;
v___y_3064_ = v___y_3270_;
v___y_3065_ = v___y_3271_;
v___y_3066_ = v___y_3272_;
v___y_3067_ = v___x_3278_;
v___y_3068_ = v___x_3282_;
v___y_3069_ = v___y_3273_;
v___y_3070_ = v___x_3286_;
goto v___jp_3049_;
}
}
v___jp_3287_:
{
lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = lean_array_get_size(v_argsArray_3294_);
v___x_3304_ = lean_nat_dec_eq(v___x_3303_, v___x_2542_);
if (v___x_3304_ == 0)
{
if (lean_obj_tag(v___y_3289_) == 0)
{
v___y_3259_ = v___y_3288_;
v___y_3260_ = v___y_3297_;
v___y_3261_ = v___y_3290_;
v___y_3262_ = v___y_3296_;
v___y_3263_ = v___y_3291_;
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___y_3292_;
v___y_3267_ = v___y_3298_;
v___y_3268_ = v___y_3293_;
v___y_3269_ = v___y_3299_;
v___y_3270_ = v___y_3289_;
v___y_3271_ = v___y_3295_;
v___y_3272_ = v___y_3301_;
v___y_3273_ = v_argsArray_3294_;
v___y_3274_ = v___x_3304_;
goto v___jp_3258_;
}
else
{
if (v___y_3292_ == 0)
{
v___y_3259_ = v___y_3288_;
v___y_3260_ = v___y_3297_;
v___y_3261_ = v___y_3290_;
v___y_3262_ = v___y_3296_;
v___y_3263_ = v___y_3291_;
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___y_3292_;
v___y_3267_ = v___y_3298_;
v___y_3268_ = v___y_3293_;
v___y_3269_ = v___y_3299_;
v___y_3270_ = v___y_3289_;
v___y_3271_ = v___y_3295_;
v___y_3272_ = v___y_3301_;
v___y_3273_ = v_argsArray_3294_;
v___y_3274_ = v___y_3292_;
goto v___jp_3258_;
}
else
{
lean_object* v_ref_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_ref_3305_ = lean_ctor_get(v___y_3301_, 2);
v___x_3306_ = l_Lean_SourceInfo_fromRef(v_ref_3305_, v___x_3304_);
v___x_3307_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3308_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3307_);
v___x_3309_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_3310_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3313_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3293_) == 1)
{
lean_object* v_val_3314_; lean_object* v___x_3315_; 
v_val_3314_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3314_);
v___x_3315_ = l_Array_mkArray1___redArg(v_val_3314_);
v___y_3115_ = v___y_3288_;
v___y_3116_ = v___y_3297_;
v___y_3117_ = v___y_3290_;
v___y_3118_ = v___y_3296_;
v___y_3119_ = v___y_3291_;
v___y_3120_ = v___y_3300_;
v___y_3121_ = v___y_3302_;
v___y_3122_ = v___y_3292_;
v___y_3123_ = v___x_3306_;
v___y_3124_ = v___x_3312_;
v___y_3125_ = v___y_3293_;
v___y_3126_ = v___y_3298_;
v___y_3127_ = v___y_3299_;
v___y_3128_ = v___y_3289_;
v___y_3129_ = v___y_3295_;
v___y_3130_ = v___x_3313_;
v___y_3131_ = v___y_3301_;
v___y_3132_ = v___x_3311_;
v___y_3133_ = v_argsArray_3294_;
v___y_3134_ = v___x_3308_;
v___y_3135_ = v___x_3315_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3316_; 
v___x_3316_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3115_ = v___y_3288_;
v___y_3116_ = v___y_3297_;
v___y_3117_ = v___y_3290_;
v___y_3118_ = v___y_3296_;
v___y_3119_ = v___y_3291_;
v___y_3120_ = v___y_3300_;
v___y_3121_ = v___y_3302_;
v___y_3122_ = v___y_3292_;
v___y_3123_ = v___x_3306_;
v___y_3124_ = v___x_3312_;
v___y_3125_ = v___y_3293_;
v___y_3126_ = v___y_3298_;
v___y_3127_ = v___y_3299_;
v___y_3128_ = v___y_3289_;
v___y_3129_ = v___y_3295_;
v___y_3130_ = v___x_3313_;
v___y_3131_ = v___y_3301_;
v___y_3132_ = v___x_3311_;
v___y_3133_ = v_argsArray_3294_;
v___y_3134_ = v___x_3308_;
v___y_3135_ = v___x_3316_;
goto v___jp_3114_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3289_) == 0)
{
lean_object* v_ref_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_ref_3317_ = lean_ctor_get(v___y_3301_, 2);
v___x_3318_ = 0;
v___x_3319_ = l_Lean_SourceInfo_fromRef(v_ref_3317_, v___x_3318_);
v___x_3320_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3321_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3320_);
v___x_3322_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3326_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3293_) == 1)
{
lean_object* v_val_3327_; lean_object* v___x_3328_; 
v_val_3327_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3327_);
v___x_3328_ = l_Array_mkArray1___redArg(v_val_3327_);
v___y_3172_ = v___x_3321_;
v___y_3173_ = v___y_3288_;
v___y_3174_ = v___y_3297_;
v___y_3175_ = v___x_3325_;
v___y_3176_ = v___y_3290_;
v___y_3177_ = v___y_3296_;
v___y_3178_ = v___y_3291_;
v___y_3179_ = v___y_3300_;
v___y_3180_ = v___y_3302_;
v___y_3181_ = v___y_3292_;
v___y_3182_ = v___y_3298_;
v___y_3183_ = v___y_3293_;
v___y_3184_ = v___y_3299_;
v___y_3185_ = v___y_3289_;
v___y_3186_ = v___x_3326_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___x_3319_;
v___y_3190_ = v_argsArray_3294_;
v___y_3191_ = v___x_3324_;
v___y_3192_ = v___x_3328_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3329_; 
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3172_ = v___x_3321_;
v___y_3173_ = v___y_3288_;
v___y_3174_ = v___y_3297_;
v___y_3175_ = v___x_3325_;
v___y_3176_ = v___y_3290_;
v___y_3177_ = v___y_3296_;
v___y_3178_ = v___y_3291_;
v___y_3179_ = v___y_3300_;
v___y_3180_ = v___y_3302_;
v___y_3181_ = v___y_3292_;
v___y_3182_ = v___y_3298_;
v___y_3183_ = v___y_3293_;
v___y_3184_ = v___y_3299_;
v___y_3185_ = v___y_3289_;
v___y_3186_ = v___x_3326_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___x_3319_;
v___y_3190_ = v_argsArray_3294_;
v___y_3191_ = v___x_3324_;
v___y_3192_ = v___x_3329_;
goto v___jp_3171_;
}
}
else
{
lean_object* v_ref_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_ref_3330_ = lean_ctor_get(v___y_3301_, 2);
v___x_3331_ = 0;
v___x_3332_ = l_Lean_SourceInfo_fromRef(v_ref_3330_, v___x_3331_);
v___x_3333_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3334_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3333_);
v___x_3335_ = l_Lean_SourceInfo_fromRef(v_tk_2543_, v___x_2527_);
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3339_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3293_) == 1)
{
lean_object* v_val_3340_; lean_object* v___x_3341_; 
v_val_3340_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3340_);
v___x_3341_ = l_Array_mkArray1___redArg(v_val_3340_);
v___y_3229_ = v___y_3288_;
v___y_3230_ = v___y_3297_;
v___y_3231_ = v___y_3290_;
v___y_3232_ = v___y_3296_;
v___y_3233_ = v___y_3291_;
v___y_3234_ = v___y_3300_;
v___y_3235_ = v___y_3302_;
v___y_3236_ = v___y_3292_;
v___y_3237_ = v___x_3339_;
v___y_3238_ = v___y_3298_;
v___y_3239_ = v___y_3293_;
v___y_3240_ = v___x_3337_;
v___y_3241_ = v___y_3299_;
v___y_3242_ = v___y_3289_;
v___y_3243_ = v___x_3332_;
v___y_3244_ = v___y_3295_;
v___y_3245_ = v___x_3334_;
v___y_3246_ = v___y_3301_;
v___y_3247_ = v_argsArray_3294_;
v___y_3248_ = v___x_3338_;
v___y_3249_ = v___x_3341_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3229_ = v___y_3288_;
v___y_3230_ = v___y_3297_;
v___y_3231_ = v___y_3290_;
v___y_3232_ = v___y_3296_;
v___y_3233_ = v___y_3291_;
v___y_3234_ = v___y_3300_;
v___y_3235_ = v___y_3302_;
v___y_3236_ = v___y_3292_;
v___y_3237_ = v___x_3339_;
v___y_3238_ = v___y_3298_;
v___y_3239_ = v___y_3293_;
v___y_3240_ = v___x_3337_;
v___y_3241_ = v___y_3299_;
v___y_3242_ = v___y_3289_;
v___y_3243_ = v___x_3332_;
v___y_3244_ = v___y_3295_;
v___y_3245_ = v___x_3334_;
v___y_3246_ = v___y_3301_;
v___y_3247_ = v_argsArray_3294_;
v___y_3248_ = v___x_3338_;
v___y_3249_ = v___x_3342_;
goto v___jp_3228_;
}
}
}
}
v___jp_3343_:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3357_, v___y_3356_, v___y_3350_, v___y_3354_, v___y_3346_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = l_Lean_LibrarySuggestions_select(v_a_3361_, v___y_3359_, v___y_3356_, v___y_3350_, v___y_3354_, v___y_3346_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; size_t v_sz_3364_; size_t v___x_3365_; lean_object* v___x_3366_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v_sz_3364_ = lean_array_size(v_a_3363_);
v___x_3365_ = ((size_t)0ULL);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3363_, v_sz_3364_, v___x_3365_, v___y_3355_, v___y_3351_, v___y_3357_, v___y_3347_, v___y_3344_, v___y_3356_, v___y_3350_, v___y_3354_, v___y_3346_);
lean_dec(v_a_3363_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___y_3288_ = v___y_3345_;
v___y_3289_ = v___y_3358_;
v___y_3290_ = v___y_3348_;
v___y_3291_ = v___y_3349_;
v___y_3292_ = v___y_3352_;
v___y_3293_ = v___y_3353_;
v_argsArray_3294_ = v_a_3367_;
v___y_3295_ = v___y_3351_;
v___y_3296_ = v___y_3357_;
v___y_3297_ = v___y_3347_;
v___y_3298_ = v___y_3344_;
v___y_3299_ = v___y_3356_;
v___y_3300_ = v___y_3350_;
v___y_3301_ = v___y_3354_;
v___y_3302_ = v___y_3346_;
goto v___jp_3287_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v___y_3358_);
lean_dec(v___y_3353_);
lean_dec(v___y_3348_);
lean_dec(v___y_3345_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
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
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3353_);
lean_dec(v___y_3348_);
lean_dec(v___y_3345_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v_a_3376_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3362_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3362_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3353_);
lean_dec(v___y_3348_);
lean_dec(v___y_3345_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v_a_3384_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3360_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3360_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
v___jp_3392_:
{
lean_object* v_config_3409_; uint8_t v_suggestions_3410_; 
v_config_3409_ = lean_ctor_get(v___y_3407_, 0);
lean_inc_ref(v_config_3409_);
lean_dec_ref(v___y_3407_);
v_suggestions_3410_ = lean_ctor_get_uint8(v_config_3409_, sizeof(void*)*3 + 26);
if (v_suggestions_3410_ == 0)
{
lean_dec_ref(v_config_3409_);
lean_dec_ref(v___f_2531_);
v___y_3288_ = v___y_3394_;
v___y_3289_ = v___y_3405_;
v___y_3290_ = v___y_3397_;
v___y_3291_ = v___y_3398_;
v___y_3292_ = v___y_3401_;
v___y_3293_ = v___y_3402_;
v_argsArray_3294_ = v___y_3408_;
v___y_3295_ = v___y_3400_;
v___y_3296_ = v___y_3406_;
v___y_3297_ = v___y_3396_;
v___y_3298_ = v___y_3393_;
v___y_3299_ = v___y_3404_;
v___y_3300_ = v___y_3399_;
v___y_3301_ = v___y_3403_;
v___y_3302_ = v___y_3395_;
goto v___jp_3287_;
}
else
{
lean_object* v_maxSuggestions_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_maxSuggestions_3411_ = lean_ctor_get(v_config_3409_, 2);
lean_inc(v_maxSuggestions_3411_);
lean_dec_ref(v_config_3409_);
v___x_3412_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3413_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3411_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_unsigned_to_nat(100u);
v___x_3415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v___x_3412_);
lean_ctor_set(v___x_3415_, 2, v___f_2531_);
lean_ctor_set(v___x_3415_, 3, v___x_3413_);
v___y_3344_ = v___y_3393_;
v___y_3345_ = v___y_3394_;
v___y_3346_ = v___y_3395_;
v___y_3347_ = v___y_3396_;
v___y_3348_ = v___y_3397_;
v___y_3349_ = v___y_3398_;
v___y_3350_ = v___y_3399_;
v___y_3351_ = v___y_3400_;
v___y_3352_ = v___y_3401_;
v___y_3353_ = v___y_3402_;
v___y_3354_ = v___y_3403_;
v___y_3355_ = v___y_3408_;
v___y_3356_ = v___y_3404_;
v___y_3357_ = v___y_3406_;
v___y_3358_ = v___y_3405_;
v___y_3359_ = v___x_3415_;
goto v___jp_3343_;
}
else
{
lean_object* v_val_3416_; lean_object* v___x_3417_; 
v_val_3416_ = lean_ctor_get(v_maxSuggestions_3411_, 0);
lean_inc(v_val_3416_);
lean_dec_ref_known(v_maxSuggestions_3411_, 1);
v___x_3417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3417_, 0, v_val_3416_);
lean_ctor_set(v___x_3417_, 1, v___x_3412_);
lean_ctor_set(v___x_3417_, 2, v___f_2531_);
lean_ctor_set(v___x_3417_, 3, v___x_3413_);
v___y_3344_ = v___y_3393_;
v___y_3345_ = v___y_3394_;
v___y_3346_ = v___y_3395_;
v___y_3347_ = v___y_3396_;
v___y_3348_ = v___y_3397_;
v___y_3349_ = v___y_3398_;
v___y_3350_ = v___y_3399_;
v___y_3351_ = v___y_3400_;
v___y_3352_ = v___y_3401_;
v___y_3353_ = v___y_3402_;
v___y_3354_ = v___y_3403_;
v___y_3355_ = v___y_3408_;
v___y_3356_ = v___y_3404_;
v___y_3357_ = v___y_3406_;
v___y_3358_ = v___y_3405_;
v___y_3359_ = v___x_3417_;
goto v___jp_3343_;
}
}
}
v___jp_3418_:
{
uint8_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = 1;
lean_inc(v___y_3419_);
v___x_3434_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3419_, v___x_3433_, v___y_3425_, v___y_3427_, v___y_3421_);
if (lean_obj_tag(v___x_3434_) == 0)
{
if (lean_obj_tag(v___y_3431_) == 1)
{
lean_object* v_a_3435_; lean_object* v_val_3436_; lean_object* v___x_3437_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v_val_3436_ = lean_ctor_get(v___y_3431_, 0);
lean_inc(v_val_3436_);
lean_dec_ref_known(v___y_3431_, 1);
v___x_3437_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3436_);
lean_dec(v_val_3436_);
v___y_3393_ = v___y_3420_;
v___y_3394_ = v___y_3419_;
v___y_3395_ = v___y_3421_;
v___y_3396_ = v___y_3422_;
v___y_3397_ = v___y_3423_;
v___y_3398_ = v___x_3433_;
v___y_3399_ = v___y_3424_;
v___y_3400_ = v___y_3425_;
v___y_3401_ = v___y_3426_;
v___y_3402_ = v___y_3432_;
v___y_3403_ = v___y_3427_;
v___y_3404_ = v___y_3428_;
v___y_3405_ = v___y_3429_;
v___y_3406_ = v___y_3430_;
v___y_3407_ = v_a_3435_;
v___y_3408_ = v___x_3437_;
goto v___jp_3392_;
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
lean_dec(v___y_3431_);
v_a_3438_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3439_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3393_ = v___y_3420_;
v___y_3394_ = v___y_3419_;
v___y_3395_ = v___y_3421_;
v___y_3396_ = v___y_3422_;
v___y_3397_ = v___y_3423_;
v___y_3398_ = v___x_3433_;
v___y_3399_ = v___y_3424_;
v___y_3400_ = v___y_3425_;
v___y_3401_ = v___y_3426_;
v___y_3402_ = v___y_3432_;
v___y_3403_ = v___y_3427_;
v___y_3404_ = v___y_3428_;
v___y_3405_ = v___y_3429_;
v___y_3406_ = v___y_3430_;
v___y_3407_ = v_a_3438_;
v___y_3408_ = v___x_3439_;
goto v___jp_3392_;
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec(v___y_3429_);
lean_dec(v___y_3423_);
lean_dec(v___y_3419_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v_a_3440_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3434_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3434_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
v___jp_3448_:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Syntax_getOptional_x3f(v___y_3452_);
lean_dec(v___y_3452_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_box(0);
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3458_;
v___y_3421_ = v___y_3462_;
v___y_3422_ = v___y_3457_;
v___y_3423_ = v___y_3451_;
v___y_3424_ = v___y_3460_;
v___y_3425_ = v___y_3455_;
v___y_3426_ = v___y_3453_;
v___y_3427_ = v___y_3461_;
v___y_3428_ = v___y_3459_;
v___y_3429_ = v___y_3450_;
v___y_3430_ = v___y_3456_;
v___y_3431_ = v_args_3454_;
v___y_3432_ = v___x_3464_;
goto v___jp_3418_;
}
else
{
lean_object* v_val_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
v_val_3465_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3463_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_val_3465_);
lean_dec(v___x_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_val_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3458_;
v___y_3421_ = v___y_3462_;
v___y_3422_ = v___y_3457_;
v___y_3423_ = v___y_3451_;
v___y_3424_ = v___y_3460_;
v___y_3425_ = v___y_3455_;
v___y_3426_ = v___y_3453_;
v___y_3427_ = v___y_3461_;
v___y_3428_ = v___y_3459_;
v___y_3429_ = v___y_3450_;
v___y_3430_ = v___y_3456_;
v___y_3431_ = v_args_3454_;
v___y_3432_ = v___x_3470_;
goto v___jp_3418_;
}
}
}
}
v___jp_3474_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3489_ = lean_unsigned_to_nat(3u);
v___x_3490_ = l_Lean_Syntax_getArg(v___y_3476_, v___x_3489_);
lean_dec(v___y_3476_);
v___x_3491_ = l_Lean_Syntax_isNone(v___x_3490_);
if (v___x_3491_ == 0)
{
uint8_t v___x_3492_; 
lean_inc(v___x_3490_);
v___x_3492_ = l_Lean_Syntax_matchesNull(v___x_3490_, v___x_3473_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec(v___x_3490_);
lean_dec(v_o_3480_);
lean_dec(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec(v___y_3475_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_3493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3494_ = l_Lean_Syntax_getArg(v___x_3490_, v___x_2542_);
lean_dec(v___x_3490_);
v___x_3495_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3496_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3495_);
lean_inc(v___x_3494_);
v___x_3497_ = l_Lean_Syntax_isOfKind(v___x_3494_, v___x_3496_);
lean_dec(v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
lean_dec(v___x_3494_);
lean_dec(v_o_3480_);
lean_dec(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec(v___y_3475_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_3498_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; lean_object* v_args_3500_; lean_object* v___x_3501_; 
v___x_3499_ = l_Lean_Syntax_getArg(v___x_3494_, v___x_3473_);
lean_dec(v___x_3494_);
v_args_3500_ = l_Lean_Syntax_getArgs(v___x_3499_);
lean_dec(v___x_3499_);
v___x_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_args_3500_);
v___y_3449_ = v___y_3475_;
v___y_3450_ = v___y_3477_;
v___y_3451_ = v_o_3480_;
v___y_3452_ = v___y_3478_;
v___y_3453_ = v___y_3479_;
v_args_3454_ = v___x_3501_;
v___y_3455_ = v___y_3481_;
v___y_3456_ = v___y_3482_;
v___y_3457_ = v___y_3483_;
v___y_3458_ = v___y_3484_;
v___y_3459_ = v___y_3485_;
v___y_3460_ = v___y_3486_;
v___y_3461_ = v___y_3487_;
v___y_3462_ = v___y_3488_;
goto v___jp_3448_;
}
}
}
else
{
lean_object* v___x_3502_; 
lean_dec(v___x_3490_);
v___x_3502_ = lean_box(0);
v___y_3449_ = v___y_3475_;
v___y_3450_ = v___y_3477_;
v___y_3451_ = v_o_3480_;
v___y_3452_ = v___y_3478_;
v___y_3453_ = v___y_3479_;
v_args_3454_ = v___x_3502_;
v___y_3455_ = v___y_3481_;
v___y_3456_ = v___y_3482_;
v___y_3457_ = v___y_3483_;
v___y_3458_ = v___y_3484_;
v___y_3459_ = v___y_3485_;
v___y_3460_ = v___y_3486_;
v___y_3461_ = v___y_3487_;
v___y_3462_ = v___y_3488_;
goto v___jp_3448_;
}
}
v___jp_3503_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3513_ = lean_unsigned_to_nat(2u);
v___x_3514_ = l_Lean_Syntax_getArg(v_stx_2526_, v___x_3513_);
v___x_3515_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3516_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3515_);
lean_inc(v___x_3514_);
v___x_3517_ = l_Lean_Syntax_isOfKind(v___x_3514_, v___x_3516_);
lean_dec(v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
lean_dec(v___x_3514_);
lean_dec(v_bang_3504_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_3518_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3518_;
}
else
{
lean_object* v_cfg_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_cfg_3519_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_2542_);
v___x_3520_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2530_);
lean_inc_ref(v___x_2529_);
lean_inc_ref(v___x_2528_);
v___x_3521_ = l_Lean_Name_mkStr4(v___x_2528_, v___x_2529_, v___x_2530_, v___x_3520_);
lean_inc(v_cfg_3519_);
v___x_3522_ = l_Lean_Syntax_isOfKind(v_cfg_3519_, v___x_3521_);
lean_dec(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v_cfg_3519_);
lean_dec(v___x_3514_);
lean_dec(v_bang_3504_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_3523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3524_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_3473_);
v___x_3525_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_3513_);
v___x_3526_ = l_Lean_Syntax_isNone(v___x_3525_);
if (v___x_3526_ == 0)
{
uint8_t v___x_3527_; 
lean_inc(v___x_3525_);
v___x_3527_ = l_Lean_Syntax_matchesNull(v___x_3525_, v___x_3473_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_dec(v___x_3525_);
lean_dec(v___x_3524_);
lean_dec(v_cfg_3519_);
lean_dec(v___x_3514_);
lean_dec(v_bang_3504_);
lean_dec(v_tk_2543_);
lean_dec_ref(v___f_2531_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_3528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3528_;
}
else
{
lean_object* v_o_3529_; lean_object* v___x_3530_; 
v_o_3529_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_2542_);
lean_dec(v___x_3525_);
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_o_3529_);
v___y_3475_ = v_cfg_3519_;
v___y_3476_ = v___x_3514_;
v___y_3477_ = v_bang_3504_;
v___y_3478_ = v___x_3524_;
v___y_3479_ = v___x_3517_;
v_o_3480_ = v___x_3530_;
v___y_3481_ = v___y_3505_;
v___y_3482_ = v___y_3506_;
v___y_3483_ = v___y_3507_;
v___y_3484_ = v___y_3508_;
v___y_3485_ = v___y_3509_;
v___y_3486_ = v___y_3510_;
v___y_3487_ = v___y_3511_;
v___y_3488_ = v___y_3512_;
goto v___jp_3474_;
}
}
else
{
lean_object* v___x_3531_; 
lean_dec(v___x_3525_);
v___x_3531_ = lean_box(0);
v___y_3475_ = v_cfg_3519_;
v___y_3476_ = v___x_3514_;
v___y_3477_ = v_bang_3504_;
v___y_3478_ = v___x_3524_;
v___y_3479_ = v___x_3517_;
v_o_3480_ = v___x_3531_;
v___y_3481_ = v___y_3505_;
v___y_3482_ = v___y_3506_;
v___y_3483_ = v___y_3507_;
v___y_3484_ = v___y_3508_;
v___y_3485_ = v___y_3509_;
v___y_3486_ = v___y_3510_;
v___y_3487_ = v___y_3511_;
v___y_3488_ = v___y_3512_;
goto v___jp_3474_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3539_, lean_object* v_stx_3540_, lean_object* v___x_3541_, lean_object* v___x_3542_, lean_object* v___x_3543_, lean_object* v___x_3544_, lean_object* v___f_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
uint8_t v___x_31073__boxed_3555_; uint8_t v___x_31074__boxed_3556_; lean_object* v_res_3557_; 
v___x_31073__boxed_3555_ = lean_unbox(v___x_3539_);
v___x_31074__boxed_3556_ = lean_unbox(v___x_3541_);
v_res_3557_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31073__boxed_3555_, v_stx_3540_, v___x_31074__boxed_3556_, v___x_3542_, v___x_3543_, v___x_3544_, v___f_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v_stx_3540_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; uint8_t v___x_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___y_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3577_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3564_);
v___x_3578_ = l_Lean_Syntax_isOfKind(v_stx_3564_, v___x_3577_);
v___x_3579_ = 1;
v___f_3580_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3581_ = lean_box(v___x_3578_);
v___x_3582_ = lean_box(v___x_3579_);
v___y_3583_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3583_, 0, v___x_3581_);
lean_closure_set(v___y_3583_, 1, v_stx_3564_);
lean_closure_set(v___y_3583_, 2, v___x_3582_);
lean_closure_set(v___y_3583_, 3, v___x_3574_);
lean_closure_set(v___y_3583_, 4, v___x_3575_);
lean_closure_set(v___y_3583_, 5, v___x_3576_);
lean_closure_set(v___y_3583_, 6, v___f_3580_);
v___x_3584_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3584_, 0, v___y_3583_);
v___x_3585_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3584_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3597_, lean_object* v_as_3598_, lean_object* v_as_x27_3599_, lean_object* v_b_3600_, lean_object* v_a_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3597_, v_as_x27_3599_, v_b_3600_, v___y_3608_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3612_, lean_object* v_as_3613_, lean_object* v_as_x27_3614_, lean_object* v_b_3615_, lean_object* v_a_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3612_, v_as_3613_, v_as_x27_3614_, v_b_3615_, v_a_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v_as_x27_3614_);
lean_dec(v_as_3613_);
lean_dec(v___x_3612_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3634_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3635_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3637_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3638_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3634_, v___x_3635_, v___x_3636_, v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3667_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3668_ = l_Lean_addBuiltinDeclarationRanges(v___x_3666_, v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3671_, lean_object* v_simprocs_3672_, lean_object* v_fvarIdsToSimp_3673_, uint8_t v_simplifyTarget_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3681_, 1);
v___x_3683_ = lean_unsigned_to_nat(32u);
v___x_3684_ = lean_mk_empty_array_with_capacity(v___x_3683_);
lean_dec_ref(v___x_3684_);
v___x_3685_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3686_ = l_Lean_Meta_dsimpGoal(v_a_3682_, v_ctx_3671_, v_simprocs_3672_, v_simplifyTarget_3674_, v_fvarIdsToSimp_3673_, v___x_3685_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_fst_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v_fst_3688_ = lean_ctor_get(v_a_3687_, 0);
if (lean_obj_tag(v_fst_3688_) == 0)
{
lean_object* v_snd_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_snd_3689_ = lean_ctor_get(v_a_3687_, 1);
lean_inc(v_snd_3689_);
lean_dec(v_a_3687_);
v___x_3690_ = lean_box(0);
v___x_3691_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3690_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; 
v_unused_3699_ = lean_ctor_get(v___x_3691_, 0);
lean_dec(v_unused_3699_);
v___x_3693_ = v___x_3691_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_dec(v___x_3691_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v_snd_3689_);
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_snd_3689_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_snd_3689_);
v_a_3700_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3691_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3691_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_snd_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3734_; 
lean_inc_ref(v_fst_3688_);
v_snd_3708_ = lean_ctor_get(v_a_3687_, 1);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_a_3687_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v_a_3687_, 0);
lean_dec(v_unused_3735_);
v___x_3710_ = v_a_3687_;
v_isShared_3711_ = v_isSharedCheck_3734_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_snd_3708_);
lean_dec(v_a_3687_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3734_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_val_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
v_val_3712_ = lean_ctor_get(v_fst_3688_, 0);
lean_inc(v_val_3712_);
lean_dec_ref_known(v_fst_3688_, 1);
v___x_3713_ = lean_box(0);
if (v_isShared_3711_ == 0)
{
lean_ctor_set_tag(v___x_3710_, 1);
lean_ctor_set(v___x_3710_, 1, v___x_3713_);
lean_ctor_set(v___x_3710_, 0, v_val_3712_);
v___x_3715_ = v___x_3710_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_val_3712_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3715_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3723_ == 0)
{
lean_object* v_unused_3724_; 
v_unused_3724_ = lean_ctor_get(v___x_3716_, 0);
lean_dec(v_unused_3724_);
v___x_3718_ = v___x_3716_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_dec(v___x_3716_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v_snd_3708_);
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_snd_3708_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_snd_3708_);
v_a_3725_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3716_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3716_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
v_a_3736_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3686_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3686_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v_fvarIdsToSimp_3673_);
lean_dec_ref(v_simprocs_3672_);
lean_dec_ref(v_ctx_3671_);
v_a_3744_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3681_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3681_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3752_, lean_object* v_simprocs_3753_, lean_object* v_fvarIdsToSimp_3754_, lean_object* v_simplifyTarget_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
uint8_t v_simplifyTarget_boxed_3762_; lean_object* v_res_3763_; 
v_simplifyTarget_boxed_3762_ = lean_unbox(v_simplifyTarget_3755_);
v_res_3763_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3752_, v_simprocs_3753_, v_fvarIdsToSimp_3754_, v_simplifyTarget_boxed_3762_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3764_, lean_object* v_simprocs_3765_, lean_object* v_fvarIdsToSimp_3766_, uint8_t v_simplifyTarget_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3764_, v_simprocs_3765_, v_fvarIdsToSimp_3766_, v_simplifyTarget_3767_, v_a_3769_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3778_, lean_object* v_simprocs_3779_, lean_object* v_fvarIdsToSimp_3780_, lean_object* v_simplifyTarget_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
uint8_t v_simplifyTarget_boxed_3791_; lean_object* v_res_3792_; 
v_simplifyTarget_boxed_3791_ = lean_unbox(v_simplifyTarget_3781_);
v_res_3792_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3778_, v_simprocs_3779_, v_fvarIdsToSimp_3780_, v_simplifyTarget_boxed_3791_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3793_, lean_object* v_simprocs_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3796_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___x_3806_ = l_Lean_MVarId_getNondepPropHyps(v_a_3805_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; uint8_t v___x_3808_; lean_object* v___x_3809_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___x_3808_ = 1;
v___x_3809_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3793_, v_simprocs_3794_, v_a_3807_, v___x_3808_, v___y_3796_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3809_;
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v_simprocs_3794_);
lean_dec_ref(v_ctx_3793_);
v_a_3810_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3806_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3806_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v_simprocs_3794_);
lean_dec_ref(v_ctx_3793_);
v_a_3818_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3804_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3804_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3826_, lean_object* v_simprocs_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3826_, v_simprocs_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3838_, lean_object* v_ctx_3839_, lean_object* v_simprocs_3840_, uint8_t v_type_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3838_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3839_, v_simprocs_3840_, v_a_3852_, v_type_3841_, v___y_3843_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3853_;
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref(v_simprocs_3840_);
lean_dec_ref(v_ctx_3839_);
v_a_3854_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3851_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3851_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3862_, lean_object* v_ctx_3863_, lean_object* v_simprocs_3864_, lean_object* v_type_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
uint8_t v_type_555__boxed_3875_; lean_object* v_res_3876_; 
v_type_555__boxed_3875_ = lean_unbox(v_type_3865_);
v_res_3876_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3862_, v_ctx_3863_, v_simprocs_3864_, v_type_555__boxed_3875_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3877_, lean_object* v_simprocs_3878_, lean_object* v_loc_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_){
_start:
{
if (lean_obj_tag(v_loc_3879_) == 0)
{
lean_object* v___f_3889_; lean_object* v___x_3890_; 
v___f_3889_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3889_, 0, v_ctx_3877_);
lean_closure_set(v___f_3889_, 1, v_simprocs_3878_);
v___x_3890_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3889_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
return v___x_3890_;
}
else
{
lean_object* v_hypotheses_3891_; uint8_t v_type_3892_; lean_object* v___x_3893_; lean_object* v___f_3894_; lean_object* v___x_3895_; 
v_hypotheses_3891_ = lean_ctor_get(v_loc_3879_, 0);
lean_inc_ref(v_hypotheses_3891_);
v_type_3892_ = lean_ctor_get_uint8(v_loc_3879_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3879_, 1);
v___x_3893_ = lean_box(v_type_3892_);
v___f_3894_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3894_, 0, v_hypotheses_3891_);
lean_closure_set(v___f_3894_, 1, v_ctx_3877_);
lean_closure_set(v___f_3894_, 2, v_simprocs_3878_);
lean_closure_set(v___f_3894_, 3, v___x_3893_);
v___x_3895_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3894_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
return v___x_3895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3896_, lean_object* v_simprocs_3897_, lean_object* v_loc_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3896_, v_simprocs_3897_, v_loc_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3913_, lean_object* v_stx_3914_, uint8_t v___x_3915_, lean_object* v___x_3916_, lean_object* v___x_3917_, lean_object* v___x_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
if (v___x_3913_ == 0)
{
lean_object* v___x_3928_; 
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_3928_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3928_;
}
else
{
lean_object* v___x_3929_; lean_object* v_tk_3930_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; uint8_t v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v_stx_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; uint8_t v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; uint8_t v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; uint8_t v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; uint8_t v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; uint8_t v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; uint8_t v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; uint8_t v___y_4235_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; uint8_t v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4285_; lean_object* v___y_4286_; uint8_t v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v_args_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___x_4311_; lean_object* v___y_4313_; uint8_t v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v_o_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v_bang_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
v___x_3929_ = lean_unsigned_to_nat(0u);
v_tk_3930_ = l_Lean_Syntax_getArg(v_stx_3914_, v___x_3929_);
v___x_4311_ = lean_unsigned_to_nat(1u);
v___x_4368_ = l_Lean_Syntax_getArg(v_stx_3914_, v___x_4311_);
v___x_4369_ = l_Lean_Syntax_isNone(v___x_4368_);
if (v___x_4369_ == 0)
{
uint8_t v___x_4370_; 
lean_inc(v___x_4368_);
v___x_4370_ = l_Lean_Syntax_matchesNull(v___x_4368_, v___x_4311_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4371_; 
lean_dec(v___x_4368_);
lean_dec(v_tk_3930_);
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_4371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4371_;
}
else
{
lean_object* v_bang_4372_; lean_object* v___x_4373_; 
v_bang_4372_ = l_Lean_Syntax_getArg(v___x_4368_, v___x_3929_);
lean_dec(v___x_4368_);
v___x_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4373_, 0, v_bang_4372_);
v_bang_4341_ = v___x_4373_;
v___y_4342_ = v___y_3919_;
v___y_4343_ = v___y_3920_;
v___y_4344_ = v___y_3921_;
v___y_4345_ = v___y_3922_;
v___y_4346_ = v___y_3923_;
v___y_4347_ = v___y_3924_;
v___y_4348_ = v___y_3925_;
v___y_4349_ = v___y_3926_;
goto v___jp_4340_;
}
}
else
{
lean_object* v___x_4374_; 
lean_dec(v___x_4368_);
v___x_4374_ = lean_box(0);
v_bang_4341_ = v___x_4374_;
v___y_4342_ = v___y_3919_;
v___y_4343_ = v___y_3920_;
v___y_4344_ = v___y_3921_;
v___y_4345_ = v___y_3922_;
v___y_4346_ = v___y_3923_;
v___y_4347_ = v___y_3924_;
v___y_4348_ = v___y_3925_;
v___y_4349_ = v___y_3926_;
goto v___jp_4340_;
}
v___jp_3931_:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3935_, v___y_3940_, v___y_3943_, v___y_3942_, v___y_3938_, v___y_3937_, v___y_3941_, v___y_3936_, v___y_3933_, v___y_3932_, v___y_3939_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v_usedTheorems_3946_; lean_object* v_diag_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3989_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref_known(v___x_3944_, 1);
v_usedTheorems_3946_ = lean_ctor_get(v_a_3945_, 0);
v_diag_3947_ = lean_ctor_get(v_a_3945_, 1);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_a_3945_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3949_ = v_a_3945_;
v_isShared_3950_ = v_isSharedCheck_3989_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_diag_3947_);
lean_inc(v_usedTheorems_3946_);
lean_dec(v_a_3945_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3989_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3934_, v_usedTheorems_3946_, v___y_3936_, v___y_3933_, v___y_3932_, v___y_3939_);
lean_dec_ref(v_usedTheorems_3946_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v_ref_3953_; lean_object* v___x_3954_; lean_object* v___x_3956_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v_ref_3953_ = lean_ctor_get(v___y_3932_, 2);
v___x_3954_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 1, v_a_3952_);
lean_ctor_set(v___x_3949_, 0, v___x_3954_);
v___x_3956_ = v___x_3949_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_a_3952_);
v___x_3956_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3957_ = lean_box(0);
v___x_3958_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
lean_ctor_set(v___x_3958_, 3, v___x_3957_);
lean_ctor_set(v___x_3958_, 4, v___x_3957_);
lean_ctor_set(v___x_3958_, 5, v___x_3957_);
lean_inc(v_ref_3953_);
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v_ref_3953_);
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3961_ = 4;
v___x_3962_ = l_Lean_MessageData_nil;
v___x_3963_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3930_, v___x_3958_, v___x_3959_, v___x_3960_, v___x_3957_, v___x_3961_, v___x_3962_, v___y_3932_, v___y_3939_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; 
v_unused_3971_ = lean_ctor_get(v___x_3963_, 0);
lean_dec(v_unused_3971_);
v___x_3965_ = v___x_3963_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_dec(v___x_3963_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 0, v_diag_3947_);
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_diag_3947_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec_ref(v_diag_3947_);
v_a_3972_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3963_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3963_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_del_object(v___x_3949_);
lean_dec_ref(v_diag_3947_);
lean_dec(v_tk_3930_);
v_a_3981_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3951_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3951_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v___y_3934_);
lean_dec(v_tk_3930_);
v_a_3990_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3944_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3944_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
v___jp_3998_:
{
if (lean_obj_tag(v___y_4002_) == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4012_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
lean_ctor_set_uint8(v___x_4012_, sizeof(void*)*1, v___x_3915_);
v___y_3932_ = v___y_4000_;
v___y_3933_ = v___y_3999_;
v___y_3934_ = v___y_4001_;
v___y_3935_ = v___y_4010_;
v___y_3936_ = v___y_4003_;
v___y_3937_ = v___y_4004_;
v___y_3938_ = v___y_4005_;
v___y_3939_ = v___y_4007_;
v___y_3940_ = v___y_4006_;
v___y_3941_ = v___y_4009_;
v___y_3942_ = v___y_4008_;
v___y_3943_ = v___x_4012_;
goto v___jp_3931_;
}
else
{
lean_object* v_val_4013_; lean_object* v___x_4014_; 
v_val_4013_ = lean_ctor_get(v___y_4002_, 0);
lean_inc(v_val_4013_);
lean_dec_ref_known(v___y_4002_, 1);
v___x_4014_ = l_Lean_Elab_Tactic_expandLocation(v_val_4013_);
lean_dec(v_val_4013_);
v___y_3932_ = v___y_4000_;
v___y_3933_ = v___y_3999_;
v___y_3934_ = v___y_4001_;
v___y_3935_ = v___y_4010_;
v___y_3936_ = v___y_4003_;
v___y_3937_ = v___y_4004_;
v___y_3938_ = v___y_4005_;
v___y_3939_ = v___y_4007_;
v___y_3940_ = v___y_4006_;
v___y_3941_ = v___y_4009_;
v___y_3942_ = v___y_4008_;
v___y_3943_ = v___x_4014_;
goto v___jp_3931_;
}
}
v___jp_4015_:
{
uint8_t v___x_4028_; uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4028_ = 0;
v___x_4029_ = 2;
v___x_4030_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4031_ = lean_box(v___x_4028_);
v___x_4032_ = lean_box(v___x_4029_);
v___x_4033_ = lean_box(v___x_4028_);
lean_inc(v_stx_4019_);
v___x_4034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4034_, 0, v_stx_4019_);
lean_closure_set(v___x_4034_, 1, v___x_4031_);
lean_closure_set(v___x_4034_, 2, v___x_4032_);
lean_closure_set(v___x_4034_, 3, v___x_4033_);
lean_closure_set(v___x_4034_, 4, v___x_4030_);
v___x_4035_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4034_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
if (lean_obj_tag(v___y_4018_) == 0)
{
lean_object* v_ctx_4037_; lean_object* v_simprocs_4038_; 
v_ctx_4037_ = lean_ctor_get(v_a_4036_, 0);
lean_inc_ref(v_ctx_4037_);
v_simprocs_4038_ = lean_ctor_get(v_a_4036_, 1);
lean_inc_ref(v_simprocs_4038_);
lean_dec(v_a_4036_);
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4026_;
v___y_4001_ = v_stx_4019_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4024_;
v___y_4004_ = v___y_4022_;
v___y_4005_ = v___y_4021_;
v___y_4006_ = v_simprocs_4038_;
v___y_4007_ = v___y_4027_;
v___y_4008_ = v___y_4020_;
v___y_4009_ = v___y_4023_;
v___y_4010_ = v_ctx_4037_;
goto v___jp_3998_;
}
else
{
lean_dec_ref_known(v___y_4018_, 1);
if (v___y_4016_ == 0)
{
lean_object* v_ctx_4039_; lean_object* v_simprocs_4040_; 
v_ctx_4039_ = lean_ctor_get(v_a_4036_, 0);
lean_inc_ref(v_ctx_4039_);
v_simprocs_4040_ = lean_ctor_get(v_a_4036_, 1);
lean_inc_ref(v_simprocs_4040_);
lean_dec(v_a_4036_);
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4026_;
v___y_4001_ = v_stx_4019_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4024_;
v___y_4004_ = v___y_4022_;
v___y_4005_ = v___y_4021_;
v___y_4006_ = v_simprocs_4040_;
v___y_4007_ = v___y_4027_;
v___y_4008_ = v___y_4020_;
v___y_4009_ = v___y_4023_;
v___y_4010_ = v_ctx_4039_;
goto v___jp_3998_;
}
else
{
lean_object* v_ctx_4041_; lean_object* v_simprocs_4042_; lean_object* v___x_4043_; 
v_ctx_4041_ = lean_ctor_get(v_a_4036_, 0);
lean_inc_ref(v_ctx_4041_);
v_simprocs_4042_ = lean_ctor_get(v_a_4036_, 1);
lean_inc_ref(v_simprocs_4042_);
lean_dec(v_a_4036_);
v___x_4043_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4041_);
v___y_3999_ = v___y_4025_;
v___y_4000_ = v___y_4026_;
v___y_4001_ = v_stx_4019_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4024_;
v___y_4004_ = v___y_4022_;
v___y_4005_ = v___y_4021_;
v___y_4006_ = v_simprocs_4042_;
v___y_4007_ = v___y_4027_;
v___y_4008_ = v___y_4020_;
v___y_4009_ = v___y_4023_;
v___y_4010_ = v___x_4043_;
goto v___jp_3998_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_stx_4019_);
lean_dec(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec(v_tk_3930_);
v_a_4044_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4035_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4035_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
v___jp_4052_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_inc_ref(v___y_4072_);
v___x_4074_ = l_Array_append___redArg(v___y_4072_, v___y_4073_);
lean_dec_ref(v___y_4073_);
lean_inc(v___y_4067_);
lean_inc(v___y_4059_);
v___x_4075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4075_, 0, v___y_4059_);
lean_ctor_set(v___x_4075_, 1, v___y_4067_);
lean_ctor_set(v___x_4075_, 2, v___x_4074_);
v___x_4076_ = l_Lean_Syntax_node6(v___y_4059_, v___y_4070_, v___y_4064_, v___y_4056_, v___y_4053_, v___y_4071_, v___y_4062_, v___x_4075_);
v___y_4016_ = v___y_4057_;
v___y_4017_ = v___y_4069_;
v___y_4018_ = v___y_4058_;
v_stx_4019_ = v___x_4076_;
v___y_4020_ = v___y_4060_;
v___y_4021_ = v___y_4054_;
v___y_4022_ = v___y_4068_;
v___y_4023_ = v___y_4066_;
v___y_4024_ = v___y_4061_;
v___y_4025_ = v___y_4063_;
v___y_4026_ = v___y_4065_;
v___y_4027_ = v___y_4055_;
goto v___jp_4015_;
}
v___jp_4077_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_inc_ref(v___y_4096_);
v___x_4098_ = l_Array_append___redArg(v___y_4096_, v___y_4097_);
lean_dec_ref(v___y_4097_);
lean_inc(v___y_4092_);
lean_inc(v___y_4083_);
v___x_4099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4083_);
lean_ctor_set(v___x_4099_, 1, v___y_4092_);
lean_ctor_set(v___x_4099_, 2, v___x_4098_);
if (lean_obj_tag(v___y_4093_) == 0)
{
lean_object* v___x_4100_; 
v___x_4100_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4079_;
v___y_4055_ = v___y_4080_;
v___y_4056_ = v___y_4081_;
v___y_4057_ = v___y_4082_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4083_;
v___y_4060_ = v___y_4085_;
v___y_4061_ = v___y_4086_;
v___y_4062_ = v___x_4099_;
v___y_4063_ = v___y_4087_;
v___y_4064_ = v___y_4088_;
v___y_4065_ = v___y_4089_;
v___y_4066_ = v___y_4090_;
v___y_4067_ = v___y_4092_;
v___y_4068_ = v___y_4091_;
v___y_4069_ = v___y_4093_;
v___y_4070_ = v___y_4094_;
v___y_4071_ = v___y_4095_;
v___y_4072_ = v___y_4096_;
v___y_4073_ = v___x_4100_;
goto v___jp_4052_;
}
else
{
lean_object* v_val_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v_val_4101_ = lean_ctor_get(v___y_4093_, 0);
v___x_4102_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4101_);
v___x_4103_ = lean_array_push(v___x_4102_, v_val_4101_);
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4079_;
v___y_4055_ = v___y_4080_;
v___y_4056_ = v___y_4081_;
v___y_4057_ = v___y_4082_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4083_;
v___y_4060_ = v___y_4085_;
v___y_4061_ = v___y_4086_;
v___y_4062_ = v___x_4099_;
v___y_4063_ = v___y_4087_;
v___y_4064_ = v___y_4088_;
v___y_4065_ = v___y_4089_;
v___y_4066_ = v___y_4090_;
v___y_4067_ = v___y_4092_;
v___y_4068_ = v___y_4091_;
v___y_4069_ = v___y_4093_;
v___y_4070_ = v___y_4094_;
v___y_4071_ = v___y_4095_;
v___y_4072_ = v___y_4096_;
v___y_4073_ = v___x_4103_;
goto v___jp_4052_;
}
}
v___jp_4104_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_inc_ref(v___y_4123_);
v___x_4125_ = l_Array_append___redArg(v___y_4123_, v___y_4124_);
lean_dec_ref(v___y_4124_);
lean_inc(v___y_4120_);
lean_inc(v___y_4111_);
v___x_4126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4126_, 0, v___y_4111_);
lean_ctor_set(v___x_4126_, 1, v___y_4120_);
lean_ctor_set(v___x_4126_, 2, v___x_4125_);
if (lean_obj_tag(v___y_4110_) == 1)
{
lean_object* v_val_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_val_4127_ = lean_ctor_get(v___y_4110_, 0);
lean_inc(v_val_4127_);
lean_dec_ref_known(v___y_4110_, 1);
v___x_4128_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4111_, 3);
v___x_4129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___y_4111_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
lean_inc_ref(v___y_4123_);
v___x_4130_ = l_Array_append___redArg(v___y_4123_, v_val_4127_);
lean_dec(v_val_4127_);
lean_inc(v___y_4120_);
v___x_4131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4131_, 0, v___y_4111_);
lean_ctor_set(v___x_4131_, 1, v___y_4120_);
lean_ctor_set(v___x_4131_, 2, v___x_4130_);
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___y_4111_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
v___x_4134_ = l_Array_mkArray3___redArg(v___x_4129_, v___x_4131_, v___x_4133_);
v___y_4078_ = v___y_4105_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4107_;
v___y_4081_ = v___y_4108_;
v___y_4082_ = v___y_4109_;
v___y_4083_ = v___y_4111_;
v___y_4084_ = v___y_4112_;
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4114_;
v___y_4087_ = v___y_4115_;
v___y_4088_ = v___y_4116_;
v___y_4089_ = v___y_4117_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___x_4126_;
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___x_4134_;
goto v___jp_4077_;
}
else
{
lean_object* v___x_4135_; 
lean_dec(v___y_4110_);
v___x_4135_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4078_ = v___y_4105_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4107_;
v___y_4081_ = v___y_4108_;
v___y_4082_ = v___y_4109_;
v___y_4083_ = v___y_4111_;
v___y_4084_ = v___y_4112_;
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4114_;
v___y_4087_ = v___y_4115_;
v___y_4088_ = v___y_4116_;
v___y_4089_ = v___y_4117_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___x_4126_;
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___x_4135_;
goto v___jp_4077_;
}
}
v___jp_4136_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_inc_ref(v___y_4145_);
v___x_4158_ = l_Array_append___redArg(v___y_4145_, v___y_4157_);
lean_dec_ref(v___y_4157_);
lean_inc(v___y_4142_);
lean_inc(v___y_4150_);
v___x_4159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4159_, 0, v___y_4150_);
lean_ctor_set(v___x_4159_, 1, v___y_4142_);
lean_ctor_set(v___x_4159_, 2, v___x_4158_);
v___x_4160_ = l_Lean_Syntax_node6(v___y_4150_, v___y_4155_, v___y_4137_, v___y_4140_, v___y_4154_, v___y_4156_, v___y_4144_, v___x_4159_);
v___y_4016_ = v___y_4141_;
v___y_4017_ = v___y_4153_;
v___y_4018_ = v___y_4143_;
v_stx_4019_ = v___x_4160_;
v___y_4020_ = v___y_4146_;
v___y_4021_ = v___y_4138_;
v___y_4022_ = v___y_4152_;
v___y_4023_ = v___y_4151_;
v___y_4024_ = v___y_4147_;
v___y_4025_ = v___y_4148_;
v___y_4026_ = v___y_4149_;
v___y_4027_ = v___y_4139_;
goto v___jp_4015_;
}
v___jp_4161_:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_inc_ref(v___y_4169_);
v___x_4182_ = l_Array_append___redArg(v___y_4169_, v___y_4181_);
lean_dec_ref(v___y_4181_);
lean_inc(v___y_4167_);
lean_inc(v___y_4174_);
v___x_4183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4183_, 0, v___y_4174_);
lean_ctor_set(v___x_4183_, 1, v___y_4167_);
lean_ctor_set(v___x_4183_, 2, v___x_4182_);
if (lean_obj_tag(v___y_4177_) == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4137_ = v___y_4162_;
v___y_4138_ = v___y_4163_;
v___y_4139_ = v___y_4164_;
v___y_4140_ = v___y_4165_;
v___y_4141_ = v___y_4166_;
v___y_4142_ = v___y_4167_;
v___y_4143_ = v___y_4168_;
v___y_4144_ = v___x_4183_;
v___y_4145_ = v___y_4169_;
v___y_4146_ = v___y_4170_;
v___y_4147_ = v___y_4171_;
v___y_4148_ = v___y_4172_;
v___y_4149_ = v___y_4173_;
v___y_4150_ = v___y_4174_;
v___y_4151_ = v___y_4175_;
v___y_4152_ = v___y_4176_;
v___y_4153_ = v___y_4177_;
v___y_4154_ = v___y_4178_;
v___y_4155_ = v___y_4180_;
v___y_4156_ = v___y_4179_;
v___y_4157_ = v___x_4184_;
goto v___jp_4136_;
}
else
{
lean_object* v_val_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_val_4185_ = lean_ctor_get(v___y_4177_, 0);
v___x_4186_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4185_);
v___x_4187_ = lean_array_push(v___x_4186_, v_val_4185_);
v___y_4137_ = v___y_4162_;
v___y_4138_ = v___y_4163_;
v___y_4139_ = v___y_4164_;
v___y_4140_ = v___y_4165_;
v___y_4141_ = v___y_4166_;
v___y_4142_ = v___y_4167_;
v___y_4143_ = v___y_4168_;
v___y_4144_ = v___x_4183_;
v___y_4145_ = v___y_4169_;
v___y_4146_ = v___y_4170_;
v___y_4147_ = v___y_4171_;
v___y_4148_ = v___y_4172_;
v___y_4149_ = v___y_4173_;
v___y_4150_ = v___y_4174_;
v___y_4151_ = v___y_4175_;
v___y_4152_ = v___y_4176_;
v___y_4153_ = v___y_4177_;
v___y_4154_ = v___y_4178_;
v___y_4155_ = v___y_4180_;
v___y_4156_ = v___y_4179_;
v___y_4157_ = v___x_4187_;
goto v___jp_4136_;
}
}
v___jp_4188_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_inc_ref(v___y_4197_);
v___x_4209_ = l_Array_append___redArg(v___y_4197_, v___y_4208_);
lean_dec_ref(v___y_4208_);
lean_inc(v___y_4194_);
lean_inc(v___y_4202_);
v___x_4210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4210_, 0, v___y_4202_);
lean_ctor_set(v___x_4210_, 1, v___y_4194_);
lean_ctor_set(v___x_4210_, 2, v___x_4209_);
if (lean_obj_tag(v___y_4195_) == 1)
{
lean_object* v_val_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v_val_4211_ = lean_ctor_get(v___y_4195_, 0);
lean_inc(v_val_4211_);
lean_dec_ref_known(v___y_4195_, 1);
v___x_4212_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4202_, 3);
v___x_4213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___y_4202_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
lean_inc_ref(v___y_4197_);
v___x_4214_ = l_Array_append___redArg(v___y_4197_, v_val_4211_);
lean_dec(v_val_4211_);
lean_inc(v___y_4194_);
v___x_4215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4215_, 0, v___y_4202_);
lean_ctor_set(v___x_4215_, 1, v___y_4194_);
lean_ctor_set(v___x_4215_, 2, v___x_4214_);
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___y_4202_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = l_Array_mkArray3___redArg(v___x_4213_, v___x_4215_, v___x_4217_);
v___y_4162_ = v___y_4189_;
v___y_4163_ = v___y_4190_;
v___y_4164_ = v___y_4191_;
v___y_4165_ = v___y_4192_;
v___y_4166_ = v___y_4193_;
v___y_4167_ = v___y_4194_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4197_;
v___y_4170_ = v___y_4198_;
v___y_4171_ = v___y_4199_;
v___y_4172_ = v___y_4200_;
v___y_4173_ = v___y_4201_;
v___y_4174_ = v___y_4202_;
v___y_4175_ = v___y_4203_;
v___y_4176_ = v___y_4204_;
v___y_4177_ = v___y_4205_;
v___y_4178_ = v___y_4206_;
v___y_4179_ = v___x_4210_;
v___y_4180_ = v___y_4207_;
v___y_4181_ = v___x_4218_;
goto v___jp_4161_;
}
else
{
lean_object* v___x_4219_; 
lean_dec(v___y_4195_);
v___x_4219_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4162_ = v___y_4189_;
v___y_4163_ = v___y_4190_;
v___y_4164_ = v___y_4191_;
v___y_4165_ = v___y_4192_;
v___y_4166_ = v___y_4193_;
v___y_4167_ = v___y_4194_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4197_;
v___y_4170_ = v___y_4198_;
v___y_4171_ = v___y_4199_;
v___y_4172_ = v___y_4200_;
v___y_4173_ = v___y_4201_;
v___y_4174_ = v___y_4202_;
v___y_4175_ = v___y_4203_;
v___y_4176_ = v___y_4204_;
v___y_4177_ = v___y_4205_;
v___y_4178_ = v___y_4206_;
v___y_4179_ = v___x_4210_;
v___y_4180_ = v___y_4207_;
v___y_4181_ = v___x_4219_;
goto v___jp_4161_;
}
}
v___jp_4220_:
{
lean_object* v_ref_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v_ref_4236_ = lean_ctor_get(v___y_4230_, 2);
v___x_4237_ = l_Lean_SourceInfo_fromRef(v_ref_4236_, v___y_4235_);
v___x_4238_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4239_ = l_Lean_Name_mkStr4(v___x_3916_, v___x_3917_, v___x_3918_, v___x_4238_);
v___x_4240_ = l_Lean_SourceInfo_fromRef(v_tk_3930_, v___x_3915_);
v___x_4241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
lean_ctor_set(v___x_4241_, 1, v___x_4238_);
v___x_4242_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4243_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4237_);
v___x_4244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4237_);
lean_ctor_set(v___x_4244_, 1, v___x_4242_);
lean_ctor_set(v___x_4244_, 2, v___x_4243_);
if (lean_obj_tag(v___y_4232_) == 1)
{
lean_object* v_val_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_val_4245_ = lean_ctor_get(v___y_4232_, 0);
lean_inc(v_val_4245_);
lean_dec_ref_known(v___y_4232_, 1);
v___x_4246_ = l_Lean_SourceInfo_fromRef(v_val_4245_, v___x_3915_);
lean_dec(v_val_4245_);
v___x_4247_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = l_Array_mkArray1___redArg(v___x_4248_);
v___y_4105_ = v___x_4244_;
v___y_4106_ = v___y_4221_;
v___y_4107_ = v___y_4222_;
v___y_4108_ = v___y_4223_;
v___y_4109_ = v___y_4224_;
v___y_4110_ = v___y_4225_;
v___y_4111_ = v___x_4237_;
v___y_4112_ = v___y_4226_;
v___y_4113_ = v___y_4227_;
v___y_4114_ = v___y_4228_;
v___y_4115_ = v___y_4229_;
v___y_4116_ = v___x_4241_;
v___y_4117_ = v___y_4230_;
v___y_4118_ = v___y_4231_;
v___y_4119_ = v___y_4233_;
v___y_4120_ = v___x_4242_;
v___y_4121_ = v___y_4234_;
v___y_4122_ = v___x_4239_;
v___y_4123_ = v___x_4243_;
v___y_4124_ = v___x_4249_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4250_; 
lean_dec(v___y_4232_);
v___x_4250_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4105_ = v___x_4244_;
v___y_4106_ = v___y_4221_;
v___y_4107_ = v___y_4222_;
v___y_4108_ = v___y_4223_;
v___y_4109_ = v___y_4224_;
v___y_4110_ = v___y_4225_;
v___y_4111_ = v___x_4237_;
v___y_4112_ = v___y_4226_;
v___y_4113_ = v___y_4227_;
v___y_4114_ = v___y_4228_;
v___y_4115_ = v___y_4229_;
v___y_4116_ = v___x_4241_;
v___y_4117_ = v___y_4230_;
v___y_4118_ = v___y_4231_;
v___y_4119_ = v___y_4233_;
v___y_4120_ = v___x_4242_;
v___y_4121_ = v___y_4234_;
v___y_4122_ = v___x_4239_;
v___y_4123_ = v___x_4243_;
v___y_4124_ = v___x_4250_;
goto v___jp_4104_;
}
}
v___jp_4251_:
{
if (lean_obj_tag(v___y_4257_) == 0)
{
uint8_t v___x_4266_; 
v___x_4266_ = 0;
v___y_4221_ = v___y_4252_;
v___y_4222_ = v___y_4253_;
v___y_4223_ = v___y_4254_;
v___y_4224_ = v___y_4255_;
v___y_4225_ = v___y_4256_;
v___y_4226_ = v___y_4257_;
v___y_4227_ = v___y_4258_;
v___y_4228_ = v___y_4259_;
v___y_4229_ = v___y_4260_;
v___y_4230_ = v___y_4261_;
v___y_4231_ = v___y_4262_;
v___y_4232_ = v___y_4263_;
v___y_4233_ = v___y_4264_;
v___y_4234_ = v___y_4265_;
v___y_4235_ = v___x_4266_;
goto v___jp_4220_;
}
else
{
if (v___y_4255_ == 0)
{
v___y_4221_ = v___y_4252_;
v___y_4222_ = v___y_4253_;
v___y_4223_ = v___y_4254_;
v___y_4224_ = v___y_4255_;
v___y_4225_ = v___y_4256_;
v___y_4226_ = v___y_4257_;
v___y_4227_ = v___y_4258_;
v___y_4228_ = v___y_4259_;
v___y_4229_ = v___y_4260_;
v___y_4230_ = v___y_4261_;
v___y_4231_ = v___y_4262_;
v___y_4232_ = v___y_4263_;
v___y_4233_ = v___y_4264_;
v___y_4234_ = v___y_4265_;
v___y_4235_ = v___y_4255_;
goto v___jp_4220_;
}
else
{
lean_object* v_ref_4267_; uint8_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_ref_4267_ = lean_ctor_get(v___y_4261_, 2);
v___x_4268_ = 0;
v___x_4269_ = l_Lean_SourceInfo_fromRef(v_ref_4267_, v___x_4268_);
v___x_4270_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4271_ = l_Lean_Name_mkStr4(v___x_3916_, v___x_3917_, v___x_3918_, v___x_4270_);
v___x_4272_ = l_Lean_SourceInfo_fromRef(v_tk_3930_, v___x_3915_);
v___x_4273_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4276_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4269_);
v___x_4277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4269_);
lean_ctor_set(v___x_4277_, 1, v___x_4275_);
lean_ctor_set(v___x_4277_, 2, v___x_4276_);
if (lean_obj_tag(v___y_4263_) == 1)
{
lean_object* v_val_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v_val_4278_ = lean_ctor_get(v___y_4263_, 0);
lean_inc(v_val_4278_);
lean_dec_ref_known(v___y_4263_, 1);
v___x_4279_ = l_Lean_SourceInfo_fromRef(v_val_4278_, v___x_3915_);
lean_dec(v_val_4278_);
v___x_4280_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = l_Array_mkArray1___redArg(v___x_4281_);
v___y_4189_ = v___x_4274_;
v___y_4190_ = v___y_4252_;
v___y_4191_ = v___y_4253_;
v___y_4192_ = v___y_4254_;
v___y_4193_ = v___y_4255_;
v___y_4194_ = v___x_4275_;
v___y_4195_ = v___y_4256_;
v___y_4196_ = v___y_4257_;
v___y_4197_ = v___x_4276_;
v___y_4198_ = v___y_4258_;
v___y_4199_ = v___y_4259_;
v___y_4200_ = v___y_4260_;
v___y_4201_ = v___y_4261_;
v___y_4202_ = v___x_4269_;
v___y_4203_ = v___y_4262_;
v___y_4204_ = v___y_4264_;
v___y_4205_ = v___y_4265_;
v___y_4206_ = v___x_4277_;
v___y_4207_ = v___x_4271_;
v___y_4208_ = v___x_4282_;
goto v___jp_4188_;
}
else
{
lean_object* v___x_4283_; 
lean_dec(v___y_4263_);
v___x_4283_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4189_ = v___x_4274_;
v___y_4190_ = v___y_4252_;
v___y_4191_ = v___y_4253_;
v___y_4192_ = v___y_4254_;
v___y_4193_ = v___y_4255_;
v___y_4194_ = v___x_4275_;
v___y_4195_ = v___y_4256_;
v___y_4196_ = v___y_4257_;
v___y_4197_ = v___x_4276_;
v___y_4198_ = v___y_4258_;
v___y_4199_ = v___y_4259_;
v___y_4200_ = v___y_4260_;
v___y_4201_ = v___y_4261_;
v___y_4202_ = v___x_4269_;
v___y_4203_ = v___y_4262_;
v___y_4204_ = v___y_4264_;
v___y_4205_ = v___y_4265_;
v___y_4206_ = v___x_4277_;
v___y_4207_ = v___x_4271_;
v___y_4208_ = v___x_4283_;
goto v___jp_4188_;
}
}
}
}
v___jp_4284_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_unsigned_to_nat(3u);
v___x_4300_ = l_Lean_Syntax_getArg(v___y_4288_, v___x_4299_);
lean_dec(v___y_4288_);
v___x_4301_ = l_Lean_Syntax_getOptional_x3f(v___x_4300_);
lean_dec(v___x_4300_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_box(0);
v___y_4252_ = v___y_4292_;
v___y_4253_ = v___y_4298_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4287_;
v___y_4256_ = v_args_4290_;
v___y_4257_ = v___y_4289_;
v___y_4258_ = v___y_4291_;
v___y_4259_ = v___y_4295_;
v___y_4260_ = v___y_4296_;
v___y_4261_ = v___y_4297_;
v___y_4262_ = v___y_4294_;
v___y_4263_ = v___y_4286_;
v___y_4264_ = v___y_4293_;
v___y_4265_ = v___x_4302_;
goto v___jp_4251_;
}
else
{
lean_object* v_val_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
v_val_4303_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4301_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_val_4303_);
lean_dec(v___x_4301_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_val_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
v___y_4252_ = v___y_4292_;
v___y_4253_ = v___y_4298_;
v___y_4254_ = v___y_4285_;
v___y_4255_ = v___y_4287_;
v___y_4256_ = v_args_4290_;
v___y_4257_ = v___y_4289_;
v___y_4258_ = v___y_4291_;
v___y_4259_ = v___y_4295_;
v___y_4260_ = v___y_4296_;
v___y_4261_ = v___y_4297_;
v___y_4262_ = v___y_4294_;
v___y_4263_ = v___y_4286_;
v___y_4264_ = v___y_4293_;
v___y_4265_ = v___x_4308_;
goto v___jp_4251_;
}
}
}
}
v___jp_4312_:
{
lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4327_ = l_Lean_Syntax_getArg(v___y_4316_, v___y_4315_);
v___x_4328_ = l_Lean_Syntax_isNone(v___x_4327_);
if (v___x_4328_ == 0)
{
uint8_t v___x_4329_; 
lean_inc(v___x_4327_);
v___x_4329_ = l_Lean_Syntax_matchesNull(v___x_4327_, v___x_4311_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
lean_dec(v___x_4327_);
lean_dec(v_o_4318_);
lean_dec(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec(v___y_4313_);
lean_dec(v_tk_3930_);
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_4330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4330_;
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4331_ = l_Lean_Syntax_getArg(v___x_4327_, v___x_3929_);
lean_dec(v___x_4327_);
v___x_4332_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3918_);
lean_inc_ref(v___x_3917_);
lean_inc_ref(v___x_3916_);
v___x_4333_ = l_Lean_Name_mkStr4(v___x_3916_, v___x_3917_, v___x_3918_, v___x_4332_);
lean_inc(v___x_4331_);
v___x_4334_ = l_Lean_Syntax_isOfKind(v___x_4331_, v___x_4333_);
lean_dec(v___x_4333_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; 
lean_dec(v___x_4331_);
lean_dec(v_o_4318_);
lean_dec(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec(v___y_4313_);
lean_dec(v_tk_3930_);
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_4335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; lean_object* v_args_4337_; lean_object* v___x_4338_; 
v___x_4336_ = l_Lean_Syntax_getArg(v___x_4331_, v___x_4311_);
lean_dec(v___x_4331_);
v_args_4337_ = l_Lean_Syntax_getArgs(v___x_4336_);
lean_dec(v___x_4336_);
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v_args_4337_);
v___y_4285_ = v___y_4313_;
v___y_4286_ = v_o_4318_;
v___y_4287_ = v___y_4314_;
v___y_4288_ = v___y_4316_;
v___y_4289_ = v___y_4317_;
v_args_4290_ = v___x_4338_;
v___y_4291_ = v___y_4319_;
v___y_4292_ = v___y_4320_;
v___y_4293_ = v___y_4321_;
v___y_4294_ = v___y_4322_;
v___y_4295_ = v___y_4323_;
v___y_4296_ = v___y_4324_;
v___y_4297_ = v___y_4325_;
v___y_4298_ = v___y_4326_;
goto v___jp_4284_;
}
}
}
else
{
lean_object* v___x_4339_; 
lean_dec(v___x_4327_);
v___x_4339_ = lean_box(0);
v___y_4285_ = v___y_4313_;
v___y_4286_ = v_o_4318_;
v___y_4287_ = v___y_4314_;
v___y_4288_ = v___y_4316_;
v___y_4289_ = v___y_4317_;
v_args_4290_ = v___x_4339_;
v___y_4291_ = v___y_4319_;
v___y_4292_ = v___y_4320_;
v___y_4293_ = v___y_4321_;
v___y_4294_ = v___y_4322_;
v___y_4295_ = v___y_4323_;
v___y_4296_ = v___y_4324_;
v___y_4297_ = v___y_4325_;
v___y_4298_ = v___y_4326_;
goto v___jp_4284_;
}
}
v___jp_4340_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4350_ = lean_unsigned_to_nat(2u);
v___x_4351_ = l_Lean_Syntax_getArg(v_stx_3914_, v___x_4350_);
v___x_4352_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3918_);
lean_inc_ref(v___x_3917_);
lean_inc_ref(v___x_3916_);
v___x_4353_ = l_Lean_Name_mkStr4(v___x_3916_, v___x_3917_, v___x_3918_, v___x_4352_);
lean_inc(v___x_4351_);
v___x_4354_ = l_Lean_Syntax_isOfKind(v___x_4351_, v___x_4353_);
lean_dec(v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
lean_dec(v___x_4351_);
lean_dec(v_bang_4341_);
lean_dec(v_tk_3930_);
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_4355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4356_ = l_Lean_Syntax_getArg(v___x_4351_, v___x_3929_);
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3918_);
lean_inc_ref(v___x_3917_);
lean_inc_ref(v___x_3916_);
v___x_4358_ = l_Lean_Name_mkStr4(v___x_3916_, v___x_3917_, v___x_3918_, v___x_4357_);
lean_inc(v___x_4356_);
v___x_4359_ = l_Lean_Syntax_isOfKind(v___x_4356_, v___x_4358_);
lean_dec(v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec(v___x_4356_);
lean_dec(v___x_4351_);
lean_dec(v_bang_4341_);
lean_dec(v_tk_3930_);
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_4360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4360_;
}
else
{
lean_object* v___x_4361_; uint8_t v___x_4362_; 
v___x_4361_ = l_Lean_Syntax_getArg(v___x_4351_, v___x_4311_);
v___x_4362_ = l_Lean_Syntax_isNone(v___x_4361_);
if (v___x_4362_ == 0)
{
uint8_t v___x_4363_; 
lean_inc(v___x_4361_);
v___x_4363_ = l_Lean_Syntax_matchesNull(v___x_4361_, v___x_4311_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
lean_dec(v___x_4361_);
lean_dec(v___x_4356_);
lean_dec(v___x_4351_);
lean_dec(v_bang_4341_);
lean_dec(v_tk_3930_);
lean_dec_ref(v___x_3918_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
v___x_4364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4364_;
}
else
{
lean_object* v_o_4365_; lean_object* v___x_4366_; 
v_o_4365_ = l_Lean_Syntax_getArg(v___x_4361_, v___x_3929_);
lean_dec(v___x_4361_);
v___x_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4366_, 0, v_o_4365_);
v___y_4313_ = v___x_4356_;
v___y_4314_ = v___x_4354_;
v___y_4315_ = v___x_4350_;
v___y_4316_ = v___x_4351_;
v___y_4317_ = v_bang_4341_;
v_o_4318_ = v___x_4366_;
v___y_4319_ = v___y_4342_;
v___y_4320_ = v___y_4343_;
v___y_4321_ = v___y_4344_;
v___y_4322_ = v___y_4345_;
v___y_4323_ = v___y_4346_;
v___y_4324_ = v___y_4347_;
v___y_4325_ = v___y_4348_;
v___y_4326_ = v___y_4349_;
goto v___jp_4312_;
}
}
else
{
lean_object* v___x_4367_; 
lean_dec(v___x_4361_);
v___x_4367_ = lean_box(0);
v___y_4313_ = v___x_4356_;
v___y_4314_ = v___x_4354_;
v___y_4315_ = v___x_4350_;
v___y_4316_ = v___x_4351_;
v___y_4317_ = v_bang_4341_;
v_o_4318_ = v___x_4367_;
v___y_4319_ = v___y_4342_;
v___y_4320_ = v___y_4343_;
v___y_4321_ = v___y_4344_;
v___y_4322_ = v___y_4345_;
v___y_4323_ = v___y_4346_;
v___y_4324_ = v___y_4347_;
v___y_4325_ = v___y_4348_;
v___y_4326_ = v___y_4349_;
goto v___jp_4312_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4375_, lean_object* v_stx_4376_, lean_object* v___x_4377_, lean_object* v___x_4378_, lean_object* v___x_4379_, lean_object* v___x_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
uint8_t v___x_8035__boxed_4390_; uint8_t v___x_8036__boxed_4391_; lean_object* v_res_4392_; 
v___x_8035__boxed_4390_ = lean_unbox(v___x_4375_);
v___x_8036__boxed_4391_ = lean_unbox(v___x_4377_);
v_res_4392_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8035__boxed_4390_, v_stx_4376_, v___x_8036__boxed_4391_, v___x_4378_, v___x_4379_, v___x_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v_stx_4376_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; uint8_t v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___y_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4412_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4399_);
v___x_4413_ = l_Lean_Syntax_isOfKind(v_stx_4399_, v___x_4412_);
v___x_4414_ = 1;
v___x_4415_ = lean_box(v___x_4413_);
v___x_4416_ = lean_box(v___x_4414_);
v___y_4417_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4417_, 0, v___x_4415_);
lean_closure_set(v___y_4417_, 1, v_stx_4399_);
lean_closure_set(v___y_4417_, 2, v___x_4416_);
lean_closure_set(v___y_4417_, 3, v___x_4409_);
lean_closure_set(v___y_4417_, 4, v___x_4410_);
lean_closure_set(v___y_4417_, 5, v___x_4411_);
v___x_4418_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4418_, 0, v___y_4417_);
v___x_4419_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4418_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4438_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4439_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4441_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4442_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4438_, v___x_4439_, v___x_4440_, v___x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4473_ = l_Lean_addBuiltinDeclarationRanges(v___x_4471_, v___x_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4475_;
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
