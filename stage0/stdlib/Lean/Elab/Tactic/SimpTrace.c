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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
lean_dec_ref_known(v_pre_49_, 2);
lean_dec(v_pre_50_);
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
lean_dec_ref_known(v_pre_26_, 2);
lean_dec(v_pre_27_);
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
uint8_t v___x_33581__boxed_208_; lean_object* v_res_209_; 
v___x_33581__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33581__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_33608__boxed_246_; lean_object* v_res_247_; 
v___x_33608__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33608__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v___x_327_; lean_object* v_toCold_328_; lean_object* v_mctx_329_; lean_object* v_lctx_330_; lean_object* v_options_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = lean_st_ref_get(v___y_321_);
v_toCold_328_ = lean_ctor_get(v___y_322_, 0);
v_mctx_329_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_mctx_329_);
lean_dec(v___x_327_);
v_lctx_330_ = lean_ctor_get(v___y_320_, 2);
v_options_331_ = lean_ctor_get(v_toCold_328_, 2);
lean_inc_ref(v_options_331_);
lean_inc_ref(v_lctx_330_);
v___x_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_332_, 0, v_env_326_);
lean_ctor_set(v___x_332_, 1, v_mctx_329_);
lean_ctor_set(v___x_332_, 2, v_lctx_330_);
lean_ctor_set(v___x_332_, 3, v_options_331_);
v___x_333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_msgData_319_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_349_, uint8_t v___y_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 1)
{
lean_object* v_pre_352_; 
v_pre_352_ = lean_ctor_get(v_x_351_, 0);
switch(lean_obj_tag(v_pre_352_))
{
case 1:
{
lean_object* v_pre_353_; 
v_pre_353_ = lean_ctor_get(v_pre_352_, 0);
switch(lean_obj_tag(v_pre_353_))
{
case 0:
{
lean_object* v_str_354_; lean_object* v_str_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_str_354_ = lean_ctor_get(v_x_351_, 1);
v_str_355_ = lean_ctor_get(v_pre_352_, 1);
v___x_356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_357_ = lean_string_dec_eq(v_str_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_359_ = lean_string_dec_eq(v_str_355_, v___x_358_);
if (v___x_359_ == 0)
{
return v___x_359_;
}
else
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_361_ = lean_string_dec_eq(v_str_354_, v___x_360_);
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
return v_suppressElabErrors_349_;
}
}
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_363_ = lean_string_dec_eq(v_str_354_, v___x_362_);
if (v___x_363_ == 0)
{
return v___x_363_;
}
else
{
return v_suppressElabErrors_349_;
}
}
}
case 1:
{
lean_object* v_pre_364_; 
v_pre_364_ = lean_ctor_get(v_pre_353_, 0);
if (lean_obj_tag(v_pre_364_) == 0)
{
lean_object* v_str_365_; lean_object* v_str_366_; lean_object* v_str_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_str_365_ = lean_ctor_get(v_x_351_, 1);
v_str_366_ = lean_ctor_get(v_pre_352_, 1);
v_str_367_ = lean_ctor_get(v_pre_353_, 1);
v___x_368_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_369_ = lean_string_dec_eq(v_str_367_, v___x_368_);
if (v___x_369_ == 0)
{
return v___x_369_;
}
else
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_371_ = lean_string_dec_eq(v_str_366_, v___x_370_);
if (v___x_371_ == 0)
{
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_373_ = lean_string_dec_eq(v_str_365_, v___x_372_);
if (v___x_373_ == 0)
{
return v___x_373_;
}
else
{
return v_suppressElabErrors_349_;
}
}
}
}
else
{
return v___y_350_;
}
}
default: 
{
return v___y_350_;
}
}
}
case 0:
{
lean_object* v_str_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_str_374_ = lean_ctor_get(v_x_351_, 1);
v___x_375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_376_ = lean_string_dec_eq(v_str_374_, v___x_375_);
if (v___x_376_ == 0)
{
return v___x_376_;
}
else
{
return v_suppressElabErrors_349_;
}
}
default: 
{
return v___y_350_;
}
}
}
else
{
return v___y_350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_377_, lean_object* v___y_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_suppressElabErrors_boxed_380_; uint8_t v___y_33809__boxed_381_; uint8_t v_res_382_; lean_object* v_r_383_; 
v_suppressElabErrors_boxed_380_ = lean_unbox(v_suppressElabErrors_377_);
v___y_33809__boxed_381_ = lean_unbox(v___y_378_);
v_res_382_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_380_, v___y_33809__boxed_381_, v_x_379_);
lean_dec(v_x_379_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_385_, lean_object* v_msgData_386_, uint8_t v_severity_387_, uint8_t v_isSilent_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
uint8_t v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_toCold_402_; lean_object* v___y_403_; lean_object* v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___y_439_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_465_; uint8_t v___y_469_; uint8_t v___y_470_; uint8_t v___y_471_; uint8_t v___x_482_; uint8_t v___y_484_; uint8_t v___y_485_; uint8_t v___y_486_; uint8_t v___y_488_; uint8_t v___x_496_; 
v___x_482_ = 2;
v___x_496_ = l_Lean_instBEqMessageSeverity_beq(v_severity_387_, v___x_482_);
if (v___x_496_ == 0)
{
v___y_488_ = v___x_496_;
goto v___jp_487_;
}
else
{
uint8_t v___x_497_; 
lean_inc_ref(v_msgData_386_);
v___x_497_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_386_);
v___y_488_ = v___x_497_;
goto v___jp_487_;
}
v___jp_394_:
{
lean_object* v_currNamespace_404_; lean_object* v_openDecls_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_traceState_414_; lean_object* v_cache_415_; lean_object* v_recordedDeps_416_; lean_object* v_messages_417_; lean_object* v_infoState_418_; lean_object* v_snapshotTasks_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
v_currNamespace_404_ = lean_ctor_get(v_toCold_402_, 4);
v_openDecls_405_ = lean_ctor_get(v_toCold_402_, 5);
lean_inc(v_openDecls_405_);
lean_inc(v_currNamespace_404_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_currNamespace_404_);
lean_ctor_set(v___x_406_, 1, v_openDecls_405_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc_ref(v___y_397_);
v___x_408_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_408_, 0, v___y_397_);
lean_ctor_set(v___x_408_, 1, v___y_399_);
lean_ctor_set(v___x_408_, 2, v___y_396_);
lean_ctor_set(v___x_408_, 3, v___y_400_);
lean_ctor_set(v___x_408_, 4, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*5, v___y_398_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*5 + 1, v___y_395_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*5 + 2, v_isSilent_388_);
v___x_409_ = lean_st_ref_take(v___y_403_);
v_env_410_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_409_, 1);
v_ngen_412_ = lean_ctor_get(v___x_409_, 2);
v_auxDeclNGen_413_ = lean_ctor_get(v___x_409_, 3);
v_traceState_414_ = lean_ctor_get(v___x_409_, 4);
v_cache_415_ = lean_ctor_get(v___x_409_, 5);
v_recordedDeps_416_ = lean_ctor_get(v___x_409_, 6);
v_messages_417_ = lean_ctor_get(v___x_409_, 7);
v_infoState_418_ = lean_ctor_get(v___x_409_, 8);
v_snapshotTasks_419_ = lean_ctor_get(v___x_409_, 9);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_430_ == 0)
{
v___x_421_ = v___x_409_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snapshotTasks_419_);
lean_inc(v_infoState_418_);
lean_inc(v_messages_417_);
lean_inc(v_recordedDeps_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_ngen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_423_ = lean_box(0);
v___x_424_ = l_Lean_MessageLog_add(v___x_408_, v_messages_417_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 7, v___x_424_);
v___x_426_ = v___x_421_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_env_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_traceState_414_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v_recordedDeps_416_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_429_, 8, v_infoState_418_);
lean_ctor_set(v_reuseFailAlloc_429_, 9, v_snapshotTasks_419_);
v___x_426_ = v_reuseFailAlloc_429_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_st_ref_put(v___y_403_, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_423_);
return v___x_428_;
}
}
}
v___jp_431_:
{
lean_object* v_fileName_440_; lean_object* v_fileMap_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_457_; 
v_fileName_440_ = lean_ctor_get(v___y_437_, 0);
v_fileMap_441_ = lean_ctor_get(v___y_437_, 1);
v___x_442_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_386_);
v___x_443_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_442_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_457_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc_ref_n(v_fileMap_441_, 2);
v___x_448_ = l_Lean_FileMap_toPosition(v_fileMap_441_, v___y_435_);
lean_dec(v___y_435_);
v___x_449_ = l_Lean_FileMap_toPosition(v_fileMap_441_, v___y_439_);
lean_dec(v___y_439_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_436_ == 0)
{
lean_del_object(v___x_446_);
lean_dec_ref(v___y_433_);
v___y_395_ = v___y_434_;
v___y_396_ = v___x_450_;
v___y_397_ = v_fileName_440_;
v___y_398_ = v___y_438_;
v___y_399_ = v___x_448_;
v___y_400_ = v___x_451_;
v___y_401_ = v_a_444_;
v_toCold_402_ = v___y_432_;
v___y_403_ = v___y_392_;
goto v___jp_394_;
}
else
{
uint8_t v___x_452_; 
lean_inc(v_a_444_);
v___x_452_ = l_Lean_MessageData_hasTag(v___y_433_, v_a_444_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec_ref_known(v___x_450_, 1);
lean_dec_ref(v___x_448_);
lean_dec(v_a_444_);
v___x_453_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_453_);
v___x_455_ = v___x_446_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_del_object(v___x_446_);
v___y_395_ = v___y_434_;
v___y_396_ = v___x_450_;
v___y_397_ = v_fileName_440_;
v___y_398_ = v___y_438_;
v___y_399_ = v___x_448_;
v___y_400_ = v___x_451_;
v___y_401_ = v_a_444_;
v_toCold_402_ = v___y_432_;
v___y_403_ = v___y_392_;
goto v___jp_394_;
}
}
}
}
v___jp_458_:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Syntax_getTailPos_x3f(v___y_463_, v___y_464_);
lean_dec(v___y_463_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_inc(v___y_465_);
v___y_432_ = v___y_460_;
v___y_433_ = v___y_461_;
v___y_434_ = v___y_462_;
v___y_435_ = v___y_465_;
v___y_436_ = v___y_459_;
v___y_437_ = v___y_460_;
v___y_438_ = v___y_464_;
v___y_439_ = v___y_465_;
goto v___jp_431_;
}
else
{
lean_object* v_val_467_; 
v_val_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_466_, 1);
v___y_432_ = v___y_460_;
v___y_433_ = v___y_461_;
v___y_434_ = v___y_462_;
v___y_435_ = v___y_465_;
v___y_436_ = v___y_459_;
v___y_437_ = v___y_460_;
v___y_438_ = v___y_464_;
v___y_439_ = v_val_467_;
goto v___jp_431_;
}
}
v___jp_468_:
{
lean_object* v_toCold_472_; lean_object* v_ref_473_; uint8_t v_suppressElabErrors_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___f_477_; lean_object* v_ref_478_; lean_object* v___x_479_; 
v_toCold_472_ = lean_ctor_get(v___y_391_, 0);
v_ref_473_ = lean_ctor_get(v___y_391_, 2);
v_suppressElabErrors_474_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*3 + 2);
v___x_475_ = lean_box(v_suppressElabErrors_474_);
v___x_476_ = lean_box(v___y_469_);
v___f_477_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_477_, 0, v___x_475_);
lean_closure_set(v___f_477_, 1, v___x_476_);
v_ref_478_ = l_Lean_replaceRef(v_ref_385_, v_ref_473_);
v___x_479_ = l_Lean_Syntax_getPos_x3f(v_ref_478_, v___y_470_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___y_459_ = v_suppressElabErrors_474_;
v___y_460_ = v_toCold_472_;
v___y_461_ = v___f_477_;
v___y_462_ = v___y_471_;
v___y_463_ = v_ref_478_;
v___y_464_ = v___y_470_;
v___y_465_ = v___x_480_;
goto v___jp_458_;
}
else
{
lean_object* v_val_481_; 
v_val_481_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_479_, 1);
v___y_459_ = v_suppressElabErrors_474_;
v___y_460_ = v_toCold_472_;
v___y_461_ = v___f_477_;
v___y_462_ = v___y_471_;
v___y_463_ = v_ref_478_;
v___y_464_ = v___y_470_;
v___y_465_ = v_val_481_;
goto v___jp_458_;
}
}
v___jp_483_:
{
if (v___y_486_ == 0)
{
v___y_469_ = v___y_484_;
v___y_470_ = v___y_485_;
v___y_471_ = v_severity_387_;
goto v___jp_468_;
}
else
{
v___y_469_ = v___y_484_;
v___y_470_ = v___y_485_;
v___y_471_ = v___x_482_;
goto v___jp_468_;
}
}
v___jp_487_:
{
if (v___y_488_ == 0)
{
uint8_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 1;
v___x_490_ = l_Lean_instBEqMessageSeverity_beq(v_severity_387_, v___x_489_);
if (v___x_490_ == 0)
{
v___y_484_ = v___y_488_;
v___y_485_ = v___y_488_;
v___y_486_ = v___x_490_;
goto v___jp_483_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_391_);
v___x_492_ = l_Lean_warningAsError;
v___x_493_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v___x_491_, v___x_492_);
lean_dec_ref(v___x_491_);
v___y_484_ = v___y_488_;
v___y_485_ = v___y_488_;
v___y_486_ = v___x_493_;
goto v___jp_483_;
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref(v_msgData_386_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_498_, lean_object* v_msgData_499_, lean_object* v_severity_500_, lean_object* v_isSilent_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v_severity_boxed_507_; uint8_t v_isSilent_boxed_508_; lean_object* v_res_509_; 
v_severity_boxed_507_ = lean_unbox(v_severity_500_);
v_isSilent_boxed_508_ = lean_unbox(v_isSilent_501_);
v_res_509_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_498_, v_msgData_499_, v_severity_boxed_507_, v_isSilent_boxed_508_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v_ref_498_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_510_, uint8_t v_severity_511_, uint8_t v_isSilent_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_ref_522_; lean_object* v___x_523_; 
v_ref_522_ = lean_ctor_get(v___y_519_, 2);
v___x_523_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_522_, v_msgData_510_, v_severity_511_, v_isSilent_512_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_524_, lean_object* v_severity_525_, lean_object* v_isSilent_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v_severity_boxed_536_; uint8_t v_isSilent_boxed_537_; lean_object* v_res_538_; 
v_severity_boxed_536_ = lean_unbox(v_severity_525_);
v_isSilent_boxed_537_ = lean_unbox(v_isSilent_526_);
v_res_538_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_524_, v_severity_boxed_536_, v_isSilent_boxed_537_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = 1;
v___x_550_ = 0;
v___x_551_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_539_, v___x_549_, v___x_550_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_565_ = l_Lean_stringToMessageData(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v_env_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_602_; 
v___x_579_ = lean_st_ref_get(v___y_577_);
v_env_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_env_580_);
lean_dec(v___x_579_);
v___x_581_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_582_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_581_, v___y_576_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_602_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_602_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_602_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
uint8_t v_isExporting_592_; 
v_isExporting_592_ = lean_ctor_get_uint8(v_env_580_, sizeof(void*)*8);
lean_dec_ref(v_env_580_);
if (v_isExporting_592_ == 0)
{
lean_dec(v_a_583_);
lean_dec(v_id_569_);
goto v___jp_587_;
}
else
{
uint8_t v___x_593_; 
v___x_593_ = l_Lean_isPrivateName(v_id_569_);
if (v___x_593_ == 0)
{
lean_dec(v_a_583_);
lean_dec(v_id_569_);
goto v___jp_587_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = lean_unbox(v_a_583_);
lean_dec(v_a_583_);
if (v___x_594_ == 0)
{
lean_dec(v_id_569_);
goto v___jp_587_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_del_object(v___x_585_);
v___x_595_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_596_ = 0;
v___x_597_ = l_Lean_MessageData_ofConstName(v_id_569_, v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_600_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
return v___x_601_;
}
}
}
v___jp_587_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_614_, uint8_t v_enableLog_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v_toCold_626_; lean_object* v_env_627_; lean_object* v_currNamespace_628_; lean_object* v_openDecls_629_; lean_object* v___x_630_; lean_object* v_res_631_; lean_object* v___x_632_; 
v___x_625_ = lean_st_ref_get(v___y_623_);
v_toCold_626_ = lean_ctor_get(v___y_622_, 0);
v_env_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc_ref(v_env_627_);
lean_dec(v___x_625_);
v_currNamespace_628_ = lean_ctor_get(v_toCold_626_, 4);
v_openDecls_629_ = lean_ctor_get(v_toCold_626_, 5);
v___x_630_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_622_);
lean_inc(v_openDecls_629_);
lean_inc(v_currNamespace_628_);
v_res_631_ = l_Lean_ResolveName_resolveGlobalName(v_env_627_, v___x_630_, v_currNamespace_628_, v_openDecls_629_, v_id_614_);
lean_dec_ref(v___x_630_);
v___x_632_ = lean_st_ref_get(v___y_623_);
if (v_enableLog_615_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v___x_632_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_res_631_);
return v___x_633_;
}
else
{
lean_object* v_env_634_; uint8_t v_isExporting_635_; 
v_env_634_ = lean_ctor_get(v___x_632_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_632_);
v_isExporting_635_ = lean_ctor_get_uint8(v_env_634_, sizeof(void*)*8);
lean_dec_ref(v_env_634_);
if (v_isExporting_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_res_631_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_631_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v_fst_639_; lean_object* v___x_640_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_637_, 1);
v_fst_639_ = lean_ctor_get(v_val_638_, 0);
lean_inc(v_fst_639_);
lean_dec(v_val_638_);
v___x_640_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_639_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_640_, 0);
lean_dec(v_unused_648_);
v___x_642_ = v___x_640_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_dec(v___x_640_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_res_631_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_res_631_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_res_631_);
v_a_649_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_640_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_640_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v___x_657_; 
lean_dec(v___x_637_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_res_631_);
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_658_, lean_object* v_enableLog_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
uint8_t v_enableLog_boxed_669_; lean_object* v_res_670_; 
v_enableLog_boxed_669_ = lean_unbox(v_enableLog_659_);
v_res_670_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_658_, v_enableLog_boxed_669_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
if (lean_obj_tag(v_a_671_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = l_List_reverse___redArg(v_a_672_);
return v___x_673_;
}
else
{
lean_object* v_head_674_; lean_object* v_tail_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_686_; 
v_head_674_ = lean_ctor_get(v_a_671_, 0);
v_tail_675_ = lean_ctor_get(v_a_671_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_a_671_);
if (v_isSharedCheck_686_ == 0)
{
v___x_677_ = v_a_671_;
v_isShared_678_ = v_isSharedCheck_686_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_tail_675_);
lean_inc(v_head_674_);
lean_dec(v_a_671_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_686_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_snd_679_; uint8_t v___x_680_; 
v_snd_679_ = lean_ctor_get(v_head_674_, 1);
v___x_680_ = l_List_isEmpty___redArg(v_snd_679_);
if (v___x_680_ == 0)
{
lean_del_object(v___x_677_);
lean_dec(v_head_674_);
v_a_671_ = v_tail_675_;
goto _start;
}
else
{
lean_object* v___x_683_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v_a_672_);
v___x_683_ = v___x_677_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_head_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_672_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v_a_671_ = v_tail_675_;
v_a_672_ = v___x_683_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
if (lean_obj_tag(v_a_687_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = l_List_reverse___redArg(v_a_688_);
return v___x_689_;
}
else
{
lean_object* v_head_690_; lean_object* v_tail_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_700_; 
v_head_690_ = lean_ctor_get(v_a_687_, 0);
v_tail_691_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_700_ == 0)
{
v___x_693_ = v_a_687_;
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_tail_691_);
lean_inc(v_head_690_);
lean_dec(v_a_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_fst_695_; lean_object* v___x_697_; 
v_fst_695_ = lean_ctor_get(v_head_690_, 0);
lean_inc(v_fst_695_);
lean_dec(v_head_690_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_a_688_);
lean_ctor_set(v___x_693_, 0, v_fst_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_fst_695_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_a_688_);
v___x_697_ = v_reuseFailAlloc_699_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_a_687_ = v_tail_691_;
v_a_688_ = v___x_697_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_ref_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_ref_707_ = lean_ctor_get(v___y_704_, 2);
v___x_708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_inc(v_ref_707_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_ref_707_);
lean_ctor_set(v___x_713_, 1, v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 1);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_toCold_736_; lean_object* v_currRecDepth_737_; lean_object* v_ref_738_; uint16_t v_optionFlags_739_; uint8_t v_suppressElabErrors_740_; uint8_t v_isRecordingDeps_741_; lean_object* v_ref_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_toCold_736_ = lean_ctor_get(v___y_733_, 0);
v_currRecDepth_737_ = lean_ctor_get(v___y_733_, 1);
v_ref_738_ = lean_ctor_get(v___y_733_, 2);
v_optionFlags_739_ = lean_ctor_get_uint16(v___y_733_, sizeof(void*)*3);
v_suppressElabErrors_740_ = lean_ctor_get_uint8(v___y_733_, sizeof(void*)*3 + 2);
v_isRecordingDeps_741_ = lean_ctor_get_uint8(v___y_733_, sizeof(void*)*3 + 3);
v_ref_742_ = l_Lean_replaceRef(v_ref_725_, v_ref_738_);
lean_inc(v_currRecDepth_737_);
lean_inc_ref(v_toCold_736_);
v___x_743_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_743_, 0, v_toCold_736_);
lean_ctor_set(v___x_743_, 1, v_currRecDepth_737_);
lean_ctor_set(v___x_743_, 2, v_ref_742_);
lean_ctor_set_uint16(v___x_743_, sizeof(void*)*3, v_optionFlags_739_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*3 + 2, v_suppressElabErrors_740_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*3 + 3, v_isRecordingDeps_741_);
v___x_744_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_726_, v___y_731_, v___y_732_, v___x_743_, v___y_734_);
lean_dec_ref_known(v___x_743_, 3);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_745_, lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_745_, v_msg_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_ref_745_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
lean_ctor_set(v___x_762_, 3, v___x_761_);
lean_ctor_set(v___x_762_, 4, v___x_760_);
lean_ctor_set(v___x_762_, 5, v___x_760_);
lean_ctor_set(v___x_762_, 6, v___x_760_);
lean_ctor_set(v___x_762_, 7, v___x_760_);
lean_ctor_set(v___x_762_, 8, v___x_760_);
lean_ctor_set(v___x_762_, 9, v___x_760_);
lean_ctor_set(v___x_762_, 10, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(32u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_766_ = ((size_t)5ULL);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_unsigned_to_nat(32u);
v___x_769_ = lean_mk_empty_array_with_capacity(v___x_768_);
v___x_770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_771_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_769_);
lean_ctor_set(v___x_771_, 2, v___x_767_);
lean_ctor_set(v___x_771_, 3, v___x_767_);
lean_ctor_set_usize(v___x_771_, 4, v___x_766_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_772_ = lean_box(1);
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
lean_ctor_set(v___x_775_, 2, v___x_772_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_797_, lean_object* v_declHint_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_env_803_; uint8_t v___x_804_; 
v___x_801_ = lean_box(0);
v___x_802_ = lean_st_ref_get(v___y_799_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_env_803_);
lean_dec(v___x_802_);
v___x_804_ = l_Lean_Name_isAnonymous(v_declHint_798_);
if (v___x_804_ == 0)
{
uint8_t v_isExporting_805_; 
v_isExporting_805_ = lean_ctor_get_uint8(v_env_803_, sizeof(void*)*8);
if (v_isExporting_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v_msg_797_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
lean_inc_ref(v_env_803_);
v___x_807_ = l_Lean_Environment_setExporting(v_env_803_, v___x_804_);
lean_inc(v_declHint_798_);
lean_inc_ref(v___x_807_);
v___x_808_ = l_Lean_Environment_contains(v___x_807_, v_declHint_798_, v_isExporting_805_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v___x_807_);
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_msg_797_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_c_815_; lean_object* v___x_816_; 
v___x_810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_812_ = l_Lean_Options_empty;
v___x_813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_813_, 0, v___x_807_);
lean_ctor_set(v___x_813_, 1, v___x_810_);
lean_ctor_set(v___x_813_, 2, v___x_811_);
lean_ctor_set(v___x_813_, 3, v___x_812_);
lean_inc(v_declHint_798_);
v___x_814_ = l_Lean_MessageData_ofConstName(v_declHint_798_, v___x_804_);
v_c_815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_815_, 0, v___x_813_);
lean_ctor_set(v_c_815_, 1, v___x_814_);
v___x_816_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_803_, v_declHint_798_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_c_815_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_MessageData_note(v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v_msg_797_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_858_; 
v_val_824_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_858_ == 0)
{
v___x_826_ = v___x_816_;
v_isShared_827_ = v_isSharedCheck_858_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v___x_816_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_858_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_mod_830_; uint8_t v___x_831_; 
v___x_828_ = l_Lean_Environment_header(v_env_803_);
lean_dec_ref(v_env_803_);
v___x_829_ = l_Lean_EnvironmentHeader_moduleNames(v___x_828_);
v_mod_830_ = lean_array_get(v___x_801_, v___x_829_, v_val_824_);
lean_dec(v_val_824_);
lean_dec_ref(v___x_829_);
v___x_831_ = l_Lean_isPrivateName(v_declHint_798_);
lean_dec(v_declHint_798_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_c_815_);
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Lean_MessageData_ofName(v_mod_830_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_MessageData_note(v___x_839_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v_msg_797_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_841_);
v___x_843_ = v___x_826_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_c_815_);
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_MessageData_ofName(v_mod_830_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_MessageData_note(v___x_852_);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v_msg_797_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_854_);
v___x_856_ = v___x_826_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_859_; 
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v_msg_797_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_860_, lean_object* v_declHint_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_860_, v_declHint_861_, v___y_862_);
lean_dec(v___y_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_886_; 
v___x_876_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_865_, v_declHint_866_, v___y_874_);
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_886_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = l_Lean_unknownIdentifierMessageTag;
v___x_882_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_887_, lean_object* v_declHint_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_887_, v_declHint_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_899_, lean_object* v_msg_900_, lean_object* v_declHint_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_913_; 
v___x_911_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_900_, v_declHint_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
v___x_913_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_899_, v_a_912_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_914_, lean_object* v_msg_915_, lean_object* v_declHint_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_914_, v_msg_915_, v_declHint_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v_ref_914_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_933_, lean_object* v_constName_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_944_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_945_ = 0;
lean_inc(v_constName_934_);
v___x_946_ = l_Lean_MessageData_ofConstName(v_constName_934_, v___x_945_);
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_944_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_933_, v___x_949_, v_constName_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_951_, lean_object* v_constName_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_951_, v_constName_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v_ref_951_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_963_, lean_object* v_cs_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_cs_975_; uint8_t v___x_979_; 
v___x_974_ = lean_box(0);
v_cs_975_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_964_, v___x_974_);
v___x_979_ = l_List_isEmpty___redArg(v_cs_975_);
if (v___x_979_ == 0)
{
lean_dec(v_n_963_);
goto v___jp_976_;
}
else
{
lean_object* v_ref_980_; lean_object* v___x_981_; lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_cs_975_);
v_ref_980_ = lean_ctor_get(v___y_971_, 2);
v___x_981_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_980_, v_n_963_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
v___jp_976_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_975_, v___x_974_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_990_, lean_object* v_cs_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_990_, v_cs_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = 1;
lean_inc(v_n_1002_);
v___x_1013_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1002_, v___x_1012_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1002_, v_a_1014_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1015_;
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_n_1002_);
v_a_1016_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1013_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1013_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
if (lean_obj_tag(v_a_1035_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_array_to_list(v_a_1036_);
return v___x_1037_;
}
else
{
lean_object* v_head_1038_; 
v_head_1038_ = lean_ctor_get(v_a_1035_, 0);
if (lean_obj_tag(v_head_1038_) == 1)
{
lean_object* v_fields_1039_; 
v_fields_1039_ = lean_ctor_get(v_head_1038_, 1);
if (lean_obj_tag(v_fields_1039_) == 0)
{
lean_object* v_tail_1040_; lean_object* v_n_1041_; lean_object* v___x_1042_; 
lean_inc_ref(v_head_1038_);
v_tail_1040_ = lean_ctor_get(v_a_1035_, 1);
lean_inc(v_tail_1040_);
lean_dec_ref_known(v_a_1035_, 2);
v_n_1041_ = lean_ctor_get(v_head_1038_, 0);
lean_inc(v_n_1041_);
lean_dec_ref_known(v_head_1038_, 2);
v___x_1042_ = lean_array_push(v_a_1036_, v_n_1041_);
v_a_1035_ = v_tail_1040_;
v_a_1036_ = v___x_1042_;
goto _start;
}
else
{
lean_object* v_tail_1044_; 
v_tail_1044_ = lean_ctor_get(v_a_1035_, 1);
lean_inc(v_tail_1044_);
lean_dec_ref_known(v_a_1035_, 2);
v_a_1035_ = v_tail_1044_;
goto _start;
}
}
else
{
lean_object* v_tail_1046_; 
v_tail_1046_ = lean_ctor_get(v_a_1035_, 1);
lean_inc(v_tail_1046_);
lean_dec_ref_known(v_a_1035_, 2);
v_a_1035_ = v_tail_1046_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1054_ = l_Lean_MessageData_ofFormat(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1055_, lean_object* v_k_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
if (lean_obj_tag(v_stx_1055_) == 3)
{
lean_object* v_val_1066_; lean_object* v_preresolved_1067_; lean_object* v___x_1068_; lean_object* v_pre_1069_; uint8_t v___x_1070_; 
v_val_1066_ = lean_ctor_get(v_stx_1055_, 2);
lean_inc(v_val_1066_);
v_preresolved_1067_ = lean_ctor_get(v_stx_1055_, 3);
v___x_1068_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1067_);
v_pre_1069_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1067_, v___x_1068_);
v___x_1070_ = l_List_isEmpty___redArg(v_pre_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec_ref_known(v_stx_1055_, 4);
lean_dec(v_val_1066_);
lean_dec_ref(v_k_1056_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_pre_1069_);
return v___x_1071_;
}
else
{
lean_object* v_toCold_1072_; lean_object* v_currRecDepth_1073_; lean_object* v_ref_1074_; uint16_t v_optionFlags_1075_; uint8_t v_suppressElabErrors_1076_; uint8_t v_isRecordingDeps_1077_; lean_object* v_ref_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec(v_pre_1069_);
v_toCold_1072_ = lean_ctor_get(v___y_1063_, 0);
v_currRecDepth_1073_ = lean_ctor_get(v___y_1063_, 1);
v_ref_1074_ = lean_ctor_get(v___y_1063_, 2);
v_optionFlags_1075_ = lean_ctor_get_uint16(v___y_1063_, sizeof(void*)*3);
v_suppressElabErrors_1076_ = lean_ctor_get_uint8(v___y_1063_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1077_ = lean_ctor_get_uint8(v___y_1063_, sizeof(void*)*3 + 3);
v_ref_1078_ = l_Lean_replaceRef(v_stx_1055_, v_ref_1074_);
lean_dec_ref_known(v_stx_1055_, 4);
lean_inc(v_currRecDepth_1073_);
lean_inc_ref(v_toCold_1072_);
v___x_1079_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1079_, 0, v_toCold_1072_);
lean_ctor_set(v___x_1079_, 1, v_currRecDepth_1073_);
lean_ctor_set(v___x_1079_, 2, v_ref_1078_);
lean_ctor_set_uint16(v___x_1079_, sizeof(void*)*3, v_optionFlags_1075_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*3 + 2, v_suppressElabErrors_1076_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*3 + 3, v_isRecordingDeps_1077_);
lean_inc(v___y_1064_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
v___x_1080_ = lean_apply_10(v_k_1056_, v_val_1066_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___x_1079_, v___y_1064_, lean_box(0));
return v___x_1080_;
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_k_1056_);
v___x_1081_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1082_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1055_, v___x_1081_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v_stx_1055_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1083_, lean_object* v_k_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1083_, v_k_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1107_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1096_, v___x_1106_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1119_, size_t v_sz_1120_, size_t v_i_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_usize_dec_lt(v_i_1121_, v_sz_1120_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_b_1122_);
return v___x_1133_;
}
else
{
lean_object* v_a_1134_; lean_object* v_name_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_a_1134_ = lean_array_uget_borrowed(v_as_1119_, v_i_1121_);
v_name_1135_ = lean_ctor_get(v_a_1134_, 0);
lean_inc(v_name_1135_);
v___x_1136_ = l_Lean_mkIdent(v_name_1135_);
lean_inc(v___x_1136_);
v___x_1137_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1136_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1136_, v_a_1138_, v_b_1122_, v___y_1129_);
lean_dec(v_a_1138_);
lean_dec(v___x_1136_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; size_t v___x_1141_; size_t v___x_1142_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1121_, v___x_1141_);
v_i_1121_ = v___x_1142_;
v_b_1122_ = v_a_1140_;
goto _start;
}
else
{
return v___x_1139_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___x_1136_);
lean_dec_ref(v_b_1122_);
v_a_1144_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1137_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1137_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1152_, lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
size_t v_sz_boxed_1165_; size_t v_i_boxed_1166_; lean_object* v_res_1167_; 
v_sz_boxed_1165_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1166_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1152_, v_sz_boxed_1165_, v_i_boxed_1166_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_as_1152_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1187_, lean_object* v_stx_1188_, uint8_t v___x_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v___x_1192_, lean_object* v___f_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
if (v___x_1187_ == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_1203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v_tk_1205_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1277_; uint8_t v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1281_; lean_object* v_stxForSuggestion_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; uint8_t v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; uint8_t v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; uint8_t v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; uint8_t v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; uint8_t v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; uint8_t v___y_1526_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; uint8_t v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v_stxForExecution_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; uint8_t v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; uint8_t v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; uint8_t v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; uint8_t v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; uint8_t v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; uint8_t v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; uint8_t v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v_argsArray_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; uint8_t v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; uint8_t v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; uint8_t v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1976_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v_args_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___x_2003_; lean_object* v___y_2005_; uint8_t v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v_o_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v_bang_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v_tk_1205_ = l_Lean_Syntax_getArg(v_stx_1188_, v___x_1204_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2062_ = l_Lean_Syntax_getArg(v_stx_1188_, v___x_2003_);
v___x_2063_ = l_Lean_Syntax_isNone(v___x_2062_);
if (v___x_2063_ == 0)
{
uint8_t v___x_2064_; 
lean_inc(v___x_2062_);
v___x_2064_ = l_Lean_Syntax_matchesNull(v___x_2062_, v___x_2003_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec(v___x_2062_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_2065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2065_;
}
else
{
lean_object* v_bang_2066_; lean_object* v___x_2067_; 
v_bang_2066_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_1204_);
lean_dec(v___x_2062_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_bang_2066_);
v_bang_2034_ = v___x_2067_;
v___y_2035_ = v___y_1194_;
v___y_2036_ = v___y_1195_;
v___y_2037_ = v___y_1196_;
v___y_2038_ = v___y_1197_;
v___y_2039_ = v___y_1198_;
v___y_2040_ = v___y_1199_;
v___y_2041_ = v___y_1200_;
v___y_2042_ = v___y_1201_;
goto v___jp_2033_;
}
}
else
{
lean_object* v___x_2068_; 
lean_dec(v___x_2062_);
v___x_2068_ = lean_box(0);
v_bang_2034_ = v___x_2068_;
v___y_2035_ = v___y_1194_;
v___y_2036_ = v___y_1195_;
v___y_2037_ = v___y_1196_;
v___y_2038_ = v___y_1197_;
v___y_2039_ = v___y_1198_;
v___y_2040_ = v___y_1199_;
v___y_2041_ = v___y_1200_;
v___y_2042_ = v___y_1201_;
goto v___jp_2033_;
}
v___jp_1206_:
{
lean_object* v___x_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(v___x_1189_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1221_, 0, v___y_1209_);
lean_closure_set(v___f_1221_, 1, v___x_1204_);
lean_closure_set(v___f_1221_, 2, v___x_1220_);
lean_closure_set(v___f_1221_, 3, v___y_1219_);
lean_closure_set(v___f_1221_, 4, v___y_1208_);
v___x_1222_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1207_, v___f_1221_, v___y_1215_, v___y_1212_, v___y_1217_, v___y_1211_, v___y_1216_, v___y_1210_, v___y_1218_, v___y_1213_);
lean_dec(v___y_1207_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v_usedTheorems_1224_; lean_object* v_diag_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1267_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_usedTheorems_1224_ = lean_ctor_get(v_a_1223_, 0);
v_diag_1225_ = lean_ctor_get(v_a_1223_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_a_1223_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1227_ = v_a_1223_;
v_isShared_1228_ = v_isSharedCheck_1267_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_diag_1225_);
lean_inc(v_usedTheorems_1224_);
lean_dec(v_a_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1267_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1214_, v_usedTheorems_1224_, v___y_1216_, v___y_1210_, v___y_1218_, v___y_1213_);
lean_dec_ref(v_usedTheorems_1224_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v_ref_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v_ref_1231_ = lean_ctor_get(v___y_1218_, 2);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_a_1230_);
lean_ctor_set(v___x_1227_, 0, v___x_1232_);
v___x_1234_ = v___x_1227_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_a_1230_);
v___x_1234_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_ctor_set(v___x_1236_, 2, v___x_1235_);
lean_ctor_set(v___x_1236_, 3, v___x_1235_);
lean_ctor_set(v___x_1236_, 4, v___x_1235_);
lean_ctor_set(v___x_1236_, 5, v___x_1235_);
lean_inc(v_ref_1231_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_ref_1231_);
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1239_ = 4;
v___x_1240_ = l_Lean_MessageData_nil;
v___x_1241_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1205_, v___x_1236_, v___x_1237_, v___x_1238_, v___x_1235_, v___x_1239_, v___x_1240_, v___y_1218_, v___y_1213_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1249_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_diag_1225_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_diag_1225_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_diag_1225_);
v_a_1250_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1241_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1241_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_del_object(v___x_1227_);
lean_dec_ref(v_diag_1225_);
lean_dec(v_tk_1205_);
v_a_1259_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1229_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1229_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v___y_1214_);
lean_dec(v_tk_1205_);
v_a_1268_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1222_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1222_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
v___jp_1276_:
{
uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = 0;
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1293_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1279_, v___x_1291_, v___y_1281_, v___x_1291_, v___x_1292_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1279_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
if (lean_obj_tag(v___y_1280_) == 0)
{
lean_object* v_ctx_1295_; lean_object* v_simprocs_1296_; lean_object* v_dischargeWrapper_1297_; 
v_ctx_1295_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_ctx_1295_);
v_simprocs_1296_ = lean_ctor_get(v_a_1294_, 1);
lean_inc_ref(v_simprocs_1296_);
v_dischargeWrapper_1297_ = lean_ctor_get(v_a_1294_, 2);
lean_inc(v_dischargeWrapper_1297_);
lean_dec(v_a_1294_);
v___y_1207_ = v_dischargeWrapper_1297_;
v___y_1208_ = v_simprocs_1296_;
v___y_1209_ = v___y_1277_;
v___y_1210_ = v___y_1288_;
v___y_1211_ = v___y_1286_;
v___y_1212_ = v___y_1284_;
v___y_1213_ = v___y_1290_;
v___y_1214_ = v_stxForSuggestion_1282_;
v___y_1215_ = v___y_1283_;
v___y_1216_ = v___y_1287_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v_ctx_1295_;
goto v___jp_1206_;
}
else
{
lean_dec_ref_known(v___y_1280_, 1);
if (v___y_1278_ == 0)
{
lean_object* v_ctx_1298_; lean_object* v_simprocs_1299_; lean_object* v_dischargeWrapper_1300_; 
v_ctx_1298_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_ctx_1298_);
v_simprocs_1299_ = lean_ctor_get(v_a_1294_, 1);
lean_inc_ref(v_simprocs_1299_);
v_dischargeWrapper_1300_ = lean_ctor_get(v_a_1294_, 2);
lean_inc(v_dischargeWrapper_1300_);
lean_dec(v_a_1294_);
v___y_1207_ = v_dischargeWrapper_1300_;
v___y_1208_ = v_simprocs_1299_;
v___y_1209_ = v___y_1277_;
v___y_1210_ = v___y_1288_;
v___y_1211_ = v___y_1286_;
v___y_1212_ = v___y_1284_;
v___y_1213_ = v___y_1290_;
v___y_1214_ = v_stxForSuggestion_1282_;
v___y_1215_ = v___y_1283_;
v___y_1216_ = v___y_1287_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v_ctx_1298_;
goto v___jp_1206_;
}
else
{
lean_object* v_ctx_1301_; lean_object* v_simprocs_1302_; lean_object* v_dischargeWrapper_1303_; lean_object* v___x_1304_; 
v_ctx_1301_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_ctx_1301_);
v_simprocs_1302_ = lean_ctor_get(v_a_1294_, 1);
lean_inc_ref(v_simprocs_1302_);
v_dischargeWrapper_1303_ = lean_ctor_get(v_a_1294_, 2);
lean_inc(v_dischargeWrapper_1303_);
lean_dec(v_a_1294_);
v___x_1304_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1301_);
v___y_1207_ = v_dischargeWrapper_1303_;
v___y_1208_ = v_simprocs_1302_;
v___y_1209_ = v___y_1277_;
v___y_1210_ = v___y_1288_;
v___y_1211_ = v___y_1286_;
v___y_1212_ = v___y_1284_;
v___y_1213_ = v___y_1290_;
v___y_1214_ = v_stxForSuggestion_1282_;
v___y_1215_ = v___y_1283_;
v___y_1216_ = v___y_1287_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v___y_1289_;
v___y_1219_ = v___x_1304_;
goto v___jp_1206_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_stxForSuggestion_1282_);
lean_dec(v___y_1280_);
lean_dec(v___y_1277_);
lean_dec(v_tk_1205_);
v_a_1305_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1293_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1293_);
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
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_inc_ref(v___y_1318_);
v___x_1337_ = l_Array_append___redArg(v___y_1318_, v___y_1336_);
lean_dec_ref(v___y_1336_);
lean_inc(v___y_1319_);
lean_inc(v___y_1317_);
v___x_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___y_1317_);
lean_ctor_set(v___x_1338_, 1, v___y_1319_);
lean_ctor_set(v___x_1338_, 2, v___x_1337_);
v___x_1339_ = l_Lean_Syntax_node6(v___y_1317_, v___y_1325_, v___y_1321_, v___y_1323_, v___y_1326_, v___y_1334_, v___y_1328_, v___x_1338_);
v___y_1277_ = v___y_1314_;
v___y_1278_ = v___y_1324_;
v___y_1279_ = v___y_1315_;
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___y_1332_;
v_stxForSuggestion_1282_ = v___x_1339_;
v___y_1283_ = v___y_1322_;
v___y_1284_ = v___y_1335_;
v___y_1285_ = v___y_1329_;
v___y_1286_ = v___y_1331_;
v___y_1287_ = v___y_1316_;
v___y_1288_ = v___y_1320_;
v___y_1289_ = v___y_1330_;
v___y_1290_ = v___y_1327_;
goto v___jp_1276_;
}
v___jp_1340_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_inc_ref_n(v___y_1345_, 2);
v___x_1364_ = l_Array_append___redArg(v___y_1345_, v___y_1363_);
lean_dec_ref(v___y_1363_);
lean_inc_n(v___y_1346_, 3);
lean_inc_n(v___y_1342_, 5);
v___x_1365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1365_, 0, v___y_1342_);
lean_ctor_set(v___x_1365_, 1, v___y_1346_);
lean_ctor_set(v___x_1365_, 2, v___x_1364_);
v___x_1366_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___y_1342_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1369_ = l_Lean_Syntax_SepArray_ofElems(v___x_1368_, v___y_1360_);
lean_dec_ref(v___y_1360_);
v___x_1370_ = l_Array_append___redArg(v___y_1345_, v___x_1369_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1371_, 0, v___y_1342_);
lean_ctor_set(v___x_1371_, 1, v___y_1346_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1342_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node3(v___y_1342_, v___y_1346_, v___x_1367_, v___x_1371_, v___x_1373_);
if (lean_obj_tag(v___y_1361_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1376_; 
v_val_1375_ = lean_ctor_get(v___y_1361_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v___y_1361_, 1);
v___x_1376_ = l_Array_mkArray1___redArg(v_val_1375_);
v___y_1314_ = v___y_1341_;
v___y_1315_ = v___y_1343_;
v___y_1316_ = v___y_1344_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___y_1347_;
v___y_1321_ = v___y_1348_;
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1350_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___y_1353_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1354_;
v___y_1328_ = v___x_1374_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1357_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1358_;
v___y_1334_ = v___x_1365_;
v___y_1335_ = v___y_1362_;
v___y_1336_ = v___x_1376_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1377_; 
lean_dec(v___y_1361_);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1314_ = v___y_1341_;
v___y_1315_ = v___y_1343_;
v___y_1316_ = v___y_1344_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___y_1347_;
v___y_1321_ = v___y_1348_;
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1350_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___y_1353_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1354_;
v___y_1328_ = v___x_1374_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1357_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1358_;
v___y_1334_ = v___x_1365_;
v___y_1335_ = v___y_1362_;
v___y_1336_ = v___x_1377_;
goto v___jp_1313_;
}
}
v___jp_1378_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc_ref(v___y_1383_);
v___x_1402_ = l_Array_append___redArg(v___y_1383_, v___y_1401_);
lean_dec_ref(v___y_1401_);
lean_inc(v___y_1384_);
lean_inc(v___y_1380_);
v___x_1403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1380_);
lean_ctor_set(v___x_1403_, 1, v___y_1384_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
if (lean_obj_tag(v___y_1389_) == 1)
{
lean_object* v_val_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_val_1404_ = lean_ctor_get(v___y_1389_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v___y_1389_, 1);
v___x_1405_ = l_Lean_SourceInfo_fromRef(v_val_1404_, v___x_1189_);
lean_dec(v_val_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Array_mkArray1___redArg(v___x_1407_);
v___y_1341_ = v___y_1379_;
v___y_1342_ = v___y_1380_;
v___y_1343_ = v___y_1381_;
v___y_1344_ = v___y_1382_;
v___y_1345_ = v___y_1383_;
v___y_1346_ = v___y_1384_;
v___y_1347_ = v___y_1385_;
v___y_1348_ = v___y_1386_;
v___y_1349_ = v___y_1387_;
v___y_1350_ = v___y_1388_;
v___y_1351_ = v___y_1390_;
v___y_1352_ = v___x_1403_;
v___y_1353_ = v___y_1391_;
v___y_1354_ = v___y_1392_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___y_1394_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1398_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___y_1396_;
v___y_1361_ = v___y_1399_;
v___y_1362_ = v___y_1400_;
v___y_1363_ = v___x_1408_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1409_; 
lean_dec(v___y_1389_);
v___x_1409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1341_ = v___y_1379_;
v___y_1342_ = v___y_1380_;
v___y_1343_ = v___y_1381_;
v___y_1344_ = v___y_1382_;
v___y_1345_ = v___y_1383_;
v___y_1346_ = v___y_1384_;
v___y_1347_ = v___y_1385_;
v___y_1348_ = v___y_1386_;
v___y_1349_ = v___y_1387_;
v___y_1350_ = v___y_1388_;
v___y_1351_ = v___y_1390_;
v___y_1352_ = v___x_1403_;
v___y_1353_ = v___y_1391_;
v___y_1354_ = v___y_1392_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___y_1394_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1398_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___y_1396_;
v___y_1361_ = v___y_1399_;
v___y_1362_ = v___y_1400_;
v___y_1363_ = v___x_1409_;
goto v___jp_1340_;
}
}
v___jp_1410_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_inc_ref(v___y_1424_);
v___x_1434_ = l_Array_append___redArg(v___y_1424_, v___y_1433_);
lean_dec_ref(v___y_1433_);
lean_inc(v___y_1431_);
lean_inc(v___y_1421_);
v___x_1435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1421_);
lean_ctor_set(v___x_1435_, 1, v___y_1431_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
v___x_1436_ = l_Lean_Syntax_node6(v___y_1421_, v___y_1417_, v___y_1425_, v___y_1419_, v___y_1413_, v___y_1412_, v___y_1422_, v___x_1435_);
v___y_1277_ = v___y_1411_;
v___y_1278_ = v___y_1420_;
v___y_1279_ = v___y_1414_;
v___y_1280_ = v___y_1430_;
v___y_1281_ = v___y_1429_;
v_stxForSuggestion_1282_ = v___x_1436_;
v___y_1283_ = v___y_1418_;
v___y_1284_ = v___y_1432_;
v___y_1285_ = v___y_1426_;
v___y_1286_ = v___y_1428_;
v___y_1287_ = v___y_1415_;
v___y_1288_ = v___y_1416_;
v___y_1289_ = v___y_1427_;
v___y_1290_ = v___y_1423_;
goto v___jp_1276_;
}
v___jp_1437_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_inc_ref_n(v___y_1449_, 2);
v___x_1461_ = l_Array_append___redArg(v___y_1449_, v___y_1460_);
lean_dec_ref(v___y_1460_);
lean_inc_n(v___y_1459_, 3);
lean_inc_n(v___y_1446_, 5);
v___x_1462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1446_);
lean_ctor_set(v___x_1462_, 1, v___y_1459_);
lean_ctor_set(v___x_1462_, 2, v___x_1461_);
v___x_1463_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1446_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1466_ = l_Lean_Syntax_SepArray_ofElems(v___x_1465_, v___y_1456_);
lean_dec_ref(v___y_1456_);
v___x_1467_ = l_Array_append___redArg(v___y_1449_, v___x_1466_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1468_, 0, v___y_1446_);
lean_ctor_set(v___x_1468_, 1, v___y_1459_);
lean_ctor_set(v___x_1468_, 2, v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1446_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l_Lean_Syntax_node3(v___y_1446_, v___y_1459_, v___x_1464_, v___x_1468_, v___x_1470_);
if (lean_obj_tag(v___y_1457_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1473_; 
v_val_1472_ = lean_ctor_get(v___y_1457_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v___y_1457_, 1);
v___x_1473_ = l_Array_mkArray1___redArg(v_val_1472_);
v___y_1411_ = v___y_1438_;
v___y_1412_ = v___x_1462_;
v___y_1413_ = v___y_1439_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1441_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___y_1443_;
v___y_1418_ = v___y_1444_;
v___y_1419_ = v___y_1445_;
v___y_1420_ = v___y_1447_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___x_1471_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1449_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1451_;
v___y_1427_ = v___y_1452_;
v___y_1428_ = v___y_1453_;
v___y_1429_ = v___y_1455_;
v___y_1430_ = v___y_1454_;
v___y_1431_ = v___y_1459_;
v___y_1432_ = v___y_1458_;
v___y_1433_ = v___x_1473_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1474_; 
lean_dec(v___y_1457_);
v___x_1474_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1411_ = v___y_1438_;
v___y_1412_ = v___x_1462_;
v___y_1413_ = v___y_1439_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1441_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___y_1443_;
v___y_1418_ = v___y_1444_;
v___y_1419_ = v___y_1445_;
v___y_1420_ = v___y_1447_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___x_1471_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1449_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1451_;
v___y_1427_ = v___y_1452_;
v___y_1428_ = v___y_1453_;
v___y_1429_ = v___y_1455_;
v___y_1430_ = v___y_1454_;
v___y_1431_ = v___y_1459_;
v___y_1432_ = v___y_1458_;
v___y_1433_ = v___x_1474_;
goto v___jp_1410_;
}
}
v___jp_1475_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_ref(v___y_1486_);
v___x_1499_ = l_Array_append___redArg(v___y_1486_, v___y_1498_);
lean_dec_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc(v___y_1484_);
v___x_1500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1484_);
lean_ctor_set(v___x_1500_, 1, v___y_1497_);
lean_ctor_set(v___x_1500_, 2, v___x_1499_);
if (lean_obj_tag(v___y_1483_) == 1)
{
lean_object* v_val_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_val_1501_ = lean_ctor_get(v___y_1483_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___y_1483_, 1);
v___x_1502_ = l_Lean_SourceInfo_fromRef(v_val_1501_, v___x_1189_);
lean_dec(v_val_1501_);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Array_mkArray1___redArg(v___x_1504_);
v___y_1438_ = v___y_1476_;
v___y_1439_ = v___x_1500_;
v___y_1440_ = v___y_1477_;
v___y_1441_ = v___y_1478_;
v___y_1442_ = v___y_1479_;
v___y_1443_ = v___y_1480_;
v___y_1444_ = v___y_1481_;
v___y_1445_ = v___y_1482_;
v___y_1446_ = v___y_1484_;
v___y_1447_ = v___y_1485_;
v___y_1448_ = v___y_1487_;
v___y_1449_ = v___y_1486_;
v___y_1450_ = v___y_1488_;
v___y_1451_ = v___y_1489_;
v___y_1452_ = v___y_1490_;
v___y_1453_ = v___y_1491_;
v___y_1454_ = v___y_1494_;
v___y_1455_ = v___y_1493_;
v___y_1456_ = v___y_1492_;
v___y_1457_ = v___y_1495_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___y_1497_;
v___y_1460_ = v___x_1505_;
goto v___jp_1437_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v___y_1483_);
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1438_ = v___y_1476_;
v___y_1439_ = v___x_1500_;
v___y_1440_ = v___y_1477_;
v___y_1441_ = v___y_1478_;
v___y_1442_ = v___y_1479_;
v___y_1443_ = v___y_1480_;
v___y_1444_ = v___y_1481_;
v___y_1445_ = v___y_1482_;
v___y_1446_ = v___y_1484_;
v___y_1447_ = v___y_1485_;
v___y_1448_ = v___y_1487_;
v___y_1449_ = v___y_1486_;
v___y_1450_ = v___y_1488_;
v___y_1451_ = v___y_1489_;
v___y_1452_ = v___y_1490_;
v___y_1453_ = v___y_1491_;
v___y_1454_ = v___y_1494_;
v___y_1455_ = v___y_1493_;
v___y_1456_ = v___y_1492_;
v___y_1457_ = v___y_1495_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___y_1497_;
v___y_1460_ = v___x_1506_;
goto v___jp_1437_;
}
}
v___jp_1507_:
{
lean_object* v_ref_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_ref_1527_ = lean_ctor_get(v___y_1519_, 2);
v___x_1528_ = l_Lean_SourceInfo_fromRef(v_ref_1527_, v___y_1526_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1530_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_1529_);
v___x_1531_ = l_Lean_SourceInfo_fromRef(v_tk_1205_, v___x_1189_);
v___x_1532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1529_);
v___x_1533_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1534_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1509_) == 1)
{
lean_object* v_val_1535_; lean_object* v___x_1536_; 
v_val_1535_ = lean_ctor_get(v___y_1509_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___y_1509_, 1);
v___x_1536_ = l_Array_mkArray1___redArg(v_val_1535_);
v___y_1476_ = v___y_1508_;
v___y_1477_ = v___y_1510_;
v___y_1478_ = v___y_1511_;
v___y_1479_ = v___y_1512_;
v___y_1480_ = v___x_1530_;
v___y_1481_ = v___y_1513_;
v___y_1482_ = v___y_1514_;
v___y_1483_ = v___y_1515_;
v___y_1484_ = v___x_1528_;
v___y_1485_ = v___y_1516_;
v___y_1486_ = v___x_1534_;
v___y_1487_ = v___y_1517_;
v___y_1488_ = v___x_1532_;
v___y_1489_ = v___y_1518_;
v___y_1490_ = v___y_1519_;
v___y_1491_ = v___y_1520_;
v___y_1492_ = v___y_1523_;
v___y_1493_ = v___y_1522_;
v___y_1494_ = v___y_1521_;
v___y_1495_ = v___y_1524_;
v___y_1496_ = v___y_1525_;
v___y_1497_ = v___x_1533_;
v___y_1498_ = v___x_1536_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1537_; 
lean_dec(v___y_1509_);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1476_ = v___y_1508_;
v___y_1477_ = v___y_1510_;
v___y_1478_ = v___y_1511_;
v___y_1479_ = v___y_1512_;
v___y_1480_ = v___x_1530_;
v___y_1481_ = v___y_1513_;
v___y_1482_ = v___y_1514_;
v___y_1483_ = v___y_1515_;
v___y_1484_ = v___x_1528_;
v___y_1485_ = v___y_1516_;
v___y_1486_ = v___x_1534_;
v___y_1487_ = v___y_1517_;
v___y_1488_ = v___x_1532_;
v___y_1489_ = v___y_1518_;
v___y_1490_ = v___y_1519_;
v___y_1491_ = v___y_1520_;
v___y_1492_ = v___y_1523_;
v___y_1493_ = v___y_1522_;
v___y_1494_ = v___y_1521_;
v___y_1495_ = v___y_1524_;
v___y_1496_ = v___y_1525_;
v___y_1497_ = v___x_1533_;
v___y_1498_ = v___x_1537_;
goto v___jp_1475_;
}
}
v___jp_1538_:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1541_);
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1558_; uint8_t v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = 0;
v___y_1508_ = v___y_1539_;
v___y_1509_ = v___y_1540_;
v___y_1510_ = v_stxForExecution_1548_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1549_;
v___y_1514_ = v_a_1558_;
v___y_1515_ = v___y_1542_;
v___y_1516_ = v___y_1543_;
v___y_1517_ = v___y_1556_;
v___y_1518_ = v___y_1551_;
v___y_1519_ = v___y_1555_;
v___y_1520_ = v___y_1552_;
v___y_1521_ = v___y_1546_;
v___y_1522_ = v___y_1545_;
v___y_1523_ = v___y_1544_;
v___y_1524_ = v___y_1547_;
v___y_1525_ = v___y_1550_;
v___y_1526_ = v___x_1559_;
goto v___jp_1507_;
}
else
{
if (v___y_1543_ == 0)
{
lean_object* v_a_1560_; 
v_a_1560_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1557_);
v___y_1508_ = v___y_1539_;
v___y_1509_ = v___y_1540_;
v___y_1510_ = v_stxForExecution_1548_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1549_;
v___y_1514_ = v_a_1560_;
v___y_1515_ = v___y_1542_;
v___y_1516_ = v___y_1543_;
v___y_1517_ = v___y_1556_;
v___y_1518_ = v___y_1551_;
v___y_1519_ = v___y_1555_;
v___y_1520_ = v___y_1552_;
v___y_1521_ = v___y_1546_;
v___y_1522_ = v___y_1545_;
v___y_1523_ = v___y_1544_;
v___y_1524_ = v___y_1547_;
v___y_1525_ = v___y_1550_;
v___y_1526_ = v___y_1543_;
goto v___jp_1507_;
}
else
{
lean_object* v_a_1561_; lean_object* v_ref_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1561_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1557_);
v_ref_1562_ = lean_ctor_get(v___y_1555_, 2);
v___x_1563_ = 0;
v___x_1564_ = l_Lean_SourceInfo_fromRef(v_ref_1562_, v___x_1563_);
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1566_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_1565_);
v___x_1567_ = l_Lean_SourceInfo_fromRef(v_tk_1205_, v___x_1189_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1571_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1540_) == 1)
{
lean_object* v_val_1572_; lean_object* v___x_1573_; 
v_val_1572_ = lean_ctor_get(v___y_1540_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___y_1540_, 1);
v___x_1573_ = l_Array_mkArray1___redArg(v_val_1572_);
v___y_1379_ = v___y_1539_;
v___y_1380_ = v___x_1564_;
v___y_1381_ = v_stxForExecution_1548_;
v___y_1382_ = v___y_1553_;
v___y_1383_ = v___x_1571_;
v___y_1384_ = v___x_1570_;
v___y_1385_ = v___y_1554_;
v___y_1386_ = v___x_1569_;
v___y_1387_ = v___y_1549_;
v___y_1388_ = v_a_1561_;
v___y_1389_ = v___y_1542_;
v___y_1390_ = v___y_1543_;
v___y_1391_ = v___x_1566_;
v___y_1392_ = v___y_1556_;
v___y_1393_ = v___y_1551_;
v___y_1394_ = v___y_1555_;
v___y_1395_ = v___y_1552_;
v___y_1396_ = v___y_1544_;
v___y_1397_ = v___y_1545_;
v___y_1398_ = v___y_1546_;
v___y_1399_ = v___y_1547_;
v___y_1400_ = v___y_1550_;
v___y_1401_ = v___x_1573_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1574_; 
lean_dec(v___y_1540_);
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1379_ = v___y_1539_;
v___y_1380_ = v___x_1564_;
v___y_1381_ = v_stxForExecution_1548_;
v___y_1382_ = v___y_1553_;
v___y_1383_ = v___x_1571_;
v___y_1384_ = v___x_1570_;
v___y_1385_ = v___y_1554_;
v___y_1386_ = v___x_1569_;
v___y_1387_ = v___y_1549_;
v___y_1388_ = v_a_1561_;
v___y_1389_ = v___y_1542_;
v___y_1390_ = v___y_1543_;
v___y_1391_ = v___x_1566_;
v___y_1392_ = v___y_1556_;
v___y_1393_ = v___y_1551_;
v___y_1394_ = v___y_1555_;
v___y_1395_ = v___y_1552_;
v___y_1396_ = v___y_1544_;
v___y_1397_ = v___y_1545_;
v___y_1398_ = v___y_1546_;
v___y_1399_ = v___y_1547_;
v___y_1400_ = v___y_1550_;
v___y_1401_ = v___x_1574_;
goto v___jp_1378_;
}
}
}
}
v___jp_1575_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_inc_ref(v___y_1591_);
v___x_1602_ = l_Array_append___redArg(v___y_1591_, v___y_1601_);
lean_dec_ref(v___y_1601_);
lean_inc(v___y_1589_);
lean_inc(v___y_1595_);
v___x_1603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1603_, 0, v___y_1595_);
lean_ctor_set(v___x_1603_, 1, v___y_1589_);
lean_ctor_set(v___x_1603_, 2, v___x_1602_);
lean_inc(v___y_1590_);
v___x_1604_ = l_Lean_Syntax_node6(v___y_1595_, v___y_1586_, v___y_1579_, v___y_1590_, v___y_1600_, v___y_1599_, v___y_1593_, v___x_1603_);
v___y_1539_ = v___y_1576_;
v___y_1540_ = v___y_1577_;
v___y_1541_ = v___y_1590_;
v___y_1542_ = v___y_1583_;
v___y_1543_ = v___y_1584_;
v___y_1544_ = v___y_1596_;
v___y_1545_ = v___y_1587_;
v___y_1546_ = v___y_1597_;
v___y_1547_ = v___y_1598_;
v_stxForExecution_1548_ = v___x_1604_;
v___y_1549_ = v___y_1592_;
v___y_1550_ = v___y_1580_;
v___y_1551_ = v___y_1581_;
v___y_1552_ = v___y_1582_;
v___y_1553_ = v___y_1588_;
v___y_1554_ = v___y_1578_;
v___y_1555_ = v___y_1585_;
v___y_1556_ = v___y_1594_;
goto v___jp_1538_;
}
v___jp_1605_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_inc_ref_n(v___y_1616_, 2);
v___x_1630_ = l_Array_append___redArg(v___y_1616_, v___y_1629_);
lean_dec_ref(v___y_1629_);
lean_inc_n(v___y_1611_, 3);
lean_inc_n(v___y_1623_, 5);
v___x_1631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1631_, 0, v___y_1623_);
lean_ctor_set(v___x_1631_, 1, v___y_1611_);
lean_ctor_set(v___x_1631_, 2, v___x_1630_);
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___y_1623_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1635_ = l_Lean_Syntax_SepArray_ofElems(v___x_1634_, v___y_1626_);
v___x_1636_ = l_Array_append___redArg(v___y_1616_, v___x_1635_);
lean_dec_ref(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1637_, 0, v___y_1623_);
lean_ctor_set(v___x_1637_, 1, v___y_1611_);
lean_ctor_set(v___x_1637_, 2, v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1623_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_Syntax_node3(v___y_1623_, v___y_1611_, v___x_1633_, v___x_1637_, v___x_1639_);
if (lean_obj_tag(v___y_1627_) == 1)
{
lean_object* v_val_1641_; lean_object* v___x_1642_; 
v_val_1641_ = lean_ctor_get(v___y_1627_, 0);
lean_inc(v_val_1641_);
v___x_1642_ = l_Array_mkArray1___redArg(v_val_1641_);
v___y_1576_ = v___y_1606_;
v___y_1577_ = v___y_1608_;
v___y_1578_ = v___y_1609_;
v___y_1579_ = v___y_1610_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
v___y_1582_ = v___y_1614_;
v___y_1583_ = v___y_1618_;
v___y_1584_ = v___y_1619_;
v___y_1585_ = v___y_1621_;
v___y_1586_ = v___y_1622_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___y_1607_;
v___y_1589_ = v___y_1611_;
v___y_1590_ = v___y_1615_;
v___y_1591_ = v___y_1616_;
v___y_1592_ = v___y_1617_;
v___y_1593_ = v___x_1640_;
v___y_1594_ = v___y_1620_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___y_1626_;
v___y_1597_ = v___y_1624_;
v___y_1598_ = v___y_1627_;
v___y_1599_ = v___x_1631_;
v___y_1600_ = v___y_1628_;
v___y_1601_ = v___x_1642_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1576_ = v___y_1606_;
v___y_1577_ = v___y_1608_;
v___y_1578_ = v___y_1609_;
v___y_1579_ = v___y_1610_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
v___y_1582_ = v___y_1614_;
v___y_1583_ = v___y_1618_;
v___y_1584_ = v___y_1619_;
v___y_1585_ = v___y_1621_;
v___y_1586_ = v___y_1622_;
v___y_1587_ = v___y_1625_;
v___y_1588_ = v___y_1607_;
v___y_1589_ = v___y_1611_;
v___y_1590_ = v___y_1615_;
v___y_1591_ = v___y_1616_;
v___y_1592_ = v___y_1617_;
v___y_1593_ = v___x_1640_;
v___y_1594_ = v___y_1620_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___y_1626_;
v___y_1597_ = v___y_1624_;
v___y_1598_ = v___y_1627_;
v___y_1599_ = v___x_1631_;
v___y_1600_ = v___y_1628_;
v___y_1601_ = v___x_1643_;
goto v___jp_1575_;
}
}
v___jp_1644_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_inc_ref(v___y_1654_);
v___x_1668_ = l_Array_append___redArg(v___y_1654_, v___y_1667_);
lean_dec_ref(v___y_1667_);
lean_inc(v___y_1650_);
lean_inc(v___y_1662_);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1662_);
lean_ctor_set(v___x_1669_, 1, v___y_1650_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
if (lean_obj_tag(v___y_1657_) == 1)
{
lean_object* v_val_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_val_1670_ = lean_ctor_get(v___y_1657_, 0);
v___x_1671_ = l_Lean_SourceInfo_fromRef(v_val_1670_, v___x_1189_);
v___x_1672_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Array_mkArray1___redArg(v___x_1673_);
v___y_1606_ = v___y_1645_;
v___y_1607_ = v___y_1646_;
v___y_1608_ = v___y_1647_;
v___y_1609_ = v___y_1648_;
v___y_1610_ = v___y_1649_;
v___y_1611_ = v___y_1650_;
v___y_1612_ = v___y_1651_;
v___y_1613_ = v___y_1652_;
v___y_1614_ = v___y_1653_;
v___y_1615_ = v___y_1655_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1658_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1661_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___y_1665_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1663_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___x_1669_;
v___y_1629_ = v___x_1674_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1606_ = v___y_1645_;
v___y_1607_ = v___y_1646_;
v___y_1608_ = v___y_1647_;
v___y_1609_ = v___y_1648_;
v___y_1610_ = v___y_1649_;
v___y_1611_ = v___y_1650_;
v___y_1612_ = v___y_1651_;
v___y_1613_ = v___y_1652_;
v___y_1614_ = v___y_1653_;
v___y_1615_ = v___y_1655_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1658_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1656_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1661_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___y_1665_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1663_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___x_1669_;
v___y_1629_ = v___x_1675_;
goto v___jp_1605_;
}
}
v___jp_1676_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_inc_ref(v___y_1678_);
v___x_1703_ = l_Array_append___redArg(v___y_1678_, v___y_1702_);
lean_dec_ref(v___y_1702_);
lean_inc(v___y_1680_);
lean_inc(v___y_1693_);
v___x_1704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1704_, 0, v___y_1693_);
lean_ctor_set(v___x_1704_, 1, v___y_1680_);
lean_ctor_set(v___x_1704_, 2, v___x_1703_);
lean_inc(v___y_1695_);
v___x_1705_ = l_Lean_Syntax_node6(v___y_1693_, v___y_1694_, v___y_1698_, v___y_1695_, v___y_1684_, v___y_1690_, v___y_1692_, v___x_1704_);
v___y_1539_ = v___y_1677_;
v___y_1540_ = v___y_1679_;
v___y_1541_ = v___y_1695_;
v___y_1542_ = v___y_1686_;
v___y_1543_ = v___y_1687_;
v___y_1544_ = v___y_1699_;
v___y_1545_ = v___y_1689_;
v___y_1546_ = v___y_1700_;
v___y_1547_ = v___y_1701_;
v_stxForExecution_1548_ = v___x_1705_;
v___y_1549_ = v___y_1696_;
v___y_1550_ = v___y_1682_;
v___y_1551_ = v___y_1683_;
v___y_1552_ = v___y_1685_;
v___y_1553_ = v___y_1691_;
v___y_1554_ = v___y_1681_;
v___y_1555_ = v___y_1688_;
v___y_1556_ = v___y_1697_;
goto v___jp_1538_;
}
v___jp_1706_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_inc_ref_n(v___y_1709_, 2);
v___x_1731_ = l_Array_append___redArg(v___y_1709_, v___y_1730_);
lean_dec_ref(v___y_1730_);
lean_inc_n(v___y_1711_, 3);
lean_inc_n(v___y_1715_, 5);
v___x_1732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1732_, 0, v___y_1715_);
lean_ctor_set(v___x_1732_, 1, v___y_1711_);
lean_ctor_set(v___x_1732_, 2, v___x_1731_);
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___y_1715_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1736_ = l_Lean_Syntax_SepArray_ofElems(v___x_1735_, v___y_1728_);
v___x_1737_ = l_Array_append___redArg(v___y_1709_, v___x_1736_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___y_1715_);
lean_ctor_set(v___x_1738_, 1, v___y_1711_);
lean_ctor_set(v___x_1738_, 2, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___y_1715_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = l_Lean_Syntax_node3(v___y_1715_, v___y_1711_, v___x_1734_, v___x_1738_, v___x_1740_);
if (lean_obj_tag(v___y_1729_) == 1)
{
lean_object* v_val_1742_; lean_object* v___x_1743_; 
v_val_1742_ = lean_ctor_get(v___y_1729_, 0);
lean_inc(v_val_1742_);
v___x_1743_ = l_Array_mkArray1___redArg(v_val_1742_);
v___y_1677_ = v___y_1707_;
v___y_1678_ = v___y_1709_;
v___y_1679_ = v___y_1710_;
v___y_1680_ = v___y_1711_;
v___y_1681_ = v___y_1712_;
v___y_1682_ = v___y_1713_;
v___y_1683_ = v___y_1714_;
v___y_1684_ = v___y_1717_;
v___y_1685_ = v___y_1718_;
v___y_1686_ = v___y_1721_;
v___y_1687_ = v___y_1722_;
v___y_1688_ = v___y_1724_;
v___y_1689_ = v___y_1727_;
v___y_1690_ = v___x_1732_;
v___y_1691_ = v___y_1708_;
v___y_1692_ = v___x_1741_;
v___y_1693_ = v___y_1715_;
v___y_1694_ = v___y_1716_;
v___y_1695_ = v___y_1719_;
v___y_1696_ = v___y_1720_;
v___y_1697_ = v___y_1723_;
v___y_1698_ = v___y_1725_;
v___y_1699_ = v___y_1728_;
v___y_1700_ = v___y_1726_;
v___y_1701_ = v___y_1729_;
v___y_1702_ = v___x_1743_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1677_ = v___y_1707_;
v___y_1678_ = v___y_1709_;
v___y_1679_ = v___y_1710_;
v___y_1680_ = v___y_1711_;
v___y_1681_ = v___y_1712_;
v___y_1682_ = v___y_1713_;
v___y_1683_ = v___y_1714_;
v___y_1684_ = v___y_1717_;
v___y_1685_ = v___y_1718_;
v___y_1686_ = v___y_1721_;
v___y_1687_ = v___y_1722_;
v___y_1688_ = v___y_1724_;
v___y_1689_ = v___y_1727_;
v___y_1690_ = v___x_1732_;
v___y_1691_ = v___y_1708_;
v___y_1692_ = v___x_1741_;
v___y_1693_ = v___y_1715_;
v___y_1694_ = v___y_1716_;
v___y_1695_ = v___y_1719_;
v___y_1696_ = v___y_1720_;
v___y_1697_ = v___y_1723_;
v___y_1698_ = v___y_1725_;
v___y_1699_ = v___y_1728_;
v___y_1700_ = v___y_1726_;
v___y_1701_ = v___y_1729_;
v___y_1702_ = v___x_1744_;
goto v___jp_1676_;
}
}
v___jp_1745_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_inc_ref(v___y_1748_);
v___x_1769_ = l_Array_append___redArg(v___y_1748_, v___y_1768_);
lean_dec_ref(v___y_1768_);
lean_inc(v___y_1750_);
lean_inc(v___y_1754_);
v___x_1770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1754_);
lean_ctor_set(v___x_1770_, 1, v___y_1750_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
if (lean_obj_tag(v___y_1759_) == 1)
{
lean_object* v_val_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_val_1771_ = lean_ctor_get(v___y_1759_, 0);
v___x_1772_ = l_Lean_SourceInfo_fromRef(v_val_1771_, v___x_1189_);
v___x_1773_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Array_mkArray1___redArg(v___x_1774_);
v___y_1707_ = v___y_1746_;
v___y_1708_ = v___y_1747_;
v___y_1709_ = v___y_1748_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___y_1750_;
v___y_1712_ = v___y_1751_;
v___y_1713_ = v___y_1752_;
v___y_1714_ = v___y_1753_;
v___y_1715_ = v___y_1754_;
v___y_1716_ = v___y_1755_;
v___y_1717_ = v___x_1770_;
v___y_1718_ = v___y_1756_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1758_;
v___y_1723_ = v___y_1761_;
v___y_1724_ = v___y_1762_;
v___y_1725_ = v___y_1763_;
v___y_1726_ = v___y_1766_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1764_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___x_1775_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1707_ = v___y_1746_;
v___y_1708_ = v___y_1747_;
v___y_1709_ = v___y_1748_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___y_1750_;
v___y_1712_ = v___y_1751_;
v___y_1713_ = v___y_1752_;
v___y_1714_ = v___y_1753_;
v___y_1715_ = v___y_1754_;
v___y_1716_ = v___y_1755_;
v___y_1717_ = v___x_1770_;
v___y_1718_ = v___y_1756_;
v___y_1719_ = v___y_1757_;
v___y_1720_ = v___y_1760_;
v___y_1721_ = v___y_1759_;
v___y_1722_ = v___y_1758_;
v___y_1723_ = v___y_1761_;
v___y_1724_ = v___y_1762_;
v___y_1725_ = v___y_1763_;
v___y_1726_ = v___y_1766_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1764_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___x_1776_;
goto v___jp_1706_;
}
}
v___jp_1777_:
{
lean_object* v_ref_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_ref_1796_ = lean_ctor_get(v___y_1790_, 2);
v___x_1797_ = l_Lean_SourceInfo_fromRef(v_ref_1796_, v___y_1795_);
v___x_1798_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1192_);
lean_inc_ref(v___x_1191_);
lean_inc_ref(v___x_1190_);
v___x_1799_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_1798_);
v___x_1800_ = l_Lean_SourceInfo_fromRef(v_tk_1205_, v___x_1189_);
v___x_1801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1798_);
v___x_1802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1803_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1780_) == 1)
{
lean_object* v_val_1804_; lean_object* v___x_1805_; 
v_val_1804_ = lean_ctor_get(v___y_1780_, 0);
lean_inc(v_val_1804_);
v___x_1805_ = l_Array_mkArray1___redArg(v_val_1804_);
v___y_1746_ = v___y_1778_;
v___y_1747_ = v___y_1779_;
v___y_1748_ = v___x_1803_;
v___y_1749_ = v___y_1780_;
v___y_1750_ = v___x_1802_;
v___y_1751_ = v___y_1781_;
v___y_1752_ = v___y_1782_;
v___y_1753_ = v___y_1783_;
v___y_1754_ = v___x_1797_;
v___y_1755_ = v___x_1799_;
v___y_1756_ = v___y_1784_;
v___y_1757_ = v___y_1785_;
v___y_1758_ = v___y_1786_;
v___y_1759_ = v___y_1787_;
v___y_1760_ = v___y_1788_;
v___y_1761_ = v___y_1789_;
v___y_1762_ = v___y_1790_;
v___y_1763_ = v___x_1801_;
v___y_1764_ = v___y_1793_;
v___y_1765_ = v___y_1792_;
v___y_1766_ = v___y_1791_;
v___y_1767_ = v___y_1794_;
v___y_1768_ = v___x_1805_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1746_ = v___y_1778_;
v___y_1747_ = v___y_1779_;
v___y_1748_ = v___x_1803_;
v___y_1749_ = v___y_1780_;
v___y_1750_ = v___x_1802_;
v___y_1751_ = v___y_1781_;
v___y_1752_ = v___y_1782_;
v___y_1753_ = v___y_1783_;
v___y_1754_ = v___x_1797_;
v___y_1755_ = v___x_1799_;
v___y_1756_ = v___y_1784_;
v___y_1757_ = v___y_1785_;
v___y_1758_ = v___y_1786_;
v___y_1759_ = v___y_1787_;
v___y_1760_ = v___y_1788_;
v___y_1761_ = v___y_1789_;
v___y_1762_ = v___y_1790_;
v___y_1763_ = v___x_1801_;
v___y_1764_ = v___y_1793_;
v___y_1765_ = v___y_1792_;
v___y_1766_ = v___y_1791_;
v___y_1767_ = v___y_1794_;
v___y_1768_ = v___x_1806_;
goto v___jp_1745_;
}
}
v___jp_1807_:
{
if (lean_obj_tag(v___y_1813_) == 0)
{
uint8_t v___x_1825_; 
v___x_1825_ = 0;
v___y_1778_ = v___y_1808_;
v___y_1779_ = v___y_1821_;
v___y_1780_ = v___y_1810_;
v___y_1781_ = v___y_1822_;
v___y_1782_ = v___y_1818_;
v___y_1783_ = v___y_1819_;
v___y_1784_ = v___y_1820_;
v___y_1785_ = v___y_1809_;
v___y_1786_ = v___y_1811_;
v___y_1787_ = v___y_1812_;
v___y_1788_ = v___y_1817_;
v___y_1789_ = v___y_1824_;
v___y_1790_ = v___y_1823_;
v___y_1791_ = v___y_1813_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v_argsArray_1816_;
v___y_1794_ = v___y_1815_;
v___y_1795_ = v___x_1825_;
goto v___jp_1777_;
}
else
{
if (v___y_1811_ == 0)
{
v___y_1778_ = v___y_1808_;
v___y_1779_ = v___y_1821_;
v___y_1780_ = v___y_1810_;
v___y_1781_ = v___y_1822_;
v___y_1782_ = v___y_1818_;
v___y_1783_ = v___y_1819_;
v___y_1784_ = v___y_1820_;
v___y_1785_ = v___y_1809_;
v___y_1786_ = v___y_1811_;
v___y_1787_ = v___y_1812_;
v___y_1788_ = v___y_1817_;
v___y_1789_ = v___y_1824_;
v___y_1790_ = v___y_1823_;
v___y_1791_ = v___y_1813_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v_argsArray_1816_;
v___y_1794_ = v___y_1815_;
v___y_1795_ = v___y_1811_;
goto v___jp_1777_;
}
else
{
lean_object* v_ref_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_ref_1826_ = lean_ctor_get(v___y_1823_, 2);
v___x_1827_ = 0;
v___x_1828_ = l_Lean_SourceInfo_fromRef(v_ref_1826_, v___x_1827_);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1192_);
lean_inc_ref(v___x_1191_);
lean_inc_ref(v___x_1190_);
v___x_1830_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_1829_);
v___x_1831_ = l_Lean_SourceInfo_fromRef(v_tk_1205_, v___x_1189_);
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1835_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1810_) == 1)
{
lean_object* v_val_1836_; lean_object* v___x_1837_; 
v_val_1836_ = lean_ctor_get(v___y_1810_, 0);
lean_inc(v_val_1836_);
v___x_1837_ = l_Array_mkArray1___redArg(v_val_1836_);
v___y_1645_ = v___y_1808_;
v___y_1646_ = v___y_1821_;
v___y_1647_ = v___y_1810_;
v___y_1648_ = v___y_1822_;
v___y_1649_ = v___x_1833_;
v___y_1650_ = v___x_1834_;
v___y_1651_ = v___y_1818_;
v___y_1652_ = v___y_1819_;
v___y_1653_ = v___y_1820_;
v___y_1654_ = v___x_1835_;
v___y_1655_ = v___y_1809_;
v___y_1656_ = v___y_1811_;
v___y_1657_ = v___y_1812_;
v___y_1658_ = v___y_1817_;
v___y_1659_ = v___y_1824_;
v___y_1660_ = v___y_1823_;
v___y_1661_ = v___x_1830_;
v___y_1662_ = v___x_1828_;
v___y_1663_ = v_argsArray_1816_;
v___y_1664_ = v___y_1814_;
v___y_1665_ = v___y_1813_;
v___y_1666_ = v___y_1815_;
v___y_1667_ = v___x_1837_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1645_ = v___y_1808_;
v___y_1646_ = v___y_1821_;
v___y_1647_ = v___y_1810_;
v___y_1648_ = v___y_1822_;
v___y_1649_ = v___x_1833_;
v___y_1650_ = v___x_1834_;
v___y_1651_ = v___y_1818_;
v___y_1652_ = v___y_1819_;
v___y_1653_ = v___y_1820_;
v___y_1654_ = v___x_1835_;
v___y_1655_ = v___y_1809_;
v___y_1656_ = v___y_1811_;
v___y_1657_ = v___y_1812_;
v___y_1658_ = v___y_1817_;
v___y_1659_ = v___y_1824_;
v___y_1660_ = v___y_1823_;
v___y_1661_ = v___x_1830_;
v___y_1662_ = v___x_1828_;
v___y_1663_ = v_argsArray_1816_;
v___y_1664_ = v___y_1814_;
v___y_1665_ = v___y_1813_;
v___y_1666_ = v___y_1815_;
v___y_1667_ = v___x_1838_;
goto v___jp_1644_;
}
}
}
}
v___jp_1839_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1851_, v___y_1843_, v___y_1856_, v___y_1845_, v___y_1842_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v___x_1860_ = l_Lean_LibrarySuggestions_select(v_a_1859_, v___y_1857_, v___y_1843_, v___y_1856_, v___y_1845_, v___y_1842_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; size_t v_sz_1862_; size_t v___x_1863_; lean_object* v___x_1864_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v_sz_1862_ = lean_array_size(v_a_1861_);
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1861_, v_sz_1862_, v___x_1863_, v___y_1846_, v___y_1844_, v___y_1851_, v___y_1852_, v___y_1847_, v___y_1843_, v___y_1856_, v___y_1845_, v___y_1842_);
lean_dec(v_a_1861_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___y_1808_ = v___y_1840_;
v___y_1809_ = v___y_1848_;
v___y_1810_ = v___y_1841_;
v___y_1811_ = v___y_1850_;
v___y_1812_ = v___y_1849_;
v___y_1813_ = v___y_1854_;
v___y_1814_ = v___y_1853_;
v___y_1815_ = v___y_1855_;
v_argsArray_1816_ = v_a_1865_;
v___y_1817_ = v___y_1844_;
v___y_1818_ = v___y_1851_;
v___y_1819_ = v___y_1852_;
v___y_1820_ = v___y_1847_;
v___y_1821_ = v___y_1843_;
v___y_1822_ = v___y_1856_;
v___y_1823_ = v___y_1845_;
v___y_1824_ = v___y_1842_;
goto v___jp_1807_;
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v_a_1866_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1864_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1864_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v_a_1874_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1860_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1860_);
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
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v_a_1882_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1858_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1858_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
v___jp_1890_:
{
lean_object* v_config_1909_; uint8_t v_suggestions_1910_; 
v_config_1909_ = lean_ctor_get(v___y_1901_, 0);
lean_inc_ref(v_config_1909_);
lean_dec_ref(v___y_1901_);
v_suggestions_1910_ = lean_ctor_get_uint8(v_config_1909_, sizeof(void*)*3 + 26);
if (v_suggestions_1910_ == 0)
{
lean_dec_ref(v_config_1909_);
lean_dec_ref(v___f_1193_);
v___y_1808_ = v___y_1891_;
v___y_1809_ = v___y_1898_;
v___y_1810_ = v___y_1892_;
v___y_1811_ = v___y_1900_;
v___y_1812_ = v___y_1899_;
v___y_1813_ = v___y_1904_;
v___y_1814_ = v___y_1905_;
v___y_1815_ = v___y_1907_;
v_argsArray_1816_ = v___y_1908_;
v___y_1817_ = v___y_1895_;
v___y_1818_ = v___y_1902_;
v___y_1819_ = v___y_1903_;
v___y_1820_ = v___y_1897_;
v___y_1821_ = v___y_1894_;
v___y_1822_ = v___y_1906_;
v___y_1823_ = v___y_1896_;
v___y_1824_ = v___y_1893_;
goto v___jp_1807_;
}
else
{
lean_object* v_maxSuggestions_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_maxSuggestions_1911_ = lean_ctor_get(v_config_1909_, 2);
lean_inc(v_maxSuggestions_1911_);
lean_dec_ref(v_config_1909_);
v___x_1912_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1913_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1911_) == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(100u);
v___x_1915_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1912_);
lean_ctor_set(v___x_1915_, 2, v___f_1193_);
lean_ctor_set(v___x_1915_, 3, v___x_1913_);
v___y_1840_ = v___y_1891_;
v___y_1841_ = v___y_1892_;
v___y_1842_ = v___y_1893_;
v___y_1843_ = v___y_1894_;
v___y_1844_ = v___y_1895_;
v___y_1845_ = v___y_1896_;
v___y_1846_ = v___y_1908_;
v___y_1847_ = v___y_1897_;
v___y_1848_ = v___y_1898_;
v___y_1849_ = v___y_1899_;
v___y_1850_ = v___y_1900_;
v___y_1851_ = v___y_1902_;
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1905_;
v___y_1854_ = v___y_1904_;
v___y_1855_ = v___y_1907_;
v___y_1856_ = v___y_1906_;
v___y_1857_ = v___x_1915_;
goto v___jp_1839_;
}
else
{
lean_object* v_val_1916_; lean_object* v___x_1917_; 
v_val_1916_ = lean_ctor_get(v_maxSuggestions_1911_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_maxSuggestions_1911_, 1);
v___x_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1917_, 0, v_val_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1912_);
lean_ctor_set(v___x_1917_, 2, v___f_1193_);
lean_ctor_set(v___x_1917_, 3, v___x_1913_);
v___y_1840_ = v___y_1891_;
v___y_1841_ = v___y_1892_;
v___y_1842_ = v___y_1893_;
v___y_1843_ = v___y_1894_;
v___y_1844_ = v___y_1895_;
v___y_1845_ = v___y_1896_;
v___y_1846_ = v___y_1908_;
v___y_1847_ = v___y_1897_;
v___y_1848_ = v___y_1898_;
v___y_1849_ = v___y_1899_;
v___y_1850_ = v___y_1900_;
v___y_1851_ = v___y_1902_;
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1905_;
v___y_1854_ = v___y_1904_;
v___y_1855_ = v___y_1907_;
v___y_1856_ = v___y_1906_;
v___y_1857_ = v___x_1917_;
goto v___jp_1839_;
}
}
}
v___jp_1918_:
{
uint8_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = 0;
lean_inc(v___y_1924_);
v___x_1935_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1924_, v___x_1934_, v___y_1923_, v___y_1920_, v___y_1926_);
if (lean_obj_tag(v___x_1935_) == 0)
{
if (lean_obj_tag(v___y_1922_) == 1)
{
lean_object* v_a_1936_; lean_object* v_val_1937_; lean_object* v___x_1938_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_val_1937_ = lean_ctor_get(v___y_1922_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v___y_1922_, 1);
v___x_1938_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1937_);
lean_dec(v_val_1937_);
lean_inc(v___y_1931_);
v___y_1891_ = v___y_1931_;
v___y_1892_ = v___y_1933_;
v___y_1893_ = v___y_1926_;
v___y_1894_ = v___y_1929_;
v___y_1895_ = v___y_1923_;
v___y_1896_ = v___y_1920_;
v___y_1897_ = v___y_1921_;
v___y_1898_ = v___y_1924_;
v___y_1899_ = v___y_1930_;
v___y_1900_ = v___y_1919_;
v___y_1901_ = v_a_1936_;
v___y_1902_ = v___y_1927_;
v___y_1903_ = v___y_1925_;
v___y_1904_ = v___y_1928_;
v___y_1905_ = v___x_1934_;
v___y_1906_ = v___y_1932_;
v___y_1907_ = v___y_1931_;
v___y_1908_ = v___x_1938_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
lean_dec(v___y_1922_);
v_a_1939_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1940_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1931_);
v___y_1891_ = v___y_1931_;
v___y_1892_ = v___y_1933_;
v___y_1893_ = v___y_1926_;
v___y_1894_ = v___y_1929_;
v___y_1895_ = v___y_1923_;
v___y_1896_ = v___y_1920_;
v___y_1897_ = v___y_1921_;
v___y_1898_ = v___y_1924_;
v___y_1899_ = v___y_1930_;
v___y_1900_ = v___y_1919_;
v___y_1901_ = v_a_1939_;
v___y_1902_ = v___y_1927_;
v___y_1903_ = v___y_1925_;
v___y_1904_ = v___y_1928_;
v___y_1905_ = v___x_1934_;
v___y_1906_ = v___y_1932_;
v___y_1907_ = v___y_1931_;
v___y_1908_ = v___x_1940_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v___y_1933_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1928_);
lean_dec(v___y_1924_);
lean_dec(v___y_1922_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v_a_1941_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1935_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1935_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
v___jp_1949_:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Syntax_getOptional_x3f(v___y_1963_);
lean_dec(v___y_1963_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_box(0);
v___y_1919_ = v___y_1956_;
v___y_1920_ = v___y_1953_;
v___y_1921_ = v___y_1954_;
v___y_1922_ = v___y_1960_;
v___y_1923_ = v___y_1952_;
v___y_1924_ = v___y_1955_;
v___y_1925_ = v___y_1959_;
v___y_1926_ = v___y_1950_;
v___y_1927_ = v___y_1958_;
v___y_1928_ = v___y_1961_;
v___y_1929_ = v___y_1951_;
v___y_1930_ = v___y_1957_;
v___y_1931_ = v___y_1964_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___x_1966_;
goto v___jp_1918_;
}
else
{
lean_object* v_val_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_val_1967_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1965_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_val_1967_);
lean_dec(v___x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_val_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1919_ = v___y_1956_;
v___y_1920_ = v___y_1953_;
v___y_1921_ = v___y_1954_;
v___y_1922_ = v___y_1960_;
v___y_1923_ = v___y_1952_;
v___y_1924_ = v___y_1955_;
v___y_1925_ = v___y_1959_;
v___y_1926_ = v___y_1950_;
v___y_1927_ = v___y_1958_;
v___y_1928_ = v___y_1961_;
v___y_1929_ = v___y_1951_;
v___y_1930_ = v___y_1957_;
v___y_1931_ = v___y_1964_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___x_1972_;
goto v___jp_1918_;
}
}
}
}
v___jp_1975_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_unsigned_to_nat(4u);
v___x_1992_ = l_Lean_Syntax_getArg(v___y_1979_, v___x_1991_);
lean_dec(v___y_1979_);
v___x_1993_ = l_Lean_Syntax_getOptional_x3f(v___x_1992_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_box(0);
v___y_1950_ = v___y_1990_;
v___y_1951_ = v___y_1987_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1989_;
v___y_1954_ = v___y_1986_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___y_1978_;
v___y_1957_ = v___y_1977_;
v___y_1958_ = v___y_1984_;
v___y_1959_ = v___y_1985_;
v___y_1960_ = v_args_1982_;
v___y_1961_ = v___y_1980_;
v___y_1962_ = v___y_1988_;
v___y_1963_ = v___y_1981_;
v___y_1964_ = v___x_1994_;
goto v___jp_1949_;
}
else
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_val_1995_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_val_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
v___y_1950_ = v___y_1990_;
v___y_1951_ = v___y_1987_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1989_;
v___y_1954_ = v___y_1986_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___y_1978_;
v___y_1957_ = v___y_1977_;
v___y_1958_ = v___y_1984_;
v___y_1959_ = v___y_1985_;
v___y_1960_ = v_args_1982_;
v___y_1961_ = v___y_1980_;
v___y_1962_ = v___y_1988_;
v___y_1963_ = v___y_1981_;
v___y_1964_ = v___x_2000_;
goto v___jp_1949_;
}
}
}
}
v___jp_2004_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = lean_unsigned_to_nat(3u);
v___x_2020_ = l_Lean_Syntax_getArg(v___y_2007_, v___x_2019_);
v___x_2021_ = l_Lean_Syntax_isNone(v___x_2020_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; 
lean_inc(v___x_2020_);
v___x_2022_ = l_Lean_Syntax_matchesNull(v___x_2020_, v___x_2003_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec(v___x_2020_);
lean_dec(v_o_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v___y_2005_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_2023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2024_ = l_Lean_Syntax_getArg(v___x_2020_, v___x_1204_);
lean_dec(v___x_2020_);
v___x_2025_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1192_);
lean_inc_ref(v___x_1191_);
lean_inc_ref(v___x_1190_);
v___x_2026_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_2025_);
lean_inc(v___x_2024_);
v___x_2027_ = l_Lean_Syntax_isOfKind(v___x_2024_, v___x_2026_);
lean_dec(v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_dec(v___x_2024_);
lean_dec(v_o_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v___y_2005_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_2028_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2028_;
}
else
{
lean_object* v___x_2029_; lean_object* v_args_2030_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_Syntax_getArg(v___x_2024_, v___x_2003_);
lean_dec(v___x_2024_);
v_args_2030_ = l_Lean_Syntax_getArgs(v___x_2029_);
lean_dec(v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_args_2030_);
v___y_1976_ = v___y_2005_;
v___y_1977_ = v_o_2010_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
v_args_1982_ = v___x_2031_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2012_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
goto v___jp_1975_;
}
}
}
else
{
lean_object* v___x_2032_; 
lean_dec(v___x_2020_);
v___x_2032_ = lean_box(0);
v___y_1976_ = v___y_2005_;
v___y_1977_ = v_o_2010_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
v_args_1982_ = v___x_2032_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2012_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
goto v___jp_1975_;
}
}
v___jp_2033_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2043_ = lean_unsigned_to_nat(2u);
v___x_2044_ = l_Lean_Syntax_getArg(v_stx_1188_, v___x_2043_);
v___x_2045_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1192_);
lean_inc_ref(v___x_1191_);
lean_inc_ref(v___x_1190_);
v___x_2046_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_2045_);
lean_inc(v___x_2044_);
v___x_2047_ = l_Lean_Syntax_isOfKind(v___x_2044_, v___x_2046_);
lean_dec(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v___x_2044_);
lean_dec(v_bang_2034_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_2048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2048_;
}
else
{
lean_object* v_cfg_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v_cfg_2049_ = l_Lean_Syntax_getArg(v___x_2044_, v___x_1204_);
v___x_2050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1192_);
lean_inc_ref(v___x_1191_);
lean_inc_ref(v___x_1190_);
v___x_2051_ = l_Lean_Name_mkStr4(v___x_1190_, v___x_1191_, v___x_1192_, v___x_2050_);
lean_inc(v_cfg_2049_);
v___x_2052_ = l_Lean_Syntax_isOfKind(v_cfg_2049_, v___x_2051_);
lean_dec(v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
lean_dec(v_cfg_2049_);
lean_dec(v___x_2044_);
lean_dec(v_bang_2034_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_2053_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2054_ = l_Lean_Syntax_getArg(v___x_2044_, v___x_2003_);
v___x_2055_ = l_Lean_Syntax_getArg(v___x_2044_, v___x_2043_);
v___x_2056_ = l_Lean_Syntax_isNone(v___x_2055_);
if (v___x_2056_ == 0)
{
uint8_t v___x_2057_; 
lean_inc(v___x_2055_);
v___x_2057_ = l_Lean_Syntax_matchesNull(v___x_2055_, v___x_2003_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
lean_dec(v___x_2055_);
lean_dec(v___x_2054_);
lean_dec(v_cfg_2049_);
lean_dec(v___x_2044_);
lean_dec(v_bang_2034_);
lean_dec(v_tk_1205_);
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1192_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
v___x_2058_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2058_;
}
else
{
lean_object* v_o_2059_; lean_object* v___x_2060_; 
v_o_2059_ = l_Lean_Syntax_getArg(v___x_2055_, v___x_1204_);
lean_dec(v___x_2055_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_o_2059_);
v___y_2005_ = v_cfg_2049_;
v___y_2006_ = v___x_2047_;
v___y_2007_ = v___x_2044_;
v___y_2008_ = v_bang_2034_;
v___y_2009_ = v___x_2054_;
v_o_2010_ = v___x_2060_;
v___y_2011_ = v___y_2035_;
v___y_2012_ = v___y_2036_;
v___y_2013_ = v___y_2037_;
v___y_2014_ = v___y_2038_;
v___y_2015_ = v___y_2039_;
v___y_2016_ = v___y_2040_;
v___y_2017_ = v___y_2041_;
v___y_2018_ = v___y_2042_;
goto v___jp_2004_;
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v___x_2055_);
v___x_2061_ = lean_box(0);
v___y_2005_ = v_cfg_2049_;
v___y_2006_ = v___x_2047_;
v___y_2007_ = v___x_2044_;
v___y_2008_ = v_bang_2034_;
v___y_2009_ = v___x_2054_;
v_o_2010_ = v___x_2061_;
v___y_2011_ = v___y_2035_;
v___y_2012_ = v___y_2036_;
v___y_2013_ = v___y_2037_;
v___y_2014_ = v___y_2038_;
v___y_2015_ = v___y_2039_;
v___y_2016_ = v___y_2040_;
v___y_2017_ = v___y_2041_;
v___y_2018_ = v___y_2042_;
goto v___jp_2004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2069_, lean_object* v_stx_2070_, lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v___x_2073_, lean_object* v___x_2074_, lean_object* v___f_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v___x_35256__boxed_2085_; uint8_t v___x_35257__boxed_2086_; lean_object* v_res_2087_; 
v___x_35256__boxed_2085_ = lean_unbox(v___x_2069_);
v___x_35257__boxed_2086_ = lean_unbox(v___x_2071_);
v_res_2087_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35256__boxed_2085_, v_stx_2070_, v___x_35257__boxed_2086_, v___x_2072_, v___x_2073_, v___x_2074_, v___f_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v_stx_2070_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___y_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2110_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2097_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v_stx_2097_, v___x_2110_);
v___x_2112_ = 1;
v___f_2113_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2114_ = lean_box(v___x_2111_);
v___x_2115_ = lean_box(v___x_2112_);
v___y_2116_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2116_, 0, v___x_2114_);
lean_closure_set(v___y_2116_, 1, v_stx_2097_);
lean_closure_set(v___y_2116_, 2, v___x_2115_);
lean_closure_set(v___y_2116_, 3, v___x_2107_);
lean_closure_set(v___y_2116_, 4, v___x_2108_);
lean_closure_set(v___y_2116_, 5, v___x_2109_);
lean_closure_set(v___y_2116_, 6, v___f_2113_);
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2117_, 0, v___y_2116_);
v___x_2118_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2117_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2130_, lean_object* v_as_2131_, lean_object* v_as_x27_2132_, lean_object* v_b_2133_, lean_object* v_a_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2130_, v_as_x27_2132_, v_b_2133_, v___y_2141_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2145_, lean_object* v_as_2146_, lean_object* v_as_x27_2147_, lean_object* v_b_2148_, lean_object* v_a_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2145_, v_as_2146_, v_as_x27_2147_, v_b_2148_, v_a_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v_as_x27_2147_);
lean_dec(v_as_2146_);
lean_dec(v___x_2145_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2160_, lean_object* v_ref_2161_, lean_object* v_msg_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2161_, v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_ref_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2173_, v_ref_2174_, v_msg_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v_ref_2174_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2186_, lean_object* v_ref_2187_, lean_object* v_constName_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2187_, v_constName_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2199_, lean_object* v_ref_2200_, lean_object* v_constName_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2199_, v_ref_2200_, v_constName_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v_ref_2200_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2212_, lean_object* v_msg_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2213_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_msg_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2224_, v_msg_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2236_, v___y_2243_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_opt_2247_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2258_, lean_object* v_ref_2259_, lean_object* v_msg_2260_, lean_object* v_declHint_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2259_, v_msg_2260_, v_declHint_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_ref_2273_, lean_object* v_msg_2274_, lean_object* v_declHint_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2272_, v_ref_2273_, v_msg_2274_, v_declHint_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v_ref_2273_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2286_, lean_object* v_declHint_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2286_, v_declHint_2287_, v___y_2295_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2298_, lean_object* v_declHint_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2298_, v_declHint_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2310_, lean_object* v_msgData_2311_, uint8_t v_severity_2312_, uint8_t v_isSilent_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2310_, v_msgData_2311_, v_severity_2312_, v_isSilent_2313_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2324_, lean_object* v_msgData_2325_, lean_object* v_severity_2326_, lean_object* v_isSilent_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_severity_boxed_2337_; uint8_t v_isSilent_boxed_2338_; lean_object* v_res_2339_; 
v_severity_boxed_2337_ = lean_unbox(v_severity_2326_);
v_isSilent_boxed_2338_ = lean_unbox(v_isSilent_2327_);
v_res_2339_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2324_, v_msgData_2325_, v_severity_boxed_2337_, v_isSilent_boxed_2338_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v_ref_2324_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2347_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2348_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2350_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2351_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2347_, v___x_2348_, v___x_2349_, v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2382_ = l_Lean_addBuiltinDeclarationRanges(v___x_2380_, v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2385_, lean_object* v_as_x27_2386_, lean_object* v_b_2387_, lean_object* v___y_2388_){
_start:
{
if (lean_obj_tag(v_as_x27_2386_) == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v_b_2387_);
return v___x_2390_;
}
else
{
lean_object* v_head_2391_; lean_object* v_tail_2392_; lean_object* v_ref_2393_; uint8_t v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_head_2391_ = lean_ctor_get(v_as_x27_2386_, 0);
v_tail_2392_ = lean_ctor_get(v_as_x27_2386_, 1);
v_ref_2393_ = lean_ctor_get(v___y_2388_, 2);
v___x_2394_ = 1;
v___x_2395_ = 0;
v___x_2396_ = l_Lean_SourceInfo_fromRef(v_ref_2393_, v___x_2395_);
v___x_2397_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2398_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2399_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2396_);
v___x_2400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2396_);
lean_ctor_set(v___x_2400_, 1, v___x_2398_);
lean_ctor_set(v___x_2400_, 2, v___x_2399_);
lean_inc(v_head_2391_);
v___x_2401_ = l_Lean_mkCIdentFrom(v___x_2385_, v_head_2391_, v___x_2394_);
lean_inc_ref(v___x_2400_);
v___x_2402_ = l_Lean_Syntax_node3(v___x_2396_, v___x_2397_, v___x_2400_, v___x_2400_, v___x_2401_);
v___x_2403_ = lean_array_push(v_b_2387_, v___x_2402_);
v_as_x27_2386_ = v_tail_2392_;
v_b_2387_ = v___x_2403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2405_, lean_object* v_as_x27_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2405_, v_as_x27_2406_, v_b_2407_, v___y_2408_);
lean_dec_ref(v___y_2408_);
lean_dec(v_as_x27_2406_);
lean_dec(v___x_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2411_, size_t v_sz_2412_, size_t v_i_2413_, lean_object* v_b_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_lt(v_i_2413_, v_sz_2412_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_b_2414_);
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v_name_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_a_2426_ = lean_array_uget_borrowed(v_as_2411_, v_i_2413_);
v_name_2427_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_name_2427_);
v___x_2428_ = l_Lean_mkIdent(v_name_2427_);
lean_inc(v___x_2428_);
v___x_2429_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2428_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2428_, v_a_2430_, v_b_2414_, v___y_2421_);
lean_dec(v_a_2430_);
lean_dec(v___x_2428_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; size_t v___x_2433_; size_t v___x_2434_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v___x_2433_ = ((size_t)1ULL);
v___x_2434_ = lean_usize_add(v_i_2413_, v___x_2433_);
v_i_2413_ = v___x_2434_;
v_b_2414_ = v_a_2432_;
goto _start;
}
else
{
return v___x_2431_;
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v___x_2428_);
lean_dec_ref(v_b_2414_);
v_a_2436_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2429_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2429_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2444_, lean_object* v_sz_2445_, lean_object* v_i_2446_, lean_object* v_b_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
size_t v_sz_boxed_2457_; size_t v_i_boxed_2458_; lean_object* v_res_2459_; 
v_sz_boxed_2457_ = lean_unbox_usize(v_sz_2445_);
lean_dec(v_sz_2445_);
v_i_boxed_2458_ = lean_unbox_usize(v_i_2446_);
lean_dec(v_i_2446_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2444_, v_sz_boxed_2457_, v_i_boxed_2458_, v_b_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v_as_2444_);
return v_res_2459_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_unsigned_to_nat(32u);
v___x_2466_ = lean_mk_empty_array_with_capacity(v___x_2465_);
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2468_ = ((size_t)5ULL);
v___x_2469_ = lean_unsigned_to_nat(0u);
v___x_2470_ = lean_unsigned_to_nat(32u);
v___x_2471_ = lean_mk_empty_array_with_capacity(v___x_2470_);
v___x_2472_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2473_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2471_);
lean_ctor_set(v___x_2473_, 2, v___x_2469_);
lean_ctor_set(v___x_2473_, 3, v___x_2469_);
lean_ctor_set_usize(v___x_2473_, 4, v___x_2468_);
return v___x_2473_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2475_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
lean_ctor_set(v___x_2476_, 2, v___x_2475_);
lean_ctor_set(v___x_2476_, 3, v___x_2474_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2478_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2488_, lean_object* v_stx_2489_, uint8_t v___x_2490_, lean_object* v___x_2491_, lean_object* v___x_2492_, lean_object* v___x_2493_, lean_object* v___f_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
if (v___x_2488_ == 0)
{
lean_object* v___x_2504_; 
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_2504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2504_;
}
else
{
lean_object* v___x_2505_; lean_object* v_tk_2506_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2621_; uint8_t v___y_2622_; lean_object* v___y_2623_; uint8_t v___y_2624_; lean_object* v_stxForSuggestion_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; uint8_t v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; uint8_t v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; uint8_t v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; uint8_t v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; uint8_t v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; uint8_t v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; uint8_t v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; uint8_t v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; uint8_t v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; uint8_t v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; uint8_t v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; uint8_t v___y_2905_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; uint8_t v___y_2924_; uint8_t v___y_2925_; lean_object* v_stxForExecution_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; uint8_t v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; uint8_t v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; uint8_t v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; uint8_t v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; uint8_t v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; uint8_t v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; uint8_t v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; uint8_t v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; uint8_t v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; uint8_t v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; uint8_t v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; uint8_t v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; uint8_t v___y_3256_; lean_object* v_argsArray_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; uint8_t v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; uint8_t v___y_3415_; lean_object* v___y_3416_; lean_object* v_args_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___x_3436_; lean_object* v___y_3438_; lean_object* v___y_3439_; uint8_t v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v_o_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_bang_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_2505_ = lean_unsigned_to_nat(0u);
v_tk_2506_ = l_Lean_Syntax_getArg(v_stx_2489_, v___x_2505_);
v___x_3436_ = lean_unsigned_to_nat(1u);
v___x_3495_ = l_Lean_Syntax_getArg(v_stx_2489_, v___x_3436_);
v___x_3496_ = l_Lean_Syntax_isNone(v___x_3495_);
if (v___x_3496_ == 0)
{
uint8_t v___x_3497_; 
lean_inc(v___x_3495_);
v___x_3497_ = l_Lean_Syntax_matchesNull(v___x_3495_, v___x_3436_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
lean_dec(v___x_3495_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_3498_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3498_;
}
else
{
lean_object* v_bang_3499_; lean_object* v___x_3500_; 
v_bang_3499_ = l_Lean_Syntax_getArg(v___x_3495_, v___x_2505_);
lean_dec(v___x_3495_);
v___x_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3500_, 0, v_bang_3499_);
v_bang_3467_ = v___x_3500_;
v___y_3468_ = v___y_2495_;
v___y_3469_ = v___y_2496_;
v___y_3470_ = v___y_2497_;
v___y_3471_ = v___y_2498_;
v___y_3472_ = v___y_2499_;
v___y_3473_ = v___y_2500_;
v___y_3474_ = v___y_2501_;
v___y_3475_ = v___y_2502_;
goto v___jp_3466_;
}
}
else
{
lean_object* v___x_3501_; 
lean_dec(v___x_3495_);
v___x_3501_ = lean_box(0);
v_bang_3467_ = v___x_3501_;
v___y_3468_ = v___y_2495_;
v___y_3469_ = v___y_2496_;
v___y_3470_ = v___y_2497_;
v___y_3471_ = v___y_2498_;
v___y_3472_ = v___y_2499_;
v___y_3473_ = v___y_2500_;
v___y_3474_ = v___y_2501_;
v___y_3475_ = v___y_2502_;
goto v___jp_3466_;
}
v___jp_2507_:
{
lean_object* v_usedTheorems_2514_; lean_object* v_diag_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2557_; 
v_usedTheorems_2514_ = lean_ctor_get(v___y_2509_, 0);
v_diag_2515_ = lean_ctor_get(v___y_2509_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___y_2509_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2517_ = v___y_2509_;
v_isShared_2518_ = v_isSharedCheck_2557_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_diag_2515_);
lean_inc(v_usedTheorems_2514_);
lean_dec(v___y_2509_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2557_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2508_, v_usedTheorems_2514_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec_ref(v_usedTheorems_2514_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v_ref_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_ref_2521_ = lean_ctor_get(v___y_2512_, 2);
v___x_2522_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v_a_2520_);
lean_ctor_set(v___x_2517_, 0, v___x_2522_);
v___x_2524_ = v___x_2517_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_a_2520_);
v___x_2524_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
lean_ctor_set(v___x_2526_, 2, v___x_2525_);
lean_ctor_set(v___x_2526_, 3, v___x_2525_);
lean_ctor_set(v___x_2526_, 4, v___x_2525_);
lean_ctor_set(v___x_2526_, 5, v___x_2525_);
lean_inc(v_ref_2521_);
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_ref_2521_);
v___x_2528_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2529_ = 4;
v___x_2530_ = l_Lean_MessageData_nil;
v___x_2531_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2506_, v___x_2526_, v___x_2527_, v___x_2528_, v___x_2525_, v___x_2529_, v___x_2530_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v___x_2531_, 0);
lean_dec(v_unused_2539_);
v___x_2533_ = v___x_2531_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_dec(v___x_2531_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v_diag_2515_);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_diag_2515_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v_diag_2515_);
v_a_2540_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2531_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2531_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_del_object(v___x_2517_);
lean_dec_ref(v_diag_2515_);
lean_dec(v_tk_2506_);
v_a_2549_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2519_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2519_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
v___jp_2558_:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2564_, v___y_2560_, v___y_2561_, v___y_2565_, v___y_2563_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2570_ = l_Lean_Meta_simpAll(v_a_2568_, v___y_2566_, v___y_2559_, v___x_2569_, v___y_2560_, v___y_2561_, v___y_2565_, v___y_2563_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v_fst_2572_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v_fst_2572_ = lean_ctor_get(v_a_2571_, 0);
if (lean_obj_tag(v_fst_2572_) == 0)
{
lean_object* v_snd_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_snd_2573_ = lean_ctor_get(v_a_2571_, 1);
lean_inc(v_snd_2573_);
lean_dec(v_a_2571_);
v___x_2574_ = lean_box(0);
v___x_2575_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2574_, v___y_2564_, v___y_2560_, v___y_2561_, v___y_2565_, v___y_2563_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_dec_ref_known(v___x_2575_, 1);
v___y_2508_ = v___y_2562_;
v___y_2509_ = v_snd_2573_;
v___y_2510_ = v___y_2560_;
v___y_2511_ = v___y_2561_;
v___y_2512_ = v___y_2565_;
v___y_2513_ = v___y_2563_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_snd_2573_);
lean_dec(v___y_2562_);
lean_dec(v_tk_2506_);
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_snd_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2602_; 
lean_inc_ref(v_fst_2572_);
v_snd_2584_ = lean_ctor_get(v_a_2571_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_a_2571_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v_a_2571_, 0);
lean_dec(v_unused_2603_);
v___x_2586_ = v_a_2571_;
v_isShared_2587_ = v_isSharedCheck_2602_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_snd_2584_);
lean_dec(v_a_2571_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2602_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v_val_2588_ = lean_ctor_get(v_fst_2572_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v_fst_2572_, 1);
v___x_2589_ = lean_box(0);
if (v_isShared_2587_ == 0)
{
lean_ctor_set_tag(v___x_2586_, 1);
lean_ctor_set(v___x_2586_, 1, v___x_2589_);
lean_ctor_set(v___x_2586_, 0, v_val_2588_);
v___x_2591_ = v___x_2586_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_val_2588_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2591_, v___y_2564_, v___y_2560_, v___y_2561_, v___y_2565_, v___y_2563_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref_known(v___x_2592_, 1);
v___y_2508_ = v___y_2562_;
v___y_2509_ = v_snd_2584_;
v___y_2510_ = v___y_2560_;
v___y_2511_ = v___y_2561_;
v___y_2512_ = v___y_2565_;
v___y_2513_ = v___y_2563_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_snd_2584_);
lean_dec(v___y_2562_);
lean_dec(v_tk_2506_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v___y_2562_);
lean_dec(v_tk_2506_);
v_a_2604_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2570_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2570_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2559_);
lean_dec(v_tk_2506_);
v_a_2612_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2567_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2567_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
v___jp_2620_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2635_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2623_, v___x_2490_, v___y_2624_, v___x_2490_, v___x_2634_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2623_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
if (lean_obj_tag(v___y_2621_) == 0)
{
lean_object* v_ctx_2637_; lean_object* v_simprocs_2638_; 
v_ctx_2637_ = lean_ctor_get(v_a_2636_, 0);
lean_inc_ref(v_ctx_2637_);
v_simprocs_2638_ = lean_ctor_get(v_a_2636_, 1);
lean_inc_ref(v_simprocs_2638_);
lean_dec(v_a_2636_);
v___y_2559_ = v_simprocs_2638_;
v___y_2560_ = v___y_2630_;
v___y_2561_ = v___y_2631_;
v___y_2562_ = v_stxForSuggestion_2625_;
v___y_2563_ = v___y_2633_;
v___y_2564_ = v___y_2627_;
v___y_2565_ = v___y_2632_;
v___y_2566_ = v_ctx_2637_;
goto v___jp_2558_;
}
else
{
lean_dec_ref_known(v___y_2621_, 1);
if (v___y_2622_ == 0)
{
lean_object* v_ctx_2639_; lean_object* v_simprocs_2640_; 
v_ctx_2639_ = lean_ctor_get(v_a_2636_, 0);
lean_inc_ref(v_ctx_2639_);
v_simprocs_2640_ = lean_ctor_get(v_a_2636_, 1);
lean_inc_ref(v_simprocs_2640_);
lean_dec(v_a_2636_);
v___y_2559_ = v_simprocs_2640_;
v___y_2560_ = v___y_2630_;
v___y_2561_ = v___y_2631_;
v___y_2562_ = v_stxForSuggestion_2625_;
v___y_2563_ = v___y_2633_;
v___y_2564_ = v___y_2627_;
v___y_2565_ = v___y_2632_;
v___y_2566_ = v_ctx_2639_;
goto v___jp_2558_;
}
else
{
lean_object* v_ctx_2641_; lean_object* v_simprocs_2642_; lean_object* v___x_2643_; 
v_ctx_2641_ = lean_ctor_get(v_a_2636_, 0);
lean_inc_ref(v_ctx_2641_);
v_simprocs_2642_ = lean_ctor_get(v_a_2636_, 1);
lean_inc_ref(v_simprocs_2642_);
lean_dec(v_a_2636_);
v___x_2643_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2641_);
v___y_2559_ = v_simprocs_2642_;
v___y_2560_ = v___y_2630_;
v___y_2561_ = v___y_2631_;
v___y_2562_ = v_stxForSuggestion_2625_;
v___y_2563_ = v___y_2633_;
v___y_2564_ = v___y_2627_;
v___y_2565_ = v___y_2632_;
v___y_2566_ = v___x_2643_;
goto v___jp_2558_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_stxForSuggestion_2625_);
lean_dec(v___y_2621_);
lean_dec(v_tk_2506_);
v_a_2644_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2635_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2635_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
v___jp_2652_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_inc_ref_n(v___y_2670_, 2);
v___x_2674_ = l_Array_append___redArg(v___y_2670_, v___y_2673_);
lean_dec_ref(v___y_2673_);
lean_inc_n(v___y_2663_, 3);
lean_inc_n(v___y_2671_, 5);
v___x_2675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___y_2671_);
lean_ctor_set(v___x_2675_, 1, v___y_2663_);
lean_ctor_set(v___x_2675_, 2, v___x_2674_);
v___x_2676_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2671_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2679_ = l_Lean_Syntax_SepArray_ofElems(v___x_2678_, v___y_2658_);
lean_dec_ref(v___y_2658_);
v___x_2680_ = l_Array_append___redArg(v___y_2670_, v___x_2679_);
lean_dec_ref(v___x_2679_);
v___x_2681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2681_, 0, v___y_2671_);
lean_ctor_set(v___x_2681_, 1, v___y_2663_);
lean_ctor_set(v___x_2681_, 2, v___x_2680_);
v___x_2682_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2671_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = l_Lean_Syntax_node3(v___y_2671_, v___y_2663_, v___x_2677_, v___x_2681_, v___x_2683_);
v___x_2685_ = l_Lean_Syntax_node5(v___y_2671_, v___y_2655_, v___y_2664_, v___y_2661_, v___y_2666_, v___x_2675_, v___x_2684_);
v___y_2621_ = v___y_2665_;
v___y_2622_ = v___y_2657_;
v___y_2623_ = v___y_2669_;
v___y_2624_ = v___y_2662_;
v_stxForSuggestion_2625_ = v___x_2685_;
v___y_2626_ = v___y_2659_;
v___y_2627_ = v___y_2656_;
v___y_2628_ = v___y_2672_;
v___y_2629_ = v___y_2667_;
v___y_2630_ = v___y_2654_;
v___y_2631_ = v___y_2660_;
v___y_2632_ = v___y_2653_;
v___y_2633_ = v___y_2668_;
goto v___jp_2620_;
}
v___jp_2686_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc_ref(v___y_2704_);
v___x_2708_ = l_Array_append___redArg(v___y_2704_, v___y_2707_);
lean_dec_ref(v___y_2707_);
lean_inc(v___y_2698_);
lean_inc(v___y_2705_);
v___x_2709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___y_2705_);
lean_ctor_set(v___x_2709_, 1, v___y_2698_);
lean_ctor_set(v___x_2709_, 2, v___x_2708_);
if (lean_obj_tag(v___y_2697_) == 1)
{
lean_object* v_val_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_val_2710_ = lean_ctor_get(v___y_2697_, 0);
lean_inc(v_val_2710_);
lean_dec_ref_known(v___y_2697_, 1);
v___x_2711_ = l_Lean_SourceInfo_fromRef(v_val_2710_, v___x_2490_);
lean_dec(v_val_2710_);
v___x_2712_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Array_mkArray1___redArg(v___x_2713_);
v___y_2653_ = v___y_2687_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v___y_2689_;
v___y_2656_ = v___y_2690_;
v___y_2657_ = v___y_2691_;
v___y_2658_ = v___y_2692_;
v___y_2659_ = v___y_2693_;
v___y_2660_ = v___y_2694_;
v___y_2661_ = v___y_2695_;
v___y_2662_ = v___y_2696_;
v___y_2663_ = v___y_2698_;
v___y_2664_ = v___y_2699_;
v___y_2665_ = v___y_2700_;
v___y_2666_ = v___x_2709_;
v___y_2667_ = v___y_2701_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___x_2714_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2715_; 
lean_dec(v___y_2697_);
v___x_2715_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2653_ = v___y_2687_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v___y_2689_;
v___y_2656_ = v___y_2690_;
v___y_2657_ = v___y_2691_;
v___y_2658_ = v___y_2692_;
v___y_2659_ = v___y_2693_;
v___y_2660_ = v___y_2694_;
v___y_2661_ = v___y_2695_;
v___y_2662_ = v___y_2696_;
v___y_2663_ = v___y_2698_;
v___y_2664_ = v___y_2699_;
v___y_2665_ = v___y_2700_;
v___y_2666_ = v___x_2709_;
v___y_2667_ = v___y_2701_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___x_2715_;
goto v___jp_2652_;
}
}
v___jp_2716_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_inc_ref_n(v___y_2718_, 2);
v___x_2738_ = l_Array_append___redArg(v___y_2718_, v___y_2737_);
lean_dec_ref(v___y_2737_);
lean_inc_n(v___y_2736_, 3);
lean_inc_n(v___y_2717_, 5);
v___x_2739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2739_, 0, v___y_2717_);
lean_ctor_set(v___x_2739_, 1, v___y_2736_);
lean_ctor_set(v___x_2739_, 2, v___x_2738_);
v___x_2740_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___y_2717_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2743_ = l_Lean_Syntax_SepArray_ofElems(v___x_2742_, v___y_2723_);
lean_dec_ref(v___y_2723_);
v___x_2744_ = l_Array_append___redArg(v___y_2718_, v___x_2743_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2745_, 0, v___y_2717_);
lean_ctor_set(v___x_2745_, 1, v___y_2736_);
lean_ctor_set(v___x_2745_, 2, v___x_2744_);
v___x_2746_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___y_2717_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l_Lean_Syntax_node3(v___y_2717_, v___y_2736_, v___x_2741_, v___x_2745_, v___x_2747_);
v___x_2749_ = l_Lean_Syntax_node5(v___y_2717_, v___y_2725_, v___y_2734_, v___y_2727_, v___y_2729_, v___x_2739_, v___x_2748_);
v___y_2621_ = v___y_2730_;
v___y_2622_ = v___y_2722_;
v___y_2623_ = v___y_2733_;
v___y_2624_ = v___y_2728_;
v_stxForSuggestion_2625_ = v___x_2749_;
v___y_2626_ = v___y_2724_;
v___y_2627_ = v___y_2721_;
v___y_2628_ = v___y_2735_;
v___y_2629_ = v___y_2731_;
v___y_2630_ = v___y_2720_;
v___y_2631_ = v___y_2726_;
v___y_2632_ = v___y_2719_;
v___y_2633_ = v___y_2732_;
goto v___jp_2620_;
}
v___jp_2750_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_inc_ref(v___y_2752_);
v___x_2772_ = l_Array_append___redArg(v___y_2752_, v___y_2771_);
lean_dec_ref(v___y_2771_);
lean_inc(v___y_2770_);
lean_inc(v___y_2751_);
v___x_2773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2773_, 0, v___y_2751_);
lean_ctor_set(v___x_2773_, 1, v___y_2770_);
lean_ctor_set(v___x_2773_, 2, v___x_2772_);
if (lean_obj_tag(v___y_2763_) == 1)
{
lean_object* v_val_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_val_2774_ = lean_ctor_get(v___y_2763_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v___y_2763_, 1);
v___x_2775_ = l_Lean_SourceInfo_fromRef(v_val_2774_, v___x_2490_);
lean_dec(v_val_2774_);
v___x_2776_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Array_mkArray1___redArg(v___x_2777_);
v___y_2717_ = v___y_2751_;
v___y_2718_ = v___y_2752_;
v___y_2719_ = v___y_2753_;
v___y_2720_ = v___y_2754_;
v___y_2721_ = v___y_2755_;
v___y_2722_ = v___y_2756_;
v___y_2723_ = v___y_2757_;
v___y_2724_ = v___y_2758_;
v___y_2725_ = v___y_2759_;
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___x_2773_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___x_2778_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2779_; 
lean_dec(v___y_2763_);
v___x_2779_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2717_ = v___y_2751_;
v___y_2718_ = v___y_2752_;
v___y_2719_ = v___y_2753_;
v___y_2720_ = v___y_2754_;
v___y_2721_ = v___y_2755_;
v___y_2722_ = v___y_2756_;
v___y_2723_ = v___y_2757_;
v___y_2724_ = v___y_2758_;
v___y_2725_ = v___y_2759_;
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___x_2773_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___x_2779_;
goto v___jp_2716_;
}
}
v___jp_2780_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_inc_ref_n(v___y_2787_, 2);
v___x_2801_ = l_Array_append___redArg(v___y_2787_, v___y_2800_);
lean_dec_ref(v___y_2800_);
lean_inc_n(v___y_2793_, 2);
lean_inc_n(v___y_2781_, 2);
v___x_2802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2802_, 0, v___y_2781_);
lean_ctor_set(v___x_2802_, 1, v___y_2793_);
lean_ctor_set(v___x_2802_, 2, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2803_, 0, v___y_2781_);
lean_ctor_set(v___x_2803_, 1, v___y_2793_);
lean_ctor_set(v___x_2803_, 2, v___y_2787_);
v___x_2804_ = l_Lean_Syntax_node5(v___y_2781_, v___y_2796_, v___y_2798_, v___y_2790_, v___y_2782_, v___x_2802_, v___x_2803_);
v___y_2621_ = v___y_2792_;
v___y_2622_ = v___y_2786_;
v___y_2623_ = v___y_2797_;
v___y_2624_ = v___y_2791_;
v_stxForSuggestion_2625_ = v___x_2804_;
v___y_2626_ = v___y_2788_;
v___y_2627_ = v___y_2785_;
v___y_2628_ = v___y_2799_;
v___y_2629_ = v___y_2794_;
v___y_2630_ = v___y_2784_;
v___y_2631_ = v___y_2789_;
v___y_2632_ = v___y_2783_;
v___y_2633_ = v___y_2795_;
goto v___jp_2620_;
}
v___jp_2805_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_inc_ref(v___y_2811_);
v___x_2826_ = l_Array_append___redArg(v___y_2811_, v___y_2825_);
lean_dec_ref(v___y_2825_);
lean_inc(v___y_2817_);
lean_inc(v___y_2806_);
v___x_2827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2827_, 0, v___y_2806_);
lean_ctor_set(v___x_2827_, 1, v___y_2817_);
lean_ctor_set(v___x_2827_, 2, v___x_2826_);
if (lean_obj_tag(v___y_2816_) == 1)
{
lean_object* v_val_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_val_2828_ = lean_ctor_get(v___y_2816_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v___y_2816_, 1);
v___x_2829_ = l_Lean_SourceInfo_fromRef(v_val_2828_, v___x_2490_);
lean_dec(v_val_2828_);
v___x_2830_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Array_mkArray1___redArg(v___x_2831_);
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___x_2827_;
v___y_2783_ = v___y_2807_;
v___y_2784_ = v___y_2808_;
v___y_2785_ = v___y_2809_;
v___y_2786_ = v___y_2810_;
v___y_2787_ = v___y_2811_;
v___y_2788_ = v___y_2812_;
v___y_2789_ = v___y_2813_;
v___y_2790_ = v___y_2814_;
v___y_2791_ = v___y_2815_;
v___y_2792_ = v___y_2818_;
v___y_2793_ = v___y_2817_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2820_;
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___x_2832_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2833_; 
lean_dec(v___y_2816_);
v___x_2833_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___x_2827_;
v___y_2783_ = v___y_2807_;
v___y_2784_ = v___y_2808_;
v___y_2785_ = v___y_2809_;
v___y_2786_ = v___y_2810_;
v___y_2787_ = v___y_2811_;
v___y_2788_ = v___y_2812_;
v___y_2789_ = v___y_2813_;
v___y_2790_ = v___y_2814_;
v___y_2791_ = v___y_2815_;
v___y_2792_ = v___y_2818_;
v___y_2793_ = v___y_2817_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2820_;
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___x_2833_;
goto v___jp_2780_;
}
}
v___jp_2834_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_inc_ref_n(v___y_2842_, 2);
v___x_2855_ = l_Array_append___redArg(v___y_2842_, v___y_2854_);
lean_dec_ref(v___y_2854_);
lean_inc_n(v___y_2852_, 2);
lean_inc_n(v___y_2840_, 2);
v___x_2856_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2856_, 0, v___y_2840_);
lean_ctor_set(v___x_2856_, 1, v___y_2852_);
lean_ctor_set(v___x_2856_, 2, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2857_, 0, v___y_2840_);
lean_ctor_set(v___x_2857_, 1, v___y_2852_);
lean_ctor_set(v___x_2857_, 2, v___y_2842_);
v___x_2858_ = l_Lean_Syntax_node5(v___y_2840_, v___y_2845_, v___y_2835_, v___y_2846_, v___y_2841_, v___x_2856_, v___x_2857_);
v___y_2621_ = v___y_2848_;
v___y_2622_ = v___y_2839_;
v___y_2623_ = v___y_2851_;
v___y_2624_ = v___y_2847_;
v_stxForSuggestion_2625_ = v___x_2858_;
v___y_2626_ = v___y_2843_;
v___y_2627_ = v___y_2838_;
v___y_2628_ = v___y_2853_;
v___y_2629_ = v___y_2849_;
v___y_2630_ = v___y_2837_;
v___y_2631_ = v___y_2844_;
v___y_2632_ = v___y_2836_;
v___y_2633_ = v___y_2850_;
goto v___jp_2620_;
}
v___jp_2859_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_inc_ref(v___y_2866_);
v___x_2880_ = l_Array_append___redArg(v___y_2866_, v___y_2879_);
lean_dec_ref(v___y_2879_);
lean_inc(v___y_2878_);
lean_inc(v___y_2864_);
v___x_2881_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2881_, 0, v___y_2864_);
lean_ctor_set(v___x_2881_, 1, v___y_2878_);
lean_ctor_set(v___x_2881_, 2, v___x_2880_);
if (lean_obj_tag(v___y_2872_) == 1)
{
lean_object* v_val_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_val_2882_ = lean_ctor_get(v___y_2872_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v___y_2872_, 1);
v___x_2883_ = l_Lean_SourceInfo_fromRef(v_val_2882_, v___x_2490_);
lean_dec(v_val_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = l_Array_mkArray1___redArg(v___x_2885_);
v___y_2835_ = v___y_2860_;
v___y_2836_ = v___y_2861_;
v___y_2837_ = v___y_2862_;
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2865_;
v___y_2840_ = v___y_2864_;
v___y_2841_ = v___x_2881_;
v___y_2842_ = v___y_2866_;
v___y_2843_ = v___y_2867_;
v___y_2844_ = v___y_2868_;
v___y_2845_ = v___y_2869_;
v___y_2846_ = v___y_2870_;
v___y_2847_ = v___y_2871_;
v___y_2848_ = v___y_2873_;
v___y_2849_ = v___y_2874_;
v___y_2850_ = v___y_2875_;
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2878_;
v___y_2853_ = v___y_2877_;
v___y_2854_ = v___x_2886_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2887_; 
lean_dec(v___y_2872_);
v___x_2887_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2835_ = v___y_2860_;
v___y_2836_ = v___y_2861_;
v___y_2837_ = v___y_2862_;
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2865_;
v___y_2840_ = v___y_2864_;
v___y_2841_ = v___x_2881_;
v___y_2842_ = v___y_2866_;
v___y_2843_ = v___y_2867_;
v___y_2844_ = v___y_2868_;
v___y_2845_ = v___y_2869_;
v___y_2846_ = v___y_2870_;
v___y_2847_ = v___y_2871_;
v___y_2848_ = v___y_2873_;
v___y_2849_ = v___y_2874_;
v___y_2850_ = v___y_2875_;
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2878_;
v___y_2853_ = v___y_2877_;
v___y_2854_ = v___x_2887_;
goto v___jp_2834_;
}
}
v___jp_2888_:
{
lean_object* v_ref_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_ref_2906_ = lean_ctor_get(v___y_2889_, 2);
v___x_2907_ = l_Lean_SourceInfo_fromRef(v_ref_2906_, v___y_2905_);
v___x_2908_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2909_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_2908_);
v___x_2910_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_2911_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2914_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2899_) == 1)
{
lean_object* v_val_2915_; lean_object* v___x_2916_; 
v_val_2915_ = lean_ctor_get(v___y_2899_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v___y_2899_, 1);
v___x_2916_ = l_Array_mkArray1___redArg(v_val_2915_);
v___y_2687_ = v___y_2889_;
v___y_2688_ = v___y_2890_;
v___y_2689_ = v___x_2909_;
v___y_2690_ = v___y_2891_;
v___y_2691_ = v___y_2892_;
v___y_2692_ = v___y_2893_;
v___y_2693_ = v___y_2894_;
v___y_2694_ = v___y_2895_;
v___y_2695_ = v___y_2896_;
v___y_2696_ = v___y_2897_;
v___y_2697_ = v___y_2898_;
v___y_2698_ = v___x_2913_;
v___y_2699_ = v___x_2912_;
v___y_2700_ = v___y_2900_;
v___y_2701_ = v___y_2901_;
v___y_2702_ = v___y_2902_;
v___y_2703_ = v___y_2903_;
v___y_2704_ = v___x_2914_;
v___y_2705_ = v___x_2907_;
v___y_2706_ = v___y_2904_;
v___y_2707_ = v___x_2916_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2917_; 
lean_dec(v___y_2899_);
v___x_2917_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2687_ = v___y_2889_;
v___y_2688_ = v___y_2890_;
v___y_2689_ = v___x_2909_;
v___y_2690_ = v___y_2891_;
v___y_2691_ = v___y_2892_;
v___y_2692_ = v___y_2893_;
v___y_2693_ = v___y_2894_;
v___y_2694_ = v___y_2895_;
v___y_2695_ = v___y_2896_;
v___y_2696_ = v___y_2897_;
v___y_2697_ = v___y_2898_;
v___y_2698_ = v___x_2913_;
v___y_2699_ = v___x_2912_;
v___y_2700_ = v___y_2900_;
v___y_2701_ = v___y_2901_;
v___y_2702_ = v___y_2902_;
v___y_2703_ = v___y_2903_;
v___y_2704_ = v___x_2914_;
v___y_2705_ = v___x_2907_;
v___y_2706_ = v___y_2904_;
v___y_2707_ = v___x_2917_;
goto v___jp_2686_;
}
}
v___jp_2918_:
{
lean_object* v___x_2935_; lean_object* v_a_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2935_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2921_);
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
v___x_2937_ = lean_array_get_size(v___y_2923_);
v___x_2938_ = lean_nat_dec_eq(v___x_2937_, v___x_2505_);
if (v___x_2938_ == 0)
{
if (lean_obj_tag(v___y_2922_) == 0)
{
v___y_2889_ = v___y_2933_;
v___y_2890_ = v___y_2931_;
v___y_2891_ = v___y_2928_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2923_;
v___y_2894_ = v___y_2927_;
v___y_2895_ = v___y_2932_;
v___y_2896_ = v_a_2936_;
v___y_2897_ = v___y_2925_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2922_;
v___y_2901_ = v___y_2930_;
v___y_2902_ = v___y_2934_;
v___y_2903_ = v_stxForExecution_2926_;
v___y_2904_ = v___y_2929_;
v___y_2905_ = v___x_2938_;
goto v___jp_2888_;
}
else
{
if (v___y_2924_ == 0)
{
v___y_2889_ = v___y_2933_;
v___y_2890_ = v___y_2931_;
v___y_2891_ = v___y_2928_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2923_;
v___y_2894_ = v___y_2927_;
v___y_2895_ = v___y_2932_;
v___y_2896_ = v_a_2936_;
v___y_2897_ = v___y_2925_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2922_;
v___y_2901_ = v___y_2930_;
v___y_2902_ = v___y_2934_;
v___y_2903_ = v_stxForExecution_2926_;
v___y_2904_ = v___y_2929_;
v___y_2905_ = v___y_2924_;
goto v___jp_2888_;
}
else
{
lean_object* v_ref_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_ref_2939_ = lean_ctor_get(v___y_2933_, 2);
v___x_2940_ = l_Lean_SourceInfo_fromRef(v_ref_2939_, v___x_2938_);
v___x_2941_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2942_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_2941_);
v___x_2943_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_2944_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2947_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2920_) == 1)
{
lean_object* v_val_2948_; lean_object* v___x_2949_; 
v_val_2948_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_val_2948_);
lean_dec_ref_known(v___y_2920_, 1);
v___x_2949_ = l_Array_mkArray1___redArg(v_val_2948_);
v___y_2751_ = v___x_2940_;
v___y_2752_ = v___x_2947_;
v___y_2753_ = v___y_2933_;
v___y_2754_ = v___y_2931_;
v___y_2755_ = v___y_2928_;
v___y_2756_ = v___y_2924_;
v___y_2757_ = v___y_2923_;
v___y_2758_ = v___y_2927_;
v___y_2759_ = v___x_2942_;
v___y_2760_ = v___y_2932_;
v___y_2761_ = v_a_2936_;
v___y_2762_ = v___y_2925_;
v___y_2763_ = v___y_2919_;
v___y_2764_ = v___y_2922_;
v___y_2765_ = v___y_2930_;
v___y_2766_ = v___y_2934_;
v___y_2767_ = v_stxForExecution_2926_;
v___y_2768_ = v___x_2945_;
v___y_2769_ = v___y_2929_;
v___y_2770_ = v___x_2946_;
v___y_2771_ = v___x_2949_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2950_; 
lean_dec(v___y_2920_);
v___x_2950_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2751_ = v___x_2940_;
v___y_2752_ = v___x_2947_;
v___y_2753_ = v___y_2933_;
v___y_2754_ = v___y_2931_;
v___y_2755_ = v___y_2928_;
v___y_2756_ = v___y_2924_;
v___y_2757_ = v___y_2923_;
v___y_2758_ = v___y_2927_;
v___y_2759_ = v___x_2942_;
v___y_2760_ = v___y_2932_;
v___y_2761_ = v_a_2936_;
v___y_2762_ = v___y_2925_;
v___y_2763_ = v___y_2919_;
v___y_2764_ = v___y_2922_;
v___y_2765_ = v___y_2930_;
v___y_2766_ = v___y_2934_;
v___y_2767_ = v_stxForExecution_2926_;
v___y_2768_ = v___x_2945_;
v___y_2769_ = v___y_2929_;
v___y_2770_ = v___x_2946_;
v___y_2771_ = v___x_2950_;
goto v___jp_2750_;
}
}
}
}
else
{
lean_dec_ref(v___y_2923_);
if (lean_obj_tag(v___y_2922_) == 0)
{
lean_object* v_ref_2951_; uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_ref_2951_ = lean_ctor_get(v___y_2933_, 2);
v___x_2952_ = 0;
v___x_2953_ = l_Lean_SourceInfo_fromRef(v_ref_2951_, v___x_2952_);
v___x_2954_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2955_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_2954_);
v___x_2956_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_2957_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2960_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2920_) == 1)
{
lean_object* v_val_2961_; lean_object* v___x_2962_; 
v_val_2961_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_val_2961_);
lean_dec_ref_known(v___y_2920_, 1);
v___x_2962_ = l_Array_mkArray1___redArg(v_val_2961_);
v___y_2806_ = v___x_2953_;
v___y_2807_ = v___y_2933_;
v___y_2808_ = v___y_2931_;
v___y_2809_ = v___y_2928_;
v___y_2810_ = v___y_2924_;
v___y_2811_ = v___x_2960_;
v___y_2812_ = v___y_2927_;
v___y_2813_ = v___y_2932_;
v___y_2814_ = v_a_2936_;
v___y_2815_ = v___y_2925_;
v___y_2816_ = v___y_2919_;
v___y_2817_ = v___x_2959_;
v___y_2818_ = v___y_2922_;
v___y_2819_ = v___y_2930_;
v___y_2820_ = v___y_2934_;
v___y_2821_ = v___x_2955_;
v___y_2822_ = v_stxForExecution_2926_;
v___y_2823_ = v___x_2958_;
v___y_2824_ = v___y_2929_;
v___y_2825_ = v___x_2962_;
goto v___jp_2805_;
}
else
{
lean_object* v___x_2963_; 
lean_dec(v___y_2920_);
v___x_2963_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2806_ = v___x_2953_;
v___y_2807_ = v___y_2933_;
v___y_2808_ = v___y_2931_;
v___y_2809_ = v___y_2928_;
v___y_2810_ = v___y_2924_;
v___y_2811_ = v___x_2960_;
v___y_2812_ = v___y_2927_;
v___y_2813_ = v___y_2932_;
v___y_2814_ = v_a_2936_;
v___y_2815_ = v___y_2925_;
v___y_2816_ = v___y_2919_;
v___y_2817_ = v___x_2959_;
v___y_2818_ = v___y_2922_;
v___y_2819_ = v___y_2930_;
v___y_2820_ = v___y_2934_;
v___y_2821_ = v___x_2955_;
v___y_2822_ = v_stxForExecution_2926_;
v___y_2823_ = v___x_2958_;
v___y_2824_ = v___y_2929_;
v___y_2825_ = v___x_2963_;
goto v___jp_2805_;
}
}
else
{
lean_object* v_ref_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_ref_2964_ = lean_ctor_get(v___y_2933_, 2);
v___x_2965_ = 0;
v___x_2966_ = l_Lean_SourceInfo_fromRef(v_ref_2964_, v___x_2965_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2968_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_2967_);
v___x_2969_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2973_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2920_) == 1)
{
lean_object* v_val_2974_; lean_object* v___x_2975_; 
v_val_2974_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_val_2974_);
lean_dec_ref_known(v___y_2920_, 1);
v___x_2975_ = l_Array_mkArray1___redArg(v_val_2974_);
v___y_2860_ = v___x_2971_;
v___y_2861_ = v___y_2933_;
v___y_2862_ = v___y_2931_;
v___y_2863_ = v___y_2928_;
v___y_2864_ = v___x_2966_;
v___y_2865_ = v___y_2924_;
v___y_2866_ = v___x_2973_;
v___y_2867_ = v___y_2927_;
v___y_2868_ = v___y_2932_;
v___y_2869_ = v___x_2968_;
v___y_2870_ = v_a_2936_;
v___y_2871_ = v___y_2925_;
v___y_2872_ = v___y_2919_;
v___y_2873_ = v___y_2922_;
v___y_2874_ = v___y_2930_;
v___y_2875_ = v___y_2934_;
v___y_2876_ = v_stxForExecution_2926_;
v___y_2877_ = v___y_2929_;
v___y_2878_ = v___x_2972_;
v___y_2879_ = v___x_2975_;
goto v___jp_2859_;
}
else
{
lean_object* v___x_2976_; 
lean_dec(v___y_2920_);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2860_ = v___x_2971_;
v___y_2861_ = v___y_2933_;
v___y_2862_ = v___y_2931_;
v___y_2863_ = v___y_2928_;
v___y_2864_ = v___x_2966_;
v___y_2865_ = v___y_2924_;
v___y_2866_ = v___x_2973_;
v___y_2867_ = v___y_2927_;
v___y_2868_ = v___y_2932_;
v___y_2869_ = v___x_2968_;
v___y_2870_ = v_a_2936_;
v___y_2871_ = v___y_2925_;
v___y_2872_ = v___y_2919_;
v___y_2873_ = v___y_2922_;
v___y_2874_ = v___y_2930_;
v___y_2875_ = v___y_2934_;
v___y_2876_ = v_stxForExecution_2926_;
v___y_2877_ = v___y_2929_;
v___y_2878_ = v___x_2972_;
v___y_2879_ = v___x_2976_;
goto v___jp_2859_;
}
}
}
}
v___jp_2977_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_inc_ref_n(v___y_2982_, 2);
v___x_3000_ = l_Array_append___redArg(v___y_2982_, v___y_2999_);
lean_dec_ref(v___y_2999_);
lean_inc_n(v___y_2986_, 3);
lean_inc_n(v___y_2998_, 5);
v___x_3001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___y_2998_);
lean_ctor_set(v___x_3001_, 1, v___y_2986_);
lean_ctor_set(v___x_3001_, 2, v___x_3000_);
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___y_2998_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3005_ = l_Lean_Syntax_SepArray_ofElems(v___x_3004_, v___y_2984_);
v___x_3006_ = l_Array_append___redArg(v___y_2982_, v___x_3005_);
lean_dec_ref(v___x_3005_);
v___x_3007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3007_, 0, v___y_2998_);
lean_ctor_set(v___x_3007_, 1, v___y_2986_);
lean_ctor_set(v___x_3007_, 2, v___x_3006_);
v___x_3008_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___y_2998_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l_Lean_Syntax_node3(v___y_2998_, v___y_2986_, v___x_3003_, v___x_3007_, v___x_3009_);
lean_inc(v___y_2981_);
v___x_3011_ = l_Lean_Syntax_node5(v___y_2998_, v___y_2978_, v___y_2989_, v___y_2981_, v___y_2995_, v___x_3001_, v___x_3010_);
v___y_2919_ = v___y_2990_;
v___y_2920_ = v___y_2991_;
v___y_2921_ = v___y_2981_;
v___y_2922_ = v___y_2993_;
v___y_2923_ = v___y_2984_;
v___y_2924_ = v___y_2983_;
v___y_2925_ = v___y_2987_;
v_stxForExecution_2926_ = v___x_3011_;
v___y_2927_ = v___y_2985_;
v___y_2928_ = v___y_2988_;
v___y_2929_ = v___y_2994_;
v___y_2930_ = v___y_2997_;
v___y_2931_ = v___y_2979_;
v___y_2932_ = v___y_2996_;
v___y_2933_ = v___y_2992_;
v___y_2934_ = v___y_2980_;
goto v___jp_2918_;
}
v___jp_3012_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_inc_ref(v___y_3017_);
v___x_3034_ = l_Array_append___redArg(v___y_3017_, v___y_3033_);
lean_dec_ref(v___y_3033_);
lean_inc(v___y_3021_);
lean_inc(v___y_3032_);
v___x_3035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___y_3032_);
lean_ctor_set(v___x_3035_, 1, v___y_3021_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
if (lean_obj_tag(v___y_3025_) == 1)
{
lean_object* v_val_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_val_3036_ = lean_ctor_get(v___y_3025_, 0);
v___x_3037_ = l_Lean_SourceInfo_fromRef(v_val_3036_, v___x_2490_);
v___x_3038_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = l_Array_mkArray1___redArg(v___x_3039_);
v___y_2978_ = v___y_3013_;
v___y_2979_ = v___y_3014_;
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3016_;
v___y_2982_ = v___y_3017_;
v___y_2983_ = v___y_3018_;
v___y_2984_ = v___y_3019_;
v___y_2985_ = v___y_3020_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3025_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3029_;
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___x_3035_;
v___y_2996_ = v___y_3030_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3032_;
v___y_2999_ = v___x_3040_;
goto v___jp_2977_;
}
else
{
lean_object* v___x_3041_; 
v___x_3041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2978_ = v___y_3013_;
v___y_2979_ = v___y_3014_;
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3016_;
v___y_2982_ = v___y_3017_;
v___y_2983_ = v___y_3018_;
v___y_2984_ = v___y_3019_;
v___y_2985_ = v___y_3020_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3025_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3029_;
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___x_3035_;
v___y_2996_ = v___y_3030_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3032_;
v___y_2999_ = v___x_3041_;
goto v___jp_2977_;
}
}
v___jp_3042_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_inc_ref_n(v___y_3051_, 2);
v___x_3065_ = l_Array_append___redArg(v___y_3051_, v___y_3064_);
lean_dec_ref(v___y_3064_);
lean_inc_n(v___y_3062_, 3);
lean_inc_n(v___y_3060_, 5);
v___x_3066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3066_, 0, v___y_3060_);
lean_ctor_set(v___x_3066_, 1, v___y_3062_);
lean_ctor_set(v___x_3066_, 2, v___x_3065_);
v___x_3067_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___y_3060_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3070_ = l_Lean_Syntax_SepArray_ofElems(v___x_3069_, v___y_3049_);
v___x_3071_ = l_Array_append___redArg(v___y_3051_, v___x_3070_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3072_, 0, v___y_3060_);
lean_ctor_set(v___x_3072_, 1, v___y_3062_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
v___x_3073_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___y_3060_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = l_Lean_Syntax_node3(v___y_3060_, v___y_3062_, v___x_3068_, v___x_3072_, v___x_3074_);
lean_inc(v___y_3047_);
v___x_3076_ = l_Lean_Syntax_node5(v___y_3060_, v___y_3043_, v___y_3044_, v___y_3047_, v___y_3053_, v___x_3066_, v___x_3075_);
v___y_2919_ = v___y_3055_;
v___y_2920_ = v___y_3056_;
v___y_2921_ = v___y_3047_;
v___y_2922_ = v___y_3058_;
v___y_2923_ = v___y_3049_;
v___y_2924_ = v___y_3048_;
v___y_2925_ = v___y_3052_;
v_stxForExecution_2926_ = v___x_3076_;
v___y_2927_ = v___y_3050_;
v___y_2928_ = v___y_3054_;
v___y_2929_ = v___y_3059_;
v___y_2930_ = v___y_3063_;
v___y_2931_ = v___y_3045_;
v___y_2932_ = v___y_3061_;
v___y_2933_ = v___y_3057_;
v___y_2934_ = v___y_3046_;
goto v___jp_2918_;
}
v___jp_3077_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_inc_ref(v___y_3086_);
v___x_3099_ = l_Array_append___redArg(v___y_3086_, v___y_3098_);
lean_dec_ref(v___y_3098_);
lean_inc(v___y_3097_);
lean_inc(v___y_3094_);
v___x_3100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3100_, 0, v___y_3094_);
lean_ctor_set(v___x_3100_, 1, v___y_3097_);
lean_ctor_set(v___x_3100_, 2, v___x_3099_);
if (lean_obj_tag(v___y_3089_) == 1)
{
lean_object* v_val_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_val_3101_ = lean_ctor_get(v___y_3089_, 0);
v___x_3102_ = l_Lean_SourceInfo_fromRef(v_val_3101_, v___x_2490_);
v___x_3103_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Array_mkArray1___redArg(v___x_3104_);
v___y_3043_ = v___y_3078_;
v___y_3044_ = v___y_3079_;
v___y_3045_ = v___y_3080_;
v___y_3046_ = v___y_3081_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3083_;
v___y_3049_ = v___y_3084_;
v___y_3050_ = v___y_3085_;
v___y_3051_ = v___y_3086_;
v___y_3052_ = v___y_3087_;
v___y_3053_ = v___x_3100_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3093_;
v___y_3059_ = v___y_3092_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3097_;
v___y_3063_ = v___y_3096_;
v___y_3064_ = v___x_3105_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3106_; 
v___x_3106_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3043_ = v___y_3078_;
v___y_3044_ = v___y_3079_;
v___y_3045_ = v___y_3080_;
v___y_3046_ = v___y_3081_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3083_;
v___y_3049_ = v___y_3084_;
v___y_3050_ = v___y_3085_;
v___y_3051_ = v___y_3086_;
v___y_3052_ = v___y_3087_;
v___y_3053_ = v___x_3100_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3093_;
v___y_3059_ = v___y_3092_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3097_;
v___y_3063_ = v___y_3096_;
v___y_3064_ = v___x_3106_;
goto v___jp_3042_;
}
}
v___jp_3107_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_inc_ref_n(v___y_3117_, 2);
v___x_3130_ = l_Array_append___redArg(v___y_3117_, v___y_3129_);
lean_dec_ref(v___y_3129_);
lean_inc_n(v___y_3122_, 2);
lean_inc_n(v___y_3128_, 2);
v___x_3131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3131_, 0, v___y_3128_);
lean_ctor_set(v___x_3131_, 1, v___y_3122_);
lean_ctor_set(v___x_3131_, 2, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3128_);
lean_ctor_set(v___x_3132_, 1, v___y_3122_);
lean_ctor_set(v___x_3132_, 2, v___y_3117_);
lean_inc(v___y_3111_);
v___x_3133_ = l_Lean_Syntax_node5(v___y_3128_, v___y_3114_, v___y_3125_, v___y_3111_, v___y_3108_, v___x_3131_, v___x_3132_);
v___y_2919_ = v___y_3119_;
v___y_2920_ = v___y_3120_;
v___y_2921_ = v___y_3111_;
v___y_2922_ = v___y_3123_;
v___y_2923_ = v___y_3113_;
v___y_2924_ = v___y_3112_;
v___y_2925_ = v___y_3116_;
v_stxForExecution_2926_ = v___x_3133_;
v___y_2927_ = v___y_3115_;
v___y_2928_ = v___y_3118_;
v___y_2929_ = v___y_3124_;
v___y_2930_ = v___y_3127_;
v___y_2931_ = v___y_3109_;
v___y_2932_ = v___y_3126_;
v___y_2933_ = v___y_3121_;
v___y_2934_ = v___y_3110_;
goto v___jp_2918_;
}
v___jp_3134_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_inc_ref(v___y_3143_);
v___x_3156_ = l_Array_append___redArg(v___y_3143_, v___y_3155_);
lean_dec_ref(v___y_3155_);
lean_inc(v___y_3148_);
lean_inc(v___y_3154_);
v___x_3157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3157_, 0, v___y_3154_);
lean_ctor_set(v___x_3157_, 1, v___y_3148_);
lean_ctor_set(v___x_3157_, 2, v___x_3156_);
if (lean_obj_tag(v___y_3145_) == 1)
{
lean_object* v_val_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_val_3158_ = lean_ctor_get(v___y_3145_, 0);
v___x_3159_ = l_Lean_SourceInfo_fromRef(v_val_3158_, v___x_2490_);
v___x_3160_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = l_Array_mkArray1___redArg(v___x_3161_);
v___y_3108_ = v___x_3157_;
v___y_3109_ = v___y_3135_;
v___y_3110_ = v___y_3136_;
v___y_3111_ = v___y_3137_;
v___y_3112_ = v___y_3138_;
v___y_3113_ = v___y_3139_;
v___y_3114_ = v___y_3140_;
v___y_3115_ = v___y_3141_;
v___y_3116_ = v___y_3142_;
v___y_3117_ = v___y_3143_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3145_;
v___y_3120_ = v___y_3146_;
v___y_3121_ = v___y_3147_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3150_;
v___y_3124_ = v___y_3149_;
v___y_3125_ = v___y_3151_;
v___y_3126_ = v___y_3152_;
v___y_3127_ = v___y_3153_;
v___y_3128_ = v___y_3154_;
v___y_3129_ = v___x_3162_;
goto v___jp_3107_;
}
else
{
lean_object* v___x_3163_; 
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3108_ = v___x_3157_;
v___y_3109_ = v___y_3135_;
v___y_3110_ = v___y_3136_;
v___y_3111_ = v___y_3137_;
v___y_3112_ = v___y_3138_;
v___y_3113_ = v___y_3139_;
v___y_3114_ = v___y_3140_;
v___y_3115_ = v___y_3141_;
v___y_3116_ = v___y_3142_;
v___y_3117_ = v___y_3143_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3145_;
v___y_3120_ = v___y_3146_;
v___y_3121_ = v___y_3147_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3150_;
v___y_3124_ = v___y_3149_;
v___y_3125_ = v___y_3151_;
v___y_3126_ = v___y_3152_;
v___y_3127_ = v___y_3153_;
v___y_3128_ = v___y_3154_;
v___y_3129_ = v___x_3163_;
goto v___jp_3107_;
}
}
v___jp_3164_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_inc_ref_n(v___y_3172_, 2);
v___x_3187_ = l_Array_append___redArg(v___y_3172_, v___y_3186_);
lean_dec_ref(v___y_3186_);
lean_inc_n(v___y_3173_, 2);
lean_inc_n(v___y_3184_, 2);
v___x_3188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3188_, 0, v___y_3184_);
lean_ctor_set(v___x_3188_, 1, v___y_3173_);
lean_ctor_set(v___x_3188_, 2, v___x_3187_);
v___x_3189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3189_, 0, v___y_3184_);
lean_ctor_set(v___x_3189_, 1, v___y_3173_);
lean_ctor_set(v___x_3189_, 2, v___y_3172_);
lean_inc(v___y_3167_);
v___x_3190_ = l_Lean_Syntax_node5(v___y_3184_, v___y_3179_, v___y_3170_, v___y_3167_, v___y_3174_, v___x_3188_, v___x_3189_);
v___y_2919_ = v___y_3177_;
v___y_2920_ = v___y_3178_;
v___y_2921_ = v___y_3167_;
v___y_2922_ = v___y_3181_;
v___y_2923_ = v___y_3169_;
v___y_2924_ = v___y_3168_;
v___y_2925_ = v___y_3175_;
v_stxForExecution_2926_ = v___x_3190_;
v___y_2927_ = v___y_3171_;
v___y_2928_ = v___y_3176_;
v___y_2929_ = v___y_3182_;
v___y_2930_ = v___y_3185_;
v___y_2931_ = v___y_3165_;
v___y_2932_ = v___y_3183_;
v___y_2933_ = v___y_3180_;
v___y_2934_ = v___y_3166_;
goto v___jp_2918_;
}
v___jp_3191_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_inc_ref(v___y_3199_);
v___x_3213_ = l_Array_append___redArg(v___y_3199_, v___y_3212_);
lean_dec_ref(v___y_3212_);
lean_inc(v___y_3200_);
lean_inc(v___y_3211_);
v___x_3214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3214_, 0, v___y_3211_);
lean_ctor_set(v___x_3214_, 1, v___y_3200_);
lean_ctor_set(v___x_3214_, 2, v___x_3213_);
if (lean_obj_tag(v___y_3203_) == 1)
{
lean_object* v_val_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_val_3215_ = lean_ctor_get(v___y_3203_, 0);
v___x_3216_ = l_Lean_SourceInfo_fromRef(v_val_3215_, v___x_2490_);
v___x_3217_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = l_Array_mkArray1___redArg(v___x_3218_);
v___y_3165_ = v___y_3192_;
v___y_3166_ = v___y_3193_;
v___y_3167_ = v___y_3194_;
v___y_3168_ = v___y_3195_;
v___y_3169_ = v___y_3196_;
v___y_3170_ = v___y_3197_;
v___y_3171_ = v___y_3198_;
v___y_3172_ = v___y_3199_;
v___y_3173_ = v___y_3200_;
v___y_3174_ = v___x_3214_;
v___y_3175_ = v___y_3201_;
v___y_3176_ = v___y_3202_;
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3204_;
v___y_3180_ = v___y_3206_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3207_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3210_;
v___y_3186_ = v___x_3219_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3165_ = v___y_3192_;
v___y_3166_ = v___y_3193_;
v___y_3167_ = v___y_3194_;
v___y_3168_ = v___y_3195_;
v___y_3169_ = v___y_3196_;
v___y_3170_ = v___y_3197_;
v___y_3171_ = v___y_3198_;
v___y_3172_ = v___y_3199_;
v___y_3173_ = v___y_3200_;
v___y_3174_ = v___x_3214_;
v___y_3175_ = v___y_3201_;
v___y_3176_ = v___y_3202_;
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3204_;
v___y_3180_ = v___y_3206_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3207_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3210_;
v___y_3186_ = v___x_3220_;
goto v___jp_3164_;
}
}
v___jp_3221_:
{
lean_object* v_ref_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_ref_3238_ = lean_ctor_get(v___y_3232_, 2);
v___x_3239_ = l_Lean_SourceInfo_fromRef(v_ref_3238_, v___y_3237_);
v___x_3240_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3241_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3240_);
v___x_3242_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_3243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3246_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3231_) == 1)
{
lean_object* v_val_3247_; lean_object* v___x_3248_; 
v_val_3247_ = lean_ctor_get(v___y_3231_, 0);
lean_inc(v_val_3247_);
v___x_3248_ = l_Array_mkArray1___redArg(v_val_3247_);
v___y_3013_ = v___x_3241_;
v___y_3014_ = v___y_3222_;
v___y_3015_ = v___y_3223_;
v___y_3016_ = v___y_3224_;
v___y_3017_ = v___x_3246_;
v___y_3018_ = v___y_3225_;
v___y_3019_ = v___y_3226_;
v___y_3020_ = v___y_3227_;
v___y_3021_ = v___x_3245_;
v___y_3022_ = v___y_3228_;
v___y_3023_ = v___y_3229_;
v___y_3024_ = v___x_3244_;
v___y_3025_ = v___y_3230_;
v___y_3026_ = v___y_3231_;
v___y_3027_ = v___y_3232_;
v___y_3028_ = v___y_3233_;
v___y_3029_ = v___y_3234_;
v___y_3030_ = v___y_3235_;
v___y_3031_ = v___y_3236_;
v___y_3032_ = v___x_3239_;
v___y_3033_ = v___x_3248_;
goto v___jp_3012_;
}
else
{
lean_object* v___x_3249_; 
v___x_3249_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3013_ = v___x_3241_;
v___y_3014_ = v___y_3222_;
v___y_3015_ = v___y_3223_;
v___y_3016_ = v___y_3224_;
v___y_3017_ = v___x_3246_;
v___y_3018_ = v___y_3225_;
v___y_3019_ = v___y_3226_;
v___y_3020_ = v___y_3227_;
v___y_3021_ = v___x_3245_;
v___y_3022_ = v___y_3228_;
v___y_3023_ = v___y_3229_;
v___y_3024_ = v___x_3244_;
v___y_3025_ = v___y_3230_;
v___y_3026_ = v___y_3231_;
v___y_3027_ = v___y_3232_;
v___y_3028_ = v___y_3233_;
v___y_3029_ = v___y_3234_;
v___y_3030_ = v___y_3235_;
v___y_3031_ = v___y_3236_;
v___y_3032_ = v___x_3239_;
v___y_3033_ = v___x_3249_;
goto v___jp_3012_;
}
}
v___jp_3250_:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = lean_array_get_size(v_argsArray_3257_);
v___x_3267_ = lean_nat_dec_eq(v___x_3266_, v___x_2505_);
if (v___x_3267_ == 0)
{
if (lean_obj_tag(v___y_3253_) == 0)
{
v___y_3222_ = v___y_3262_;
v___y_3223_ = v___y_3265_;
v___y_3224_ = v___y_3254_;
v___y_3225_ = v___y_3255_;
v___y_3226_ = v_argsArray_3257_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___y_3256_;
v___y_3229_ = v___y_3259_;
v___y_3230_ = v___y_3251_;
v___y_3231_ = v___y_3252_;
v___y_3232_ = v___y_3264_;
v___y_3233_ = v___y_3260_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3263_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v___x_3267_;
goto v___jp_3221_;
}
else
{
if (v___y_3255_ == 0)
{
v___y_3222_ = v___y_3262_;
v___y_3223_ = v___y_3265_;
v___y_3224_ = v___y_3254_;
v___y_3225_ = v___y_3255_;
v___y_3226_ = v_argsArray_3257_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___y_3256_;
v___y_3229_ = v___y_3259_;
v___y_3230_ = v___y_3251_;
v___y_3231_ = v___y_3252_;
v___y_3232_ = v___y_3264_;
v___y_3233_ = v___y_3260_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3263_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v___y_3255_;
goto v___jp_3221_;
}
else
{
lean_object* v_ref_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_ref_3268_ = lean_ctor_get(v___y_3264_, 2);
v___x_3269_ = l_Lean_SourceInfo_fromRef(v_ref_3268_, v___x_3267_);
v___x_3270_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3271_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3270_);
v___x_3272_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_3273_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3276_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3252_) == 1)
{
lean_object* v_val_3277_; lean_object* v___x_3278_; 
v_val_3277_ = lean_ctor_get(v___y_3252_, 0);
lean_inc(v_val_3277_);
v___x_3278_ = l_Array_mkArray1___redArg(v_val_3277_);
v___y_3078_ = v___x_3271_;
v___y_3079_ = v___x_3274_;
v___y_3080_ = v___y_3262_;
v___y_3081_ = v___y_3265_;
v___y_3082_ = v___y_3254_;
v___y_3083_ = v___y_3255_;
v___y_3084_ = v_argsArray_3257_;
v___y_3085_ = v___y_3258_;
v___y_3086_ = v___x_3276_;
v___y_3087_ = v___y_3256_;
v___y_3088_ = v___y_3259_;
v___y_3089_ = v___y_3251_;
v___y_3090_ = v___y_3252_;
v___y_3091_ = v___y_3264_;
v___y_3092_ = v___y_3260_;
v___y_3093_ = v___y_3253_;
v___y_3094_ = v___x_3269_;
v___y_3095_ = v___y_3263_;
v___y_3096_ = v___y_3261_;
v___y_3097_ = v___x_3275_;
v___y_3098_ = v___x_3278_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3279_; 
v___x_3279_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3078_ = v___x_3271_;
v___y_3079_ = v___x_3274_;
v___y_3080_ = v___y_3262_;
v___y_3081_ = v___y_3265_;
v___y_3082_ = v___y_3254_;
v___y_3083_ = v___y_3255_;
v___y_3084_ = v_argsArray_3257_;
v___y_3085_ = v___y_3258_;
v___y_3086_ = v___x_3276_;
v___y_3087_ = v___y_3256_;
v___y_3088_ = v___y_3259_;
v___y_3089_ = v___y_3251_;
v___y_3090_ = v___y_3252_;
v___y_3091_ = v___y_3264_;
v___y_3092_ = v___y_3260_;
v___y_3093_ = v___y_3253_;
v___y_3094_ = v___x_3269_;
v___y_3095_ = v___y_3263_;
v___y_3096_ = v___y_3261_;
v___y_3097_ = v___x_3275_;
v___y_3098_ = v___x_3279_;
goto v___jp_3077_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3253_) == 0)
{
lean_object* v_ref_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_ref_3280_ = lean_ctor_get(v___y_3264_, 2);
v___x_3281_ = 0;
v___x_3282_ = l_Lean_SourceInfo_fromRef(v_ref_3280_, v___x_3281_);
v___x_3283_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3284_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3283_);
v___x_3285_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3289_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3252_) == 1)
{
lean_object* v_val_3290_; lean_object* v___x_3291_; 
v_val_3290_ = lean_ctor_get(v___y_3252_, 0);
lean_inc(v_val_3290_);
v___x_3291_ = l_Array_mkArray1___redArg(v_val_3290_);
v___y_3135_ = v___y_3262_;
v___y_3136_ = v___y_3265_;
v___y_3137_ = v___y_3254_;
v___y_3138_ = v___y_3255_;
v___y_3139_ = v_argsArray_3257_;
v___y_3140_ = v___x_3284_;
v___y_3141_ = v___y_3258_;
v___y_3142_ = v___y_3256_;
v___y_3143_ = v___x_3289_;
v___y_3144_ = v___y_3259_;
v___y_3145_ = v___y_3251_;
v___y_3146_ = v___y_3252_;
v___y_3147_ = v___y_3264_;
v___y_3148_ = v___x_3288_;
v___y_3149_ = v___y_3260_;
v___y_3150_ = v___y_3253_;
v___y_3151_ = v___x_3287_;
v___y_3152_ = v___y_3263_;
v___y_3153_ = v___y_3261_;
v___y_3154_ = v___x_3282_;
v___y_3155_ = v___x_3291_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3135_ = v___y_3262_;
v___y_3136_ = v___y_3265_;
v___y_3137_ = v___y_3254_;
v___y_3138_ = v___y_3255_;
v___y_3139_ = v_argsArray_3257_;
v___y_3140_ = v___x_3284_;
v___y_3141_ = v___y_3258_;
v___y_3142_ = v___y_3256_;
v___y_3143_ = v___x_3289_;
v___y_3144_ = v___y_3259_;
v___y_3145_ = v___y_3251_;
v___y_3146_ = v___y_3252_;
v___y_3147_ = v___y_3264_;
v___y_3148_ = v___x_3288_;
v___y_3149_ = v___y_3260_;
v___y_3150_ = v___y_3253_;
v___y_3151_ = v___x_3287_;
v___y_3152_ = v___y_3263_;
v___y_3153_ = v___y_3261_;
v___y_3154_ = v___x_3282_;
v___y_3155_ = v___x_3292_;
goto v___jp_3134_;
}
}
else
{
lean_object* v_ref_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_ref_3293_ = lean_ctor_get(v___y_3264_, 2);
v___x_3294_ = 0;
v___x_3295_ = l_Lean_SourceInfo_fromRef(v_ref_3293_, v___x_3294_);
v___x_3296_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3297_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3296_);
v___x_3298_ = l_Lean_SourceInfo_fromRef(v_tk_2506_, v___x_2490_);
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3302_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3252_) == 1)
{
lean_object* v_val_3303_; lean_object* v___x_3304_; 
v_val_3303_ = lean_ctor_get(v___y_3252_, 0);
lean_inc(v_val_3303_);
v___x_3304_ = l_Array_mkArray1___redArg(v_val_3303_);
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3265_;
v___y_3194_ = v___y_3254_;
v___y_3195_ = v___y_3255_;
v___y_3196_ = v_argsArray_3257_;
v___y_3197_ = v___x_3300_;
v___y_3198_ = v___y_3258_;
v___y_3199_ = v___x_3302_;
v___y_3200_ = v___x_3301_;
v___y_3201_ = v___y_3256_;
v___y_3202_ = v___y_3259_;
v___y_3203_ = v___y_3251_;
v___y_3204_ = v___x_3297_;
v___y_3205_ = v___y_3252_;
v___y_3206_ = v___y_3264_;
v___y_3207_ = v___y_3260_;
v___y_3208_ = v___y_3253_;
v___y_3209_ = v___y_3263_;
v___y_3210_ = v___y_3261_;
v___y_3211_ = v___x_3295_;
v___y_3212_ = v___x_3304_;
goto v___jp_3191_;
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3265_;
v___y_3194_ = v___y_3254_;
v___y_3195_ = v___y_3255_;
v___y_3196_ = v_argsArray_3257_;
v___y_3197_ = v___x_3300_;
v___y_3198_ = v___y_3258_;
v___y_3199_ = v___x_3302_;
v___y_3200_ = v___x_3301_;
v___y_3201_ = v___y_3256_;
v___y_3202_ = v___y_3259_;
v___y_3203_ = v___y_3251_;
v___y_3204_ = v___x_3297_;
v___y_3205_ = v___y_3252_;
v___y_3206_ = v___y_3264_;
v___y_3207_ = v___y_3260_;
v___y_3208_ = v___y_3253_;
v___y_3209_ = v___y_3263_;
v___y_3210_ = v___y_3261_;
v___y_3211_ = v___x_3295_;
v___y_3212_ = v___x_3305_;
goto v___jp_3191_;
}
}
}
}
v___jp_3306_:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3312_, v___y_3310_, v___y_3320_, v___y_3309_, v___y_3321_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3325_ = l_Lean_LibrarySuggestions_select(v_a_3324_, v___y_3322_, v___y_3310_, v___y_3320_, v___y_3309_, v___y_3321_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; size_t v_sz_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v_sz_3327_ = lean_array_size(v_a_3326_);
v___x_3328_ = ((size_t)0ULL);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3326_, v_sz_3327_, v___x_3328_, v___y_3307_, v___y_3315_, v___y_3312_, v___y_3319_, v___y_3313_, v___y_3310_, v___y_3320_, v___y_3309_, v___y_3321_);
lean_dec(v_a_3326_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v___y_3251_ = v___y_3316_;
v___y_3252_ = v___y_3317_;
v___y_3253_ = v___y_3318_;
v___y_3254_ = v___y_3308_;
v___y_3255_ = v___y_3311_;
v___y_3256_ = v___y_3314_;
v_argsArray_3257_ = v_a_3330_;
v___y_3258_ = v___y_3315_;
v___y_3259_ = v___y_3312_;
v___y_3260_ = v___y_3319_;
v___y_3261_ = v___y_3313_;
v___y_3262_ = v___y_3310_;
v___y_3263_ = v___y_3320_;
v___y_3264_ = v___y_3309_;
v___y_3265_ = v___y_3321_;
goto v___jp_3250_;
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3308_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v_a_3331_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3329_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v_a_3339_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3325_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3325_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v_a_3347_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3323_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3323_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
v___jp_3355_:
{
lean_object* v_config_3372_; uint8_t v_suggestions_3373_; 
v_config_3372_ = lean_ctor_get(v___y_3359_, 0);
lean_inc_ref(v_config_3372_);
lean_dec_ref(v___y_3359_);
v_suggestions_3373_ = lean_ctor_get_uint8(v_config_3372_, sizeof(void*)*3 + 26);
if (v_suggestions_3373_ == 0)
{
lean_dec_ref(v_config_3372_);
lean_dec_ref(v___f_2494_);
v___y_3251_ = v___y_3365_;
v___y_3252_ = v___y_3366_;
v___y_3253_ = v___y_3367_;
v___y_3254_ = v___y_3356_;
v___y_3255_ = v___y_3360_;
v___y_3256_ = v___y_3363_;
v_argsArray_3257_ = v___y_3371_;
v___y_3258_ = v___y_3364_;
v___y_3259_ = v___y_3361_;
v___y_3260_ = v___y_3368_;
v___y_3261_ = v___y_3362_;
v___y_3262_ = v___y_3358_;
v___y_3263_ = v___y_3369_;
v___y_3264_ = v___y_3357_;
v___y_3265_ = v___y_3370_;
goto v___jp_3250_;
}
else
{
lean_object* v_maxSuggestions_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_maxSuggestions_3374_ = lean_ctor_get(v_config_3372_, 2);
lean_inc(v_maxSuggestions_3374_);
lean_dec_ref(v_config_3372_);
v___x_3375_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3376_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3374_) == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_unsigned_to_nat(100u);
v___x_3378_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v___x_3375_);
lean_ctor_set(v___x_3378_, 2, v___f_2494_);
lean_ctor_set(v___x_3378_, 3, v___x_3376_);
v___y_3307_ = v___y_3371_;
v___y_3308_ = v___y_3356_;
v___y_3309_ = v___y_3357_;
v___y_3310_ = v___y_3358_;
v___y_3311_ = v___y_3360_;
v___y_3312_ = v___y_3361_;
v___y_3313_ = v___y_3362_;
v___y_3314_ = v___y_3363_;
v___y_3315_ = v___y_3364_;
v___y_3316_ = v___y_3365_;
v___y_3317_ = v___y_3366_;
v___y_3318_ = v___y_3367_;
v___y_3319_ = v___y_3368_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___x_3378_;
goto v___jp_3306_;
}
else
{
lean_object* v_val_3379_; lean_object* v___x_3380_; 
v_val_3379_ = lean_ctor_get(v_maxSuggestions_3374_, 0);
lean_inc(v_val_3379_);
lean_dec_ref_known(v_maxSuggestions_3374_, 1);
v___x_3380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3380_, 0, v_val_3379_);
lean_ctor_set(v___x_3380_, 1, v___x_3375_);
lean_ctor_set(v___x_3380_, 2, v___f_2494_);
lean_ctor_set(v___x_3380_, 3, v___x_3376_);
v___y_3307_ = v___y_3371_;
v___y_3308_ = v___y_3356_;
v___y_3309_ = v___y_3357_;
v___y_3310_ = v___y_3358_;
v___y_3311_ = v___y_3360_;
v___y_3312_ = v___y_3361_;
v___y_3313_ = v___y_3362_;
v___y_3314_ = v___y_3363_;
v___y_3315_ = v___y_3364_;
v___y_3316_ = v___y_3365_;
v___y_3317_ = v___y_3366_;
v___y_3318_ = v___y_3367_;
v___y_3319_ = v___y_3368_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___x_3380_;
goto v___jp_3306_;
}
}
}
v___jp_3381_:
{
uint8_t v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = 1;
lean_inc(v___y_3382_);
v___x_3397_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3382_, v___x_3396_, v___y_3388_, v___y_3383_, v___y_3394_);
if (lean_obj_tag(v___x_3397_) == 0)
{
if (lean_obj_tag(v___y_3390_) == 1)
{
lean_object* v_a_3398_; lean_object* v_val_3399_; lean_object* v___x_3400_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v_val_3399_ = lean_ctor_get(v___y_3390_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v___y_3390_, 1);
v___x_3400_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3399_);
lean_dec(v_val_3399_);
v___y_3356_ = v___y_3382_;
v___y_3357_ = v___y_3383_;
v___y_3358_ = v___y_3384_;
v___y_3359_ = v_a_3398_;
v___y_3360_ = v___y_3385_;
v___y_3361_ = v___y_3386_;
v___y_3362_ = v___y_3387_;
v___y_3363_ = v___x_3396_;
v___y_3364_ = v___y_3388_;
v___y_3365_ = v___y_3389_;
v___y_3366_ = v___y_3395_;
v___y_3367_ = v___y_3391_;
v___y_3368_ = v___y_3392_;
v___y_3369_ = v___y_3393_;
v___y_3370_ = v___y_3394_;
v___y_3371_ = v___x_3400_;
goto v___jp_3355_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
lean_dec(v___y_3390_);
v_a_3401_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3397_, 1);
v___x_3402_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3356_ = v___y_3382_;
v___y_3357_ = v___y_3383_;
v___y_3358_ = v___y_3384_;
v___y_3359_ = v_a_3401_;
v___y_3360_ = v___y_3385_;
v___y_3361_ = v___y_3386_;
v___y_3362_ = v___y_3387_;
v___y_3363_ = v___x_3396_;
v___y_3364_ = v___y_3388_;
v___y_3365_ = v___y_3389_;
v___y_3366_ = v___y_3395_;
v___y_3367_ = v___y_3391_;
v___y_3368_ = v___y_3392_;
v___y_3369_ = v___y_3393_;
v___y_3370_ = v___y_3394_;
v___y_3371_ = v___x_3402_;
goto v___jp_3355_;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v___y_3395_);
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec(v___y_3382_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v_a_3403_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3397_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3397_);
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
v___jp_3411_:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_Syntax_getOptional_x3f(v___y_3416_);
lean_dec(v___y_3416_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_box(0);
v___y_3382_ = v___y_3414_;
v___y_3383_ = v___y_3424_;
v___y_3384_ = v___y_3422_;
v___y_3385_ = v___y_3415_;
v___y_3386_ = v___y_3419_;
v___y_3387_ = v___y_3421_;
v___y_3388_ = v___y_3418_;
v___y_3389_ = v___y_3412_;
v___y_3390_ = v_args_3417_;
v___y_3391_ = v___y_3413_;
v___y_3392_ = v___y_3420_;
v___y_3393_ = v___y_3423_;
v___y_3394_ = v___y_3425_;
v___y_3395_ = v___x_3427_;
goto v___jp_3381_;
}
else
{
lean_object* v_val_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_val_3428_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3426_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_val_3428_);
lean_dec(v___x_3426_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_val_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
v___y_3382_ = v___y_3414_;
v___y_3383_ = v___y_3424_;
v___y_3384_ = v___y_3422_;
v___y_3385_ = v___y_3415_;
v___y_3386_ = v___y_3419_;
v___y_3387_ = v___y_3421_;
v___y_3388_ = v___y_3418_;
v___y_3389_ = v___y_3412_;
v___y_3390_ = v_args_3417_;
v___y_3391_ = v___y_3413_;
v___y_3392_ = v___y_3420_;
v___y_3393_ = v___y_3423_;
v___y_3394_ = v___y_3425_;
v___y_3395_ = v___x_3433_;
goto v___jp_3381_;
}
}
}
}
v___jp_3437_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3452_ = lean_unsigned_to_nat(3u);
v___x_3453_ = l_Lean_Syntax_getArg(v___y_3442_, v___x_3452_);
lean_dec(v___y_3442_);
v___x_3454_ = l_Lean_Syntax_isNone(v___x_3453_);
if (v___x_3454_ == 0)
{
uint8_t v___x_3455_; 
lean_inc(v___x_3453_);
v___x_3455_ = l_Lean_Syntax_matchesNull(v___x_3453_, v___x_3436_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; 
lean_dec(v___x_3453_);
lean_dec(v_o_3443_);
lean_dec(v___y_3441_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_3456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3456_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; 
v___x_3457_ = l_Lean_Syntax_getArg(v___x_3453_, v___x_2505_);
lean_dec(v___x_3453_);
v___x_3458_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3459_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3458_);
lean_inc(v___x_3457_);
v___x_3460_ = l_Lean_Syntax_isOfKind(v___x_3457_, v___x_3459_);
lean_dec(v___x_3459_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; 
lean_dec(v___x_3457_);
lean_dec(v_o_3443_);
lean_dec(v___y_3441_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_3461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3461_;
}
else
{
lean_object* v___x_3462_; lean_object* v_args_3463_; lean_object* v___x_3464_; 
v___x_3462_ = l_Lean_Syntax_getArg(v___x_3457_, v___x_3436_);
lean_dec(v___x_3457_);
v_args_3463_ = l_Lean_Syntax_getArgs(v___x_3462_);
lean_dec(v___x_3462_);
v___x_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_args_3463_);
v___y_3412_ = v_o_3443_;
v___y_3413_ = v___y_3439_;
v___y_3414_ = v___y_3438_;
v___y_3415_ = v___y_3440_;
v___y_3416_ = v___y_3441_;
v_args_3417_ = v___x_3464_;
v___y_3418_ = v___y_3444_;
v___y_3419_ = v___y_3445_;
v___y_3420_ = v___y_3446_;
v___y_3421_ = v___y_3447_;
v___y_3422_ = v___y_3448_;
v___y_3423_ = v___y_3449_;
v___y_3424_ = v___y_3450_;
v___y_3425_ = v___y_3451_;
goto v___jp_3411_;
}
}
}
else
{
lean_object* v___x_3465_; 
lean_dec(v___x_3453_);
v___x_3465_ = lean_box(0);
v___y_3412_ = v_o_3443_;
v___y_3413_ = v___y_3439_;
v___y_3414_ = v___y_3438_;
v___y_3415_ = v___y_3440_;
v___y_3416_ = v___y_3441_;
v_args_3417_ = v___x_3465_;
v___y_3418_ = v___y_3444_;
v___y_3419_ = v___y_3445_;
v___y_3420_ = v___y_3446_;
v___y_3421_ = v___y_3447_;
v___y_3422_ = v___y_3448_;
v___y_3423_ = v___y_3449_;
v___y_3424_ = v___y_3450_;
v___y_3425_ = v___y_3451_;
goto v___jp_3411_;
}
}
v___jp_3466_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3476_ = lean_unsigned_to_nat(2u);
v___x_3477_ = l_Lean_Syntax_getArg(v_stx_2489_, v___x_3476_);
v___x_3478_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3479_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3478_);
lean_inc(v___x_3477_);
v___x_3480_ = l_Lean_Syntax_isOfKind(v___x_3477_, v___x_3479_);
lean_dec(v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___x_3477_);
lean_dec(v_bang_3467_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_3481_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3481_;
}
else
{
lean_object* v_cfg_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v_cfg_3482_ = l_Lean_Syntax_getArg(v___x_3477_, v___x_2505_);
v___x_3483_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2493_);
lean_inc_ref(v___x_2492_);
lean_inc_ref(v___x_2491_);
v___x_3484_ = l_Lean_Name_mkStr4(v___x_2491_, v___x_2492_, v___x_2493_, v___x_3483_);
lean_inc(v_cfg_3482_);
v___x_3485_ = l_Lean_Syntax_isOfKind(v_cfg_3482_, v___x_3484_);
lean_dec(v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec(v_cfg_3482_);
lean_dec(v___x_3477_);
lean_dec(v_bang_3467_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_3486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3487_ = l_Lean_Syntax_getArg(v___x_3477_, v___x_3436_);
v___x_3488_ = l_Lean_Syntax_getArg(v___x_3477_, v___x_3476_);
v___x_3489_ = l_Lean_Syntax_isNone(v___x_3488_);
if (v___x_3489_ == 0)
{
uint8_t v___x_3490_; 
lean_inc(v___x_3488_);
v___x_3490_ = l_Lean_Syntax_matchesNull(v___x_3488_, v___x_3436_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
lean_dec(v___x_3488_);
lean_dec(v___x_3487_);
lean_dec(v_cfg_3482_);
lean_dec(v___x_3477_);
lean_dec(v_bang_3467_);
lean_dec(v_tk_2506_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v___x_2491_);
v___x_3491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3491_;
}
else
{
lean_object* v_o_3492_; lean_object* v___x_3493_; 
v_o_3492_ = l_Lean_Syntax_getArg(v___x_3488_, v___x_2505_);
lean_dec(v___x_3488_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v_o_3492_);
v___y_3438_ = v_cfg_3482_;
v___y_3439_ = v_bang_3467_;
v___y_3440_ = v___x_3480_;
v___y_3441_ = v___x_3487_;
v___y_3442_ = v___x_3477_;
v_o_3443_ = v___x_3493_;
v___y_3444_ = v___y_3468_;
v___y_3445_ = v___y_3469_;
v___y_3446_ = v___y_3470_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v___y_3474_;
v___y_3451_ = v___y_3475_;
goto v___jp_3437_;
}
}
else
{
lean_object* v___x_3494_; 
lean_dec(v___x_3488_);
v___x_3494_ = lean_box(0);
v___y_3438_ = v_cfg_3482_;
v___y_3439_ = v_bang_3467_;
v___y_3440_ = v___x_3480_;
v___y_3441_ = v___x_3487_;
v___y_3442_ = v___x_3477_;
v_o_3443_ = v___x_3494_;
v___y_3444_ = v___y_3468_;
v___y_3445_ = v___y_3469_;
v___y_3446_ = v___y_3470_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3472_;
v___y_3449_ = v___y_3473_;
v___y_3450_ = v___y_3474_;
v___y_3451_ = v___y_3475_;
goto v___jp_3437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3502_, lean_object* v_stx_3503_, lean_object* v___x_3504_, lean_object* v___x_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v___f_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v___x_31073__boxed_3518_; uint8_t v___x_31074__boxed_3519_; lean_object* v_res_3520_; 
v___x_31073__boxed_3518_ = lean_unbox(v___x_3502_);
v___x_31074__boxed_3519_ = lean_unbox(v___x_3504_);
v_res_3520_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31073__boxed_3518_, v_stx_3503_, v___x_31074__boxed_3519_, v___x_3505_, v___x_3506_, v___x_3507_, v___f_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_stx_3503_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; uint8_t v___x_3542_; lean_object* v___f_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___y_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3527_);
v___x_3541_ = l_Lean_Syntax_isOfKind(v_stx_3527_, v___x_3540_);
v___x_3542_ = 1;
v___f_3543_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3544_ = lean_box(v___x_3541_);
v___x_3545_ = lean_box(v___x_3542_);
v___y_3546_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3546_, 0, v___x_3544_);
lean_closure_set(v___y_3546_, 1, v_stx_3527_);
lean_closure_set(v___y_3546_, 2, v___x_3545_);
lean_closure_set(v___y_3546_, 3, v___x_3537_);
lean_closure_set(v___y_3546_, 4, v___x_3538_);
lean_closure_set(v___y_3546_, 5, v___x_3539_);
lean_closure_set(v___y_3546_, 6, v___f_3543_);
v___x_3547_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3547_, 0, v___y_3546_);
v___x_3548_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3547_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3560_, lean_object* v_as_3561_, lean_object* v_as_x27_3562_, lean_object* v_b_3563_, lean_object* v_a_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3560_, v_as_x27_3562_, v_b_3563_, v___y_3571_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3575_, lean_object* v_as_3576_, lean_object* v_as_x27_3577_, lean_object* v_b_3578_, lean_object* v_a_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3575_, v_as_3576_, v_as_x27_3577_, v_b_3578_, v_a_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v_as_x27_3577_);
lean_dec(v_as_3576_);
lean_dec(v___x_3575_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3597_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3598_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3600_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3601_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3597_, v___x_3598_, v___x_3599_, v___x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3631_ = l_Lean_addBuiltinDeclarationRanges(v___x_3629_, v___x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3634_, lean_object* v_simprocs_3635_, lean_object* v_fvarIdsToSimp_3636_, uint8_t v_simplifyTarget_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = lean_unsigned_to_nat(32u);
v___x_3647_ = lean_mk_empty_array_with_capacity(v___x_3646_);
lean_dec_ref(v___x_3647_);
v___x_3648_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3649_ = l_Lean_Meta_dsimpGoal(v_a_3645_, v_ctx_3634_, v_simprocs_3635_, v_simplifyTarget_3637_, v_fvarIdsToSimp_3636_, v___x_3648_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v_fst_3651_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v_fst_3651_ = lean_ctor_get(v_a_3650_, 0);
if (lean_obj_tag(v_fst_3651_) == 0)
{
lean_object* v_snd_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_snd_3652_ = lean_ctor_get(v_a_3650_, 1);
lean_inc(v_snd_3652_);
lean_dec(v_a_3650_);
v___x_3653_ = lean_box(0);
v___x_3654_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3653_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; 
v_unused_3662_ = lean_ctor_get(v___x_3654_, 0);
lean_dec(v_unused_3662_);
v___x_3656_ = v___x_3654_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_dec(v___x_3654_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v_snd_3652_);
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_snd_3652_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v_snd_3652_);
v_a_3663_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3654_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3654_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v_snd_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3697_; 
lean_inc_ref(v_fst_3651_);
v_snd_3671_ = lean_ctor_get(v_a_3650_, 1);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; 
v_unused_3698_ = lean_ctor_get(v_a_3650_, 0);
lean_dec(v_unused_3698_);
v___x_3673_ = v_a_3650_;
v_isShared_3674_ = v_isSharedCheck_3697_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_snd_3671_);
lean_dec(v_a_3650_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3697_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_val_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
v_val_3675_ = lean_ctor_get(v_fst_3651_, 0);
lean_inc(v_val_3675_);
lean_dec_ref_known(v_fst_3651_, 1);
v___x_3676_ = lean_box(0);
if (v_isShared_3674_ == 0)
{
lean_ctor_set_tag(v___x_3673_, 1);
lean_ctor_set(v___x_3673_, 1, v___x_3676_);
lean_ctor_set(v___x_3673_, 0, v_val_3675_);
v___x_3678_ = v___x_3673_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_val_3675_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3678_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v___x_3679_, 0);
lean_dec(v_unused_3687_);
v___x_3681_ = v___x_3679_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v___x_3679_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v_snd_3671_);
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_snd_3671_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v_snd_3671_);
v_a_3688_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3679_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3679_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_a_3699_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3649_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3649_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v_fvarIdsToSimp_3636_);
lean_dec_ref(v_simprocs_3635_);
lean_dec_ref(v_ctx_3634_);
v_a_3707_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3644_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3644_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3715_, lean_object* v_simprocs_3716_, lean_object* v_fvarIdsToSimp_3717_, lean_object* v_simplifyTarget_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_){
_start:
{
uint8_t v_simplifyTarget_boxed_3725_; lean_object* v_res_3726_; 
v_simplifyTarget_boxed_3725_ = lean_unbox(v_simplifyTarget_3718_);
v_res_3726_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3715_, v_simprocs_3716_, v_fvarIdsToSimp_3717_, v_simplifyTarget_boxed_3725_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_a_3720_);
lean_dec(v_a_3719_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3727_, lean_object* v_simprocs_3728_, lean_object* v_fvarIdsToSimp_3729_, uint8_t v_simplifyTarget_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3727_, v_simprocs_3728_, v_fvarIdsToSimp_3729_, v_simplifyTarget_3730_, v_a_3732_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3741_, lean_object* v_simprocs_3742_, lean_object* v_fvarIdsToSimp_3743_, lean_object* v_simplifyTarget_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
uint8_t v_simplifyTarget_boxed_3754_; lean_object* v_res_3755_; 
v_simplifyTarget_boxed_3754_ = lean_unbox(v_simplifyTarget_3744_);
v_res_3755_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3741_, v_simprocs_3742_, v_fvarIdsToSimp_3743_, v_simplifyTarget_boxed_3754_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3756_, lean_object* v_simprocs_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3759_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___x_3769_ = l_Lean_MVarId_getNondepPropHyps(v_a_3768_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; uint8_t v___x_3771_; lean_object* v___x_3772_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v___x_3771_ = 1;
v___x_3772_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3756_, v_simprocs_3757_, v_a_3770_, v___x_3771_, v___y_3759_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
return v___x_3772_;
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v_simprocs_3757_);
lean_dec_ref(v_ctx_3756_);
v_a_3773_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3769_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3769_);
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
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v_simprocs_3757_);
lean_dec_ref(v_ctx_3756_);
v_a_3781_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3767_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3767_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3789_, lean_object* v_simprocs_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3789_, v_simprocs_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3801_, lean_object* v_ctx_3802_, lean_object* v_simprocs_3803_, uint8_t v_type_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3801_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3816_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3816_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3802_, v_simprocs_3803_, v_a_3815_, v_type_3804_, v___y_3806_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3816_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v_simprocs_3803_);
lean_dec_ref(v_ctx_3802_);
v_a_3817_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3814_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3814_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3825_, lean_object* v_ctx_3826_, lean_object* v_simprocs_3827_, lean_object* v_type_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
uint8_t v_type_638__boxed_3838_; lean_object* v_res_3839_; 
v_type_638__boxed_3838_ = lean_unbox(v_type_3828_);
v_res_3839_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3825_, v_ctx_3826_, v_simprocs_3827_, v_type_638__boxed_3838_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3840_, lean_object* v_simprocs_3841_, lean_object* v_loc_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_){
_start:
{
if (lean_obj_tag(v_loc_3842_) == 0)
{
lean_object* v___f_3852_; lean_object* v___x_3853_; 
v___f_3852_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3852_, 0, v_ctx_3840_);
lean_closure_set(v___f_3852_, 1, v_simprocs_3841_);
v___x_3853_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3852_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
return v___x_3853_;
}
else
{
lean_object* v_hypotheses_3854_; uint8_t v_type_3855_; lean_object* v___x_3856_; lean_object* v___f_3857_; lean_object* v___x_3858_; 
v_hypotheses_3854_ = lean_ctor_get(v_loc_3842_, 0);
lean_inc_ref(v_hypotheses_3854_);
v_type_3855_ = lean_ctor_get_uint8(v_loc_3842_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3842_, 1);
v___x_3856_ = lean_box(v_type_3855_);
v___f_3857_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3857_, 0, v_hypotheses_3854_);
lean_closure_set(v___f_3857_, 1, v_ctx_3840_);
lean_closure_set(v___f_3857_, 2, v_simprocs_3841_);
lean_closure_set(v___f_3857_, 3, v___x_3856_);
v___x_3858_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3857_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3859_, lean_object* v_simprocs_3860_, lean_object* v_loc_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3859_, v_simprocs_3860_, v_loc_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3876_, lean_object* v_stx_3877_, uint8_t v___x_3878_, lean_object* v___x_3879_, lean_object* v___x_3880_, lean_object* v___x_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
if (v___x_3876_ == 0)
{
lean_object* v___x_3891_; 
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_3891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; lean_object* v_tk_3893_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; uint8_t v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v_stx_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; uint8_t v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; uint8_t v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; uint8_t v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; uint8_t v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; uint8_t v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; uint8_t v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; uint8_t v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; uint8_t v___y_4198_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; uint8_t v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v_args_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___x_4274_; uint8_t v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v_o_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v_bang_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v_tk_3893_ = l_Lean_Syntax_getArg(v_stx_3877_, v___x_3892_);
v___x_4274_ = lean_unsigned_to_nat(1u);
v___x_4331_ = l_Lean_Syntax_getArg(v_stx_3877_, v___x_4274_);
v___x_4332_ = l_Lean_Syntax_isNone(v___x_4331_);
if (v___x_4332_ == 0)
{
uint8_t v___x_4333_; 
lean_inc(v___x_4331_);
v___x_4333_ = l_Lean_Syntax_matchesNull(v___x_4331_, v___x_4274_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_dec(v___x_4331_);
lean_dec(v_tk_3893_);
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_4334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4334_;
}
else
{
lean_object* v_bang_4335_; lean_object* v___x_4336_; 
v_bang_4335_ = l_Lean_Syntax_getArg(v___x_4331_, v___x_3892_);
lean_dec(v___x_4331_);
v___x_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4336_, 0, v_bang_4335_);
v_bang_4304_ = v___x_4336_;
v___y_4305_ = v___y_3882_;
v___y_4306_ = v___y_3883_;
v___y_4307_ = v___y_3884_;
v___y_4308_ = v___y_3885_;
v___y_4309_ = v___y_3886_;
v___y_4310_ = v___y_3887_;
v___y_4311_ = v___y_3888_;
v___y_4312_ = v___y_3889_;
goto v___jp_4303_;
}
}
else
{
lean_object* v___x_4337_; 
lean_dec(v___x_4331_);
v___x_4337_ = lean_box(0);
v_bang_4304_ = v___x_4337_;
v___y_4305_ = v___y_3882_;
v___y_4306_ = v___y_3883_;
v___y_4307_ = v___y_3884_;
v___y_4308_ = v___y_3885_;
v___y_4309_ = v___y_3886_;
v___y_4310_ = v___y_3887_;
v___y_4311_ = v___y_3888_;
v___y_4312_ = v___y_3889_;
goto v___jp_4303_;
}
v___jp_3894_:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3904_, v___y_3903_, v___y_3906_, v___y_3898_, v___y_3896_, v___y_3897_, v___y_3905_, v___y_3901_, v___y_3902_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v_usedTheorems_3909_; lean_object* v_diag_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3952_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v_usedTheorems_3909_ = lean_ctor_get(v_a_3908_, 0);
v_diag_3910_ = lean_ctor_get(v_a_3908_, 1);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_a_3908_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3912_ = v_a_3908_;
v_isShared_3913_ = v_isSharedCheck_3952_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_diag_3910_);
lean_inc(v_usedTheorems_3909_);
lean_dec(v_a_3908_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3952_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3895_, v_usedTheorems_3909_, v___y_3901_, v___y_3902_, v___y_3899_, v___y_3900_);
lean_dec_ref(v_usedTheorems_3909_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v_ref_3916_; lean_object* v___x_3917_; lean_object* v___x_3919_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v_ref_3916_ = lean_ctor_get(v___y_3899_, 2);
v___x_3917_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 1, v_a_3915_);
lean_ctor_set(v___x_3912_, 0, v___x_3917_);
v___x_3919_ = v___x_3912_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_a_3915_);
v___x_3919_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
lean_ctor_set(v___x_3921_, 2, v___x_3920_);
lean_ctor_set(v___x_3921_, 3, v___x_3920_);
lean_ctor_set(v___x_3921_, 4, v___x_3920_);
lean_ctor_set(v___x_3921_, 5, v___x_3920_);
lean_inc(v_ref_3916_);
v___x_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3922_, 0, v_ref_3916_);
v___x_3923_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3924_ = 4;
v___x_3925_ = l_Lean_MessageData_nil;
v___x_3926_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3893_, v___x_3921_, v___x_3922_, v___x_3923_, v___x_3920_, v___x_3924_, v___x_3925_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v___x_3926_, 0);
lean_dec(v_unused_3934_);
v___x_3928_ = v___x_3926_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_dec(v___x_3926_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v_diag_3910_);
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_diag_3910_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v_diag_3910_);
v_a_3935_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3926_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3926_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_del_object(v___x_3912_);
lean_dec_ref(v_diag_3910_);
lean_dec(v_tk_3893_);
v_a_3944_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3914_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3914_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec(v___y_3895_);
lean_dec(v_tk_3893_);
v_a_3953_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3907_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3907_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
v___jp_3961_:
{
if (lean_obj_tag(v___y_3966_) == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3975_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
lean_ctor_set_uint8(v___x_3975_, sizeof(void*)*1, v___x_3878_);
v___y_3895_ = v___y_3962_;
v___y_3896_ = v___y_3963_;
v___y_3897_ = v___y_3965_;
v___y_3898_ = v___y_3964_;
v___y_3899_ = v___y_3967_;
v___y_3900_ = v___y_3969_;
v___y_3901_ = v___y_3968_;
v___y_3902_ = v___y_3970_;
v___y_3903_ = v___y_3971_;
v___y_3904_ = v___y_3973_;
v___y_3905_ = v___y_3972_;
v___y_3906_ = v___x_3975_;
goto v___jp_3894_;
}
else
{
lean_object* v_val_3976_; lean_object* v___x_3977_; 
v_val_3976_ = lean_ctor_get(v___y_3966_, 0);
lean_inc(v_val_3976_);
lean_dec_ref_known(v___y_3966_, 1);
v___x_3977_ = l_Lean_Elab_Tactic_expandLocation(v_val_3976_);
lean_dec(v_val_3976_);
v___y_3895_ = v___y_3962_;
v___y_3896_ = v___y_3963_;
v___y_3897_ = v___y_3965_;
v___y_3898_ = v___y_3964_;
v___y_3899_ = v___y_3967_;
v___y_3900_ = v___y_3969_;
v___y_3901_ = v___y_3968_;
v___y_3902_ = v___y_3970_;
v___y_3903_ = v___y_3971_;
v___y_3904_ = v___y_3973_;
v___y_3905_ = v___y_3972_;
v___y_3906_ = v___x_3977_;
goto v___jp_3894_;
}
}
v___jp_3978_:
{
uint8_t v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3991_ = 0;
v___x_3992_ = 2;
v___x_3993_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_3994_ = lean_box(v___x_3991_);
v___x_3995_ = lean_box(v___x_3992_);
v___x_3996_ = lean_box(v___x_3991_);
lean_inc(v_stx_3982_);
v___x_3997_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3997_, 0, v_stx_3982_);
lean_closure_set(v___x_3997_, 1, v___x_3994_);
lean_closure_set(v___x_3997_, 2, v___x_3995_);
lean_closure_set(v___x_3997_, 3, v___x_3996_);
lean_closure_set(v___x_3997_, 4, v___x_3993_);
v___x_3998_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3997_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
if (lean_obj_tag(v___y_3981_) == 0)
{
lean_object* v_ctx_4000_; lean_object* v_simprocs_4001_; 
v_ctx_4000_ = lean_ctor_get(v_a_3999_, 0);
lean_inc_ref(v_ctx_4000_);
v_simprocs_4001_ = lean_ctor_get(v_a_3999_, 1);
lean_inc_ref(v_simprocs_4001_);
lean_dec(v_a_3999_);
v___y_3962_ = v_stx_3982_;
v___y_3963_ = v___y_3984_;
v___y_3964_ = v___y_3983_;
v___y_3965_ = v___y_3985_;
v___y_3966_ = v___y_3980_;
v___y_3967_ = v___y_3989_;
v___y_3968_ = v___y_3987_;
v___y_3969_ = v___y_3990_;
v___y_3970_ = v___y_3988_;
v___y_3971_ = v_simprocs_4001_;
v___y_3972_ = v___y_3986_;
v___y_3973_ = v_ctx_4000_;
goto v___jp_3961_;
}
else
{
lean_dec_ref_known(v___y_3981_, 1);
if (v___y_3979_ == 0)
{
lean_object* v_ctx_4002_; lean_object* v_simprocs_4003_; 
v_ctx_4002_ = lean_ctor_get(v_a_3999_, 0);
lean_inc_ref(v_ctx_4002_);
v_simprocs_4003_ = lean_ctor_get(v_a_3999_, 1);
lean_inc_ref(v_simprocs_4003_);
lean_dec(v_a_3999_);
v___y_3962_ = v_stx_3982_;
v___y_3963_ = v___y_3984_;
v___y_3964_ = v___y_3983_;
v___y_3965_ = v___y_3985_;
v___y_3966_ = v___y_3980_;
v___y_3967_ = v___y_3989_;
v___y_3968_ = v___y_3987_;
v___y_3969_ = v___y_3990_;
v___y_3970_ = v___y_3988_;
v___y_3971_ = v_simprocs_4003_;
v___y_3972_ = v___y_3986_;
v___y_3973_ = v_ctx_4002_;
goto v___jp_3961_;
}
else
{
lean_object* v_ctx_4004_; lean_object* v_simprocs_4005_; lean_object* v___x_4006_; 
v_ctx_4004_ = lean_ctor_get(v_a_3999_, 0);
lean_inc_ref(v_ctx_4004_);
v_simprocs_4005_ = lean_ctor_get(v_a_3999_, 1);
lean_inc_ref(v_simprocs_4005_);
lean_dec(v_a_3999_);
v___x_4006_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4004_);
v___y_3962_ = v_stx_3982_;
v___y_3963_ = v___y_3984_;
v___y_3964_ = v___y_3983_;
v___y_3965_ = v___y_3985_;
v___y_3966_ = v___y_3980_;
v___y_3967_ = v___y_3989_;
v___y_3968_ = v___y_3987_;
v___y_3969_ = v___y_3990_;
v___y_3970_ = v___y_3988_;
v___y_3971_ = v_simprocs_4005_;
v___y_3972_ = v___y_3986_;
v___y_3973_ = v___x_4006_;
goto v___jp_3961_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v_stx_3982_);
lean_dec(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec(v_tk_3893_);
v_a_4007_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3998_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3998_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
v___jp_4015_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_inc_ref(v___y_4034_);
v___x_4037_ = l_Array_append___redArg(v___y_4034_, v___y_4036_);
lean_dec_ref(v___y_4036_);
lean_inc(v___y_4029_);
lean_inc(v___y_4017_);
v___x_4038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4038_, 0, v___y_4017_);
lean_ctor_set(v___x_4038_, 1, v___y_4029_);
lean_ctor_set(v___x_4038_, 2, v___x_4037_);
v___x_4039_ = l_Lean_Syntax_node6(v___y_4017_, v___y_4016_, v___y_4030_, v___y_4031_, v___y_4035_, v___y_4020_, v___y_4033_, v___x_4038_);
v___y_3979_ = v___y_4027_;
v___y_3980_ = v___y_4032_;
v___y_3981_ = v___y_4025_;
v_stx_3982_ = v___x_4039_;
v___y_3983_ = v___y_4026_;
v___y_3984_ = v___y_4024_;
v___y_3985_ = v___y_4018_;
v___y_3986_ = v___y_4023_;
v___y_3987_ = v___y_4019_;
v___y_3988_ = v___y_4022_;
v___y_3989_ = v___y_4028_;
v___y_3990_ = v___y_4021_;
goto v___jp_3978_;
}
v___jp_4040_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_inc_ref(v___y_4059_);
v___x_4061_ = l_Array_append___redArg(v___y_4059_, v___y_4060_);
lean_dec_ref(v___y_4060_);
lean_inc(v___y_4055_);
lean_inc(v___y_4042_);
v___x_4062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4062_, 0, v___y_4042_);
lean_ctor_set(v___x_4062_, 1, v___y_4055_);
lean_ctor_set(v___x_4062_, 2, v___x_4061_);
if (lean_obj_tag(v___y_4057_) == 0)
{
lean_object* v___x_4063_; 
v___x_4063_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4016_ = v___y_4041_;
v___y_4017_ = v___y_4042_;
v___y_4018_ = v___y_4043_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4045_;
v___y_4021_ = v___y_4046_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4048_;
v___y_4024_ = v___y_4049_;
v___y_4025_ = v___y_4050_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4053_;
v___y_4028_ = v___y_4052_;
v___y_4029_ = v___y_4055_;
v___y_4030_ = v___y_4054_;
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___x_4062_;
v___y_4034_ = v___y_4059_;
v___y_4035_ = v___y_4058_;
v___y_4036_ = v___x_4063_;
goto v___jp_4015_;
}
else
{
lean_object* v_val_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_val_4064_ = lean_ctor_get(v___y_4057_, 0);
v___x_4065_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4064_);
v___x_4066_ = lean_array_push(v___x_4065_, v_val_4064_);
v___y_4016_ = v___y_4041_;
v___y_4017_ = v___y_4042_;
v___y_4018_ = v___y_4043_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4045_;
v___y_4021_ = v___y_4046_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4048_;
v___y_4024_ = v___y_4049_;
v___y_4025_ = v___y_4050_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4053_;
v___y_4028_ = v___y_4052_;
v___y_4029_ = v___y_4055_;
v___y_4030_ = v___y_4054_;
v___y_4031_ = v___y_4056_;
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___x_4062_;
v___y_4034_ = v___y_4059_;
v___y_4035_ = v___y_4058_;
v___y_4036_ = v___x_4066_;
goto v___jp_4015_;
}
}
v___jp_4067_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
lean_inc_ref(v___y_4086_);
v___x_4088_ = l_Array_append___redArg(v___y_4086_, v___y_4087_);
lean_dec_ref(v___y_4087_);
lean_inc(v___y_4081_);
lean_inc(v___y_4069_);
v___x_4089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4089_, 0, v___y_4069_);
lean_ctor_set(v___x_4089_, 1, v___y_4081_);
lean_ctor_set(v___x_4089_, 2, v___x_4088_);
if (lean_obj_tag(v___y_4084_) == 1)
{
lean_object* v_val_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_val_4090_ = lean_ctor_get(v___y_4084_, 0);
lean_inc(v_val_4090_);
lean_dec_ref_known(v___y_4084_, 1);
v___x_4091_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4069_, 3);
v___x_4092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___y_4069_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
lean_inc_ref(v___y_4086_);
v___x_4093_ = l_Array_append___redArg(v___y_4086_, v_val_4090_);
lean_dec(v_val_4090_);
lean_inc(v___y_4081_);
v___x_4094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4094_, 0, v___y_4069_);
lean_ctor_set(v___x_4094_, 1, v___y_4081_);
lean_ctor_set(v___x_4094_, 2, v___x_4093_);
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___y_4069_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = l_Array_mkArray3___redArg(v___x_4092_, v___x_4094_, v___x_4096_);
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___y_4070_;
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___x_4089_;
v___y_4046_ = v___y_4072_;
v___y_4047_ = v___y_4073_;
v___y_4048_ = v___y_4074_;
v___y_4049_ = v___y_4075_;
v___y_4050_ = v___y_4076_;
v___y_4051_ = v___y_4077_;
v___y_4052_ = v___y_4079_;
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4082_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4085_;
v___y_4059_ = v___y_4086_;
v___y_4060_ = v___x_4097_;
goto v___jp_4040_;
}
else
{
lean_object* v___x_4098_; 
lean_dec(v___y_4084_);
v___x_4098_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___y_4070_;
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___x_4089_;
v___y_4046_ = v___y_4072_;
v___y_4047_ = v___y_4073_;
v___y_4048_ = v___y_4074_;
v___y_4049_ = v___y_4075_;
v___y_4050_ = v___y_4076_;
v___y_4051_ = v___y_4077_;
v___y_4052_ = v___y_4079_;
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4082_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4085_;
v___y_4059_ = v___y_4086_;
v___y_4060_ = v___x_4098_;
goto v___jp_4040_;
}
}
v___jp_4099_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_inc_ref(v___y_4103_);
v___x_4121_ = l_Array_append___redArg(v___y_4103_, v___y_4120_);
lean_dec_ref(v___y_4120_);
lean_inc(v___y_4104_);
lean_inc(v___y_4106_);
v___x_4122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4122_, 0, v___y_4106_);
lean_ctor_set(v___x_4122_, 1, v___y_4104_);
lean_ctor_set(v___x_4122_, 2, v___x_4121_);
v___x_4123_ = l_Lean_Syntax_node6(v___y_4106_, v___y_4102_, v___y_4119_, v___y_4115_, v___y_4118_, v___y_4100_, v___y_4117_, v___x_4122_);
v___y_3979_ = v___y_4113_;
v___y_3980_ = v___y_4116_;
v___y_3981_ = v___y_4111_;
v_stx_3982_ = v___x_4123_;
v___y_3983_ = v___y_4112_;
v___y_3984_ = v___y_4110_;
v___y_3985_ = v___y_4101_;
v___y_3986_ = v___y_4109_;
v___y_3987_ = v___y_4105_;
v___y_3988_ = v___y_4108_;
v___y_3989_ = v___y_4114_;
v___y_3990_ = v___y_4107_;
goto v___jp_3978_;
}
v___jp_4124_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_inc_ref(v___y_4128_);
v___x_4145_ = l_Array_append___redArg(v___y_4128_, v___y_4144_);
lean_dec_ref(v___y_4144_);
lean_inc(v___y_4129_);
lean_inc(v___y_4130_);
v___x_4146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4146_, 0, v___y_4130_);
lean_ctor_set(v___x_4146_, 1, v___y_4129_);
lean_ctor_set(v___x_4146_, 2, v___x_4145_);
if (lean_obj_tag(v___y_4141_) == 0)
{
lean_object* v___x_4147_; 
v___x_4147_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4100_ = v___y_4125_;
v___y_4101_ = v___y_4126_;
v___y_4102_ = v___y_4127_;
v___y_4103_ = v___y_4128_;
v___y_4104_ = v___y_4129_;
v___y_4105_ = v___y_4131_;
v___y_4106_ = v___y_4130_;
v___y_4107_ = v___y_4132_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4137_;
v___y_4113_ = v___y_4139_;
v___y_4114_ = v___y_4138_;
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___x_4146_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4143_;
v___y_4120_ = v___x_4147_;
goto v___jp_4099_;
}
else
{
lean_object* v_val_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v_val_4148_ = lean_ctor_get(v___y_4141_, 0);
v___x_4149_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4148_);
v___x_4150_ = lean_array_push(v___x_4149_, v_val_4148_);
v___y_4100_ = v___y_4125_;
v___y_4101_ = v___y_4126_;
v___y_4102_ = v___y_4127_;
v___y_4103_ = v___y_4128_;
v___y_4104_ = v___y_4129_;
v___y_4105_ = v___y_4131_;
v___y_4106_ = v___y_4130_;
v___y_4107_ = v___y_4132_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4137_;
v___y_4113_ = v___y_4139_;
v___y_4114_ = v___y_4138_;
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___x_4146_;
v___y_4118_ = v___y_4142_;
v___y_4119_ = v___y_4143_;
v___y_4120_ = v___x_4150_;
goto v___jp_4099_;
}
}
v___jp_4151_:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_inc_ref(v___y_4154_);
v___x_4172_ = l_Array_append___redArg(v___y_4154_, v___y_4171_);
lean_dec_ref(v___y_4171_);
lean_inc(v___y_4155_);
lean_inc(v___y_4156_);
v___x_4173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4173_, 0, v___y_4156_);
lean_ctor_set(v___x_4173_, 1, v___y_4155_);
lean_ctor_set(v___x_4173_, 2, v___x_4172_);
if (lean_obj_tag(v___y_4168_) == 1)
{
lean_object* v_val_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v_val_4174_ = lean_ctor_get(v___y_4168_, 0);
lean_inc(v_val_4174_);
lean_dec_ref_known(v___y_4168_, 1);
v___x_4175_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4156_, 3);
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___y_4156_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
lean_inc_ref(v___y_4154_);
v___x_4177_ = l_Array_append___redArg(v___y_4154_, v_val_4174_);
lean_dec(v_val_4174_);
lean_inc(v___y_4155_);
v___x_4178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4178_, 0, v___y_4156_);
lean_ctor_set(v___x_4178_, 1, v___y_4155_);
lean_ctor_set(v___x_4178_, 2, v___x_4177_);
v___x_4179_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___y_4156_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = l_Array_mkArray3___redArg(v___x_4176_, v___x_4178_, v___x_4180_);
v___y_4125_ = v___x_4173_;
v___y_4126_ = v___y_4152_;
v___y_4127_ = v___y_4153_;
v___y_4128_ = v___y_4154_;
v___y_4129_ = v___y_4155_;
v___y_4130_ = v___y_4156_;
v___y_4131_ = v___y_4157_;
v___y_4132_ = v___y_4158_;
v___y_4133_ = v___y_4159_;
v___y_4134_ = v___y_4160_;
v___y_4135_ = v___y_4161_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___y_4163_;
v___y_4138_ = v___y_4165_;
v___y_4139_ = v___y_4164_;
v___y_4140_ = v___y_4166_;
v___y_4141_ = v___y_4167_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___x_4181_;
goto v___jp_4124_;
}
else
{
lean_object* v___x_4182_; 
lean_dec(v___y_4168_);
v___x_4182_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4125_ = v___x_4173_;
v___y_4126_ = v___y_4152_;
v___y_4127_ = v___y_4153_;
v___y_4128_ = v___y_4154_;
v___y_4129_ = v___y_4155_;
v___y_4130_ = v___y_4156_;
v___y_4131_ = v___y_4157_;
v___y_4132_ = v___y_4158_;
v___y_4133_ = v___y_4159_;
v___y_4134_ = v___y_4160_;
v___y_4135_ = v___y_4161_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___y_4163_;
v___y_4138_ = v___y_4165_;
v___y_4139_ = v___y_4164_;
v___y_4140_ = v___y_4166_;
v___y_4141_ = v___y_4167_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___x_4182_;
goto v___jp_4124_;
}
}
v___jp_4183_:
{
lean_object* v_ref_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_ref_4199_ = lean_ctor_get(v___y_4192_, 2);
v___x_4200_ = l_Lean_SourceInfo_fromRef(v_ref_4199_, v___y_4198_);
v___x_4201_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4202_ = l_Lean_Name_mkStr4(v___x_3879_, v___x_3880_, v___x_3881_, v___x_4201_);
v___x_4203_ = l_Lean_SourceInfo_fromRef(v_tk_3893_, v___x_3878_);
v___x_4204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set(v___x_4204_, 1, v___x_4201_);
v___x_4205_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4206_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4200_);
v___x_4207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4200_);
lean_ctor_set(v___x_4207_, 1, v___x_4205_);
lean_ctor_set(v___x_4207_, 2, v___x_4206_);
if (lean_obj_tag(v___y_4197_) == 1)
{
lean_object* v_val_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_val_4208_ = lean_ctor_get(v___y_4197_, 0);
lean_inc(v_val_4208_);
lean_dec_ref_known(v___y_4197_, 1);
v___x_4209_ = l_Lean_SourceInfo_fromRef(v_val_4208_, v___x_3878_);
lean_dec(v_val_4208_);
v___x_4210_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = l_Array_mkArray1___redArg(v___x_4211_);
v___y_4068_ = v___x_4202_;
v___y_4069_ = v___x_4200_;
v___y_4070_ = v___y_4184_;
v___y_4071_ = v___y_4185_;
v___y_4072_ = v___y_4186_;
v___y_4073_ = v___y_4187_;
v___y_4074_ = v___y_4188_;
v___y_4075_ = v___y_4189_;
v___y_4076_ = v___y_4190_;
v___y_4077_ = v___y_4191_;
v___y_4078_ = v___y_4193_;
v___y_4079_ = v___y_4192_;
v___y_4080_ = v___x_4204_;
v___y_4081_ = v___x_4205_;
v___y_4082_ = v___y_4194_;
v___y_4083_ = v___y_4195_;
v___y_4084_ = v___y_4196_;
v___y_4085_ = v___x_4207_;
v___y_4086_ = v___x_4206_;
v___y_4087_ = v___x_4212_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4213_; 
lean_dec(v___y_4197_);
v___x_4213_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4068_ = v___x_4202_;
v___y_4069_ = v___x_4200_;
v___y_4070_ = v___y_4184_;
v___y_4071_ = v___y_4185_;
v___y_4072_ = v___y_4186_;
v___y_4073_ = v___y_4187_;
v___y_4074_ = v___y_4188_;
v___y_4075_ = v___y_4189_;
v___y_4076_ = v___y_4190_;
v___y_4077_ = v___y_4191_;
v___y_4078_ = v___y_4193_;
v___y_4079_ = v___y_4192_;
v___y_4080_ = v___x_4204_;
v___y_4081_ = v___x_4205_;
v___y_4082_ = v___y_4194_;
v___y_4083_ = v___y_4195_;
v___y_4084_ = v___y_4196_;
v___y_4085_ = v___x_4207_;
v___y_4086_ = v___x_4206_;
v___y_4087_ = v___x_4213_;
goto v___jp_4067_;
}
}
v___jp_4214_:
{
if (lean_obj_tag(v___y_4221_) == 0)
{
uint8_t v___x_4229_; 
v___x_4229_ = 0;
v___y_4184_ = v___y_4215_;
v___y_4185_ = v___y_4216_;
v___y_4186_ = v___y_4217_;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4224_;
v___y_4193_ = v___y_4223_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4228_;
v___y_4196_ = v___y_4226_;
v___y_4197_ = v___y_4227_;
v___y_4198_ = v___x_4229_;
goto v___jp_4183_;
}
else
{
if (v___y_4223_ == 0)
{
v___y_4184_ = v___y_4215_;
v___y_4185_ = v___y_4216_;
v___y_4186_ = v___y_4217_;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4224_;
v___y_4193_ = v___y_4223_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4228_;
v___y_4196_ = v___y_4226_;
v___y_4197_ = v___y_4227_;
v___y_4198_ = v___y_4223_;
goto v___jp_4183_;
}
else
{
lean_object* v_ref_4230_; uint8_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_ref_4230_ = lean_ctor_get(v___y_4224_, 2);
v___x_4231_ = 0;
v___x_4232_ = l_Lean_SourceInfo_fromRef(v_ref_4230_, v___x_4231_);
v___x_4233_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4234_ = l_Lean_Name_mkStr4(v___x_3879_, v___x_3880_, v___x_3881_, v___x_4233_);
v___x_4235_ = l_Lean_SourceInfo_fromRef(v_tk_3893_, v___x_3878_);
v___x_4236_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4235_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4239_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4232_);
v___x_4240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4232_);
lean_ctor_set(v___x_4240_, 1, v___x_4238_);
lean_ctor_set(v___x_4240_, 2, v___x_4239_);
if (lean_obj_tag(v___y_4227_) == 1)
{
lean_object* v_val_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_val_4241_ = lean_ctor_get(v___y_4227_, 0);
lean_inc(v_val_4241_);
lean_dec_ref_known(v___y_4227_, 1);
v___x_4242_ = l_Lean_SourceInfo_fromRef(v_val_4241_, v___x_3878_);
lean_dec(v_val_4241_);
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4242_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = l_Array_mkArray1___redArg(v___x_4244_);
v___y_4152_ = v___y_4215_;
v___y_4153_ = v___x_4234_;
v___y_4154_ = v___x_4239_;
v___y_4155_ = v___x_4238_;
v___y_4156_ = v___x_4232_;
v___y_4157_ = v___y_4216_;
v___y_4158_ = v___y_4217_;
v___y_4159_ = v___y_4218_;
v___y_4160_ = v___y_4219_;
v___y_4161_ = v___y_4220_;
v___y_4162_ = v___y_4221_;
v___y_4163_ = v___y_4222_;
v___y_4164_ = v___y_4223_;
v___y_4165_ = v___y_4224_;
v___y_4166_ = v___y_4225_;
v___y_4167_ = v___y_4228_;
v___y_4168_ = v___y_4226_;
v___y_4169_ = v___x_4240_;
v___y_4170_ = v___x_4237_;
v___y_4171_ = v___x_4245_;
goto v___jp_4151_;
}
else
{
lean_object* v___x_4246_; 
lean_dec(v___y_4227_);
v___x_4246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4152_ = v___y_4215_;
v___y_4153_ = v___x_4234_;
v___y_4154_ = v___x_4239_;
v___y_4155_ = v___x_4238_;
v___y_4156_ = v___x_4232_;
v___y_4157_ = v___y_4216_;
v___y_4158_ = v___y_4217_;
v___y_4159_ = v___y_4218_;
v___y_4160_ = v___y_4219_;
v___y_4161_ = v___y_4220_;
v___y_4162_ = v___y_4221_;
v___y_4163_ = v___y_4222_;
v___y_4164_ = v___y_4223_;
v___y_4165_ = v___y_4224_;
v___y_4166_ = v___y_4225_;
v___y_4167_ = v___y_4228_;
v___y_4168_ = v___y_4226_;
v___y_4169_ = v___x_4240_;
v___y_4170_ = v___x_4237_;
v___y_4171_ = v___x_4246_;
goto v___jp_4151_;
}
}
}
}
v___jp_4247_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = lean_unsigned_to_nat(3u);
v___x_4263_ = l_Lean_Syntax_getArg(v___y_4250_, v___x_4262_);
lean_dec(v___y_4250_);
v___x_4264_ = l_Lean_Syntax_getOptional_x3f(v___x_4263_);
lean_dec(v___x_4263_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_box(0);
v___y_4215_ = v___y_4256_;
v___y_4216_ = v___y_4258_;
v___y_4217_ = v___y_4261_;
v___y_4218_ = v___y_4259_;
v___y_4219_ = v___y_4257_;
v___y_4220_ = v___y_4255_;
v___y_4221_ = v___y_4252_;
v___y_4222_ = v___y_4254_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v___y_4260_;
v___y_4225_ = v___y_4249_;
v___y_4226_ = v_args_4253_;
v___y_4227_ = v___y_4251_;
v___y_4228_ = v___x_4265_;
goto v___jp_4214_;
}
else
{
lean_object* v_val_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
v_val_4266_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4264_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_val_4266_);
lean_dec(v___x_4264_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_val_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
v___y_4215_ = v___y_4256_;
v___y_4216_ = v___y_4258_;
v___y_4217_ = v___y_4261_;
v___y_4218_ = v___y_4259_;
v___y_4219_ = v___y_4257_;
v___y_4220_ = v___y_4255_;
v___y_4221_ = v___y_4252_;
v___y_4222_ = v___y_4254_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v___y_4260_;
v___y_4225_ = v___y_4249_;
v___y_4226_ = v_args_4253_;
v___y_4227_ = v___y_4251_;
v___y_4228_ = v___x_4271_;
goto v___jp_4214_;
}
}
}
}
v___jp_4275_:
{
lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4290_ = l_Lean_Syntax_getArg(v___y_4279_, v___y_4277_);
v___x_4291_ = l_Lean_Syntax_isNone(v___x_4290_);
if (v___x_4291_ == 0)
{
uint8_t v___x_4292_; 
lean_inc(v___x_4290_);
v___x_4292_ = l_Lean_Syntax_matchesNull(v___x_4290_, v___x_4274_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
lean_dec(v___x_4290_);
lean_dec(v_o_4281_);
lean_dec(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec(v_tk_3893_);
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_4293_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4293_;
}
else
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4294_ = l_Lean_Syntax_getArg(v___x_4290_, v___x_3892_);
lean_dec(v___x_4290_);
v___x_4295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3881_);
lean_inc_ref(v___x_3880_);
lean_inc_ref(v___x_3879_);
v___x_4296_ = l_Lean_Name_mkStr4(v___x_3879_, v___x_3880_, v___x_3881_, v___x_4295_);
lean_inc(v___x_4294_);
v___x_4297_ = l_Lean_Syntax_isOfKind(v___x_4294_, v___x_4296_);
lean_dec(v___x_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; 
lean_dec(v___x_4294_);
lean_dec(v_o_4281_);
lean_dec(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec(v_tk_3893_);
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_4298_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4298_;
}
else
{
lean_object* v___x_4299_; lean_object* v_args_4300_; lean_object* v___x_4301_; 
v___x_4299_ = l_Lean_Syntax_getArg(v___x_4294_, v___x_4274_);
lean_dec(v___x_4294_);
v_args_4300_ = l_Lean_Syntax_getArgs(v___x_4299_);
lean_dec(v___x_4299_);
v___x_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4301_, 0, v_args_4300_);
v___y_4248_ = v___y_4276_;
v___y_4249_ = v___y_4278_;
v___y_4250_ = v___y_4279_;
v___y_4251_ = v_o_4281_;
v___y_4252_ = v___y_4280_;
v_args_4253_ = v___x_4301_;
v___y_4254_ = v___y_4282_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4284_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4286_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
goto v___jp_4247_;
}
}
}
else
{
lean_object* v___x_4302_; 
lean_dec(v___x_4290_);
v___x_4302_ = lean_box(0);
v___y_4248_ = v___y_4276_;
v___y_4249_ = v___y_4278_;
v___y_4250_ = v___y_4279_;
v___y_4251_ = v_o_4281_;
v___y_4252_ = v___y_4280_;
v_args_4253_ = v___x_4302_;
v___y_4254_ = v___y_4282_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4284_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4286_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
goto v___jp_4247_;
}
}
v___jp_4303_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4313_ = lean_unsigned_to_nat(2u);
v___x_4314_ = l_Lean_Syntax_getArg(v_stx_3877_, v___x_4313_);
v___x_4315_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3881_);
lean_inc_ref(v___x_3880_);
lean_inc_ref(v___x_3879_);
v___x_4316_ = l_Lean_Name_mkStr4(v___x_3879_, v___x_3880_, v___x_3881_, v___x_4315_);
lean_inc(v___x_4314_);
v___x_4317_ = l_Lean_Syntax_isOfKind(v___x_4314_, v___x_4316_);
lean_dec(v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; 
lean_dec(v___x_4314_);
lean_dec(v_bang_4304_);
lean_dec(v_tk_3893_);
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_4318_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4318_;
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4319_ = l_Lean_Syntax_getArg(v___x_4314_, v___x_3892_);
v___x_4320_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3881_);
lean_inc_ref(v___x_3880_);
lean_inc_ref(v___x_3879_);
v___x_4321_ = l_Lean_Name_mkStr4(v___x_3879_, v___x_3880_, v___x_3881_, v___x_4320_);
lean_inc(v___x_4319_);
v___x_4322_ = l_Lean_Syntax_isOfKind(v___x_4319_, v___x_4321_);
lean_dec(v___x_4321_);
if (v___x_4322_ == 0)
{
lean_object* v___x_4323_; 
lean_dec(v___x_4319_);
lean_dec(v___x_4314_);
lean_dec(v_bang_4304_);
lean_dec(v_tk_3893_);
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_4323_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4323_;
}
else
{
lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = l_Lean_Syntax_getArg(v___x_4314_, v___x_4274_);
v___x_4325_ = l_Lean_Syntax_isNone(v___x_4324_);
if (v___x_4325_ == 0)
{
uint8_t v___x_4326_; 
lean_inc(v___x_4324_);
v___x_4326_ = l_Lean_Syntax_matchesNull(v___x_4324_, v___x_4274_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; 
lean_dec(v___x_4324_);
lean_dec(v___x_4319_);
lean_dec(v___x_4314_);
lean_dec(v_bang_4304_);
lean_dec(v_tk_3893_);
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___x_3879_);
v___x_4327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4327_;
}
else
{
lean_object* v_o_4328_; lean_object* v___x_4329_; 
v_o_4328_ = l_Lean_Syntax_getArg(v___x_4324_, v___x_3892_);
lean_dec(v___x_4324_);
v___x_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4329_, 0, v_o_4328_);
v___y_4276_ = v___x_4317_;
v___y_4277_ = v___x_4313_;
v___y_4278_ = v___x_4319_;
v___y_4279_ = v___x_4314_;
v___y_4280_ = v_bang_4304_;
v_o_4281_ = v___x_4329_;
v___y_4282_ = v___y_4305_;
v___y_4283_ = v___y_4306_;
v___y_4284_ = v___y_4307_;
v___y_4285_ = v___y_4308_;
v___y_4286_ = v___y_4309_;
v___y_4287_ = v___y_4310_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4312_;
goto v___jp_4275_;
}
}
else
{
lean_object* v___x_4330_; 
lean_dec(v___x_4324_);
v___x_4330_ = lean_box(0);
v___y_4276_ = v___x_4317_;
v___y_4277_ = v___x_4313_;
v___y_4278_ = v___x_4319_;
v___y_4279_ = v___x_4314_;
v___y_4280_ = v_bang_4304_;
v_o_4281_ = v___x_4330_;
v___y_4282_ = v___y_4305_;
v___y_4283_ = v___y_4306_;
v___y_4284_ = v___y_4307_;
v___y_4285_ = v___y_4308_;
v___y_4286_ = v___y_4309_;
v___y_4287_ = v___y_4310_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4312_;
goto v___jp_4275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4338_, lean_object* v_stx_4339_, lean_object* v___x_4340_, lean_object* v___x_4341_, lean_object* v___x_4342_, lean_object* v___x_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
uint8_t v___x_8035__boxed_4353_; uint8_t v___x_8036__boxed_4354_; lean_object* v_res_4355_; 
v___x_8035__boxed_4353_ = lean_unbox(v___x_4338_);
v___x_8036__boxed_4354_ = lean_unbox(v___x_4340_);
v_res_4355_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8035__boxed_4353_, v_stx_4339_, v___x_8036__boxed_4354_, v___x_4341_, v___x_4342_, v___x_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v_stx_4339_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; uint8_t v___x_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___y_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4375_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4362_);
v___x_4376_ = l_Lean_Syntax_isOfKind(v_stx_4362_, v___x_4375_);
v___x_4377_ = 1;
v___x_4378_ = lean_box(v___x_4376_);
v___x_4379_ = lean_box(v___x_4377_);
v___y_4380_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4380_, 0, v___x_4378_);
lean_closure_set(v___y_4380_, 1, v_stx_4362_);
lean_closure_set(v___y_4380_, 2, v___x_4379_);
lean_closure_set(v___y_4380_, 3, v___x_4372_);
lean_closure_set(v___y_4380_, 4, v___x_4373_);
lean_closure_set(v___y_4380_, 5, v___x_4374_);
v___x_4381_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4381_, 0, v___y_4380_);
v___x_4382_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4381_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4401_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4402_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4401_, v___x_4402_, v___x_4403_, v___x_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4436_ = l_Lean_addBuiltinDeclarationRanges(v___x_4434_, v___x_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4438_;
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
