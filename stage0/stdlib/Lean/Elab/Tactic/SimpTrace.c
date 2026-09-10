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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simp_all!"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpAllTraceArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13_value;
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
uint8_t v___x_33339__boxed_208_; lean_object* v_res_209_; 
v___x_33339__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33339__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_33366__boxed_246_; lean_object* v_res_247_; 
v___x_33366__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33366__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
v___x_257_ = l_Array_mkArray0(lean_box(0));
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
lean_object* v_toCold_311_; lean_object* v_options_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_toCold_311_ = lean_ctor_get(v___y_309_, 0);
v_options_312_ = lean_ctor_get(v_toCold_311_, 2);
v___x_313_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_312_, v_opt_308_);
v___x_314_ = lean_box(v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(lean_object* v_opt_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_316_, v___y_317_);
lean_dec_ref(v___y_317_);
lean_dec_ref(v_opt_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; lean_object* v___x_328_; lean_object* v_toCold_329_; lean_object* v_mctx_330_; lean_object* v_lctx_331_; lean_object* v_options_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = lean_st_ref_get(v___y_322_);
v_toCold_329_ = lean_ctor_get(v___y_323_, 0);
v_mctx_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_mctx_330_);
lean_dec(v___x_328_);
v_lctx_331_ = lean_ctor_get(v___y_321_, 2);
v_options_332_ = lean_ctor_get(v_toCold_329_, 2);
lean_inc_ref(v_options_332_);
lean_inc_ref(v_lctx_331_);
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_env_327_);
lean_ctor_set(v___x_333_, 1, v_mctx_330_);
lean_ctor_set(v___x_333_, 2, v_lctx_331_);
lean_ctor_set(v___x_333_, 3, v_options_332_);
v___x_334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_msgData_320_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_350_, uint8_t v___y_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_352_) == 1)
{
lean_object* v_pre_353_; 
v_pre_353_ = lean_ctor_get(v_x_352_, 0);
switch(lean_obj_tag(v_pre_353_))
{
case 1:
{
lean_object* v_pre_354_; 
v_pre_354_ = lean_ctor_get(v_pre_353_, 0);
switch(lean_obj_tag(v_pre_354_))
{
case 0:
{
lean_object* v_str_355_; lean_object* v_str_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_str_355_ = lean_ctor_get(v_x_352_, 1);
v_str_356_ = lean_ctor_get(v_pre_353_, 1);
v___x_357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_358_ = lean_string_dec_eq(v_str_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_360_ = lean_string_dec_eq(v_str_356_, v___x_359_);
if (v___x_360_ == 0)
{
return v___x_360_;
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_362_ = lean_string_dec_eq(v_str_355_, v___x_361_);
if (v___x_362_ == 0)
{
return v___x_362_;
}
else
{
return v_suppressElabErrors_350_;
}
}
}
else
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_364_ = lean_string_dec_eq(v_str_355_, v___x_363_);
if (v___x_364_ == 0)
{
return v___x_364_;
}
else
{
return v_suppressElabErrors_350_;
}
}
}
case 1:
{
lean_object* v_pre_365_; 
v_pre_365_ = lean_ctor_get(v_pre_354_, 0);
if (lean_obj_tag(v_pre_365_) == 0)
{
lean_object* v_str_366_; lean_object* v_str_367_; lean_object* v_str_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_str_366_ = lean_ctor_get(v_x_352_, 1);
v_str_367_ = lean_ctor_get(v_pre_353_, 1);
v_str_368_ = lean_ctor_get(v_pre_354_, 1);
v___x_369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_370_ = lean_string_dec_eq(v_str_368_, v___x_369_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_372_ = lean_string_dec_eq(v_str_367_, v___x_371_);
if (v___x_372_ == 0)
{
return v___x_372_;
}
else
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_374_ = lean_string_dec_eq(v_str_366_, v___x_373_);
if (v___x_374_ == 0)
{
return v___x_374_;
}
else
{
return v_suppressElabErrors_350_;
}
}
}
}
else
{
return v___y_351_;
}
}
default: 
{
return v___y_351_;
}
}
}
case 0:
{
lean_object* v_str_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_str_375_ = lean_ctor_get(v_x_352_, 1);
v___x_376_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_377_ = lean_string_dec_eq(v_str_375_, v___x_376_);
if (v___x_377_ == 0)
{
return v___x_377_;
}
else
{
return v_suppressElabErrors_350_;
}
}
default: 
{
return v___y_351_;
}
}
}
else
{
return v___y_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_378_, lean_object* v___y_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_suppressElabErrors_boxed_381_; uint8_t v___y_33565__boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_suppressElabErrors_boxed_381_ = lean_unbox(v_suppressElabErrors_378_);
v___y_33565__boxed_382_ = lean_unbox(v___y_379_);
v_res_383_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_381_, v___y_33565__boxed_382_, v_x_380_);
lean_dec(v_x_380_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_386_, lean_object* v_msgData_387_, uint8_t v_severity_388_, uint8_t v_isSilent_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; uint8_t v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v___y_474_; uint8_t v___y_475_; uint8_t v___x_480_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; uint8_t v___y_490_; uint8_t v___x_506_; 
v___x_480_ = 2;
v___x_506_ = l_Lean_instBEqMessageSeverity_beq(v_severity_388_, v___x_480_);
if (v___x_506_ == 0)
{
v___y_490_ = v___x_506_;
goto v___jp_489_;
}
else
{
uint8_t v___x_507_; 
lean_inc_ref(v_msgData_387_);
v___x_507_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_387_);
v___y_490_ = v___x_507_;
goto v___jp_489_;
}
v___jp_395_:
{
lean_object* v___x_405_; lean_object* v_toCold_406_; lean_object* v_currNamespace_407_; lean_object* v_openDecls_408_; lean_object* v_env_409_; lean_object* v_nextMacroScope_410_; lean_object* v_ngen_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_traceState_413_; lean_object* v_cache_414_; lean_object* v_messages_415_; lean_object* v_infoState_416_; lean_object* v_snapshotTasks_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_431_; 
v___x_405_ = lean_st_ref_take(v___y_404_);
v_toCold_406_ = lean_ctor_get(v___y_403_, 0);
v_currNamespace_407_ = lean_ctor_get(v_toCold_406_, 4);
v_openDecls_408_ = lean_ctor_get(v_toCold_406_, 5);
v_env_409_ = lean_ctor_get(v___x_405_, 0);
v_nextMacroScope_410_ = lean_ctor_get(v___x_405_, 1);
v_ngen_411_ = lean_ctor_get(v___x_405_, 2);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_405_, 3);
v_traceState_413_ = lean_ctor_get(v___x_405_, 4);
v_cache_414_ = lean_ctor_get(v___x_405_, 5);
v_messages_415_ = lean_ctor_get(v___x_405_, 6);
v_infoState_416_ = lean_ctor_get(v___x_405_, 7);
v_snapshotTasks_417_ = lean_ctor_get(v___x_405_, 8);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_431_ == 0)
{
v___x_419_ = v___x_405_;
v_isShared_420_ = v_isSharedCheck_431_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snapshotTasks_417_);
lean_inc(v_infoState_416_);
lean_inc(v_messages_415_);
lean_inc(v_cache_414_);
lean_inc(v_traceState_413_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_ngen_411_);
lean_inc(v_nextMacroScope_410_);
lean_inc(v_env_409_);
lean_dec(v___x_405_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_431_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_inc(v_openDecls_408_);
lean_inc(v_currNamespace_407_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_currNamespace_407_);
lean_ctor_set(v___x_421_, 1, v_openDecls_408_);
v___x_422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___y_397_);
lean_inc_ref(v___y_396_);
lean_inc_ref(v___y_402_);
v___x_423_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_423_, 0, v___y_402_);
lean_ctor_set(v___x_423_, 1, v___y_399_);
lean_ctor_set(v___x_423_, 2, v___y_401_);
lean_ctor_set(v___x_423_, 3, v___y_396_);
lean_ctor_set(v___x_423_, 4, v___x_422_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5, v___y_400_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5 + 1, v___y_398_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5 + 2, v_isSilent_389_);
v___x_424_ = l_Lean_MessageLog_add(v___x_423_, v_messages_415_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 6, v___x_424_);
v___x_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_env_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_nextMacroScope_410_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_ngen_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_traceState_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_infoState_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_snapshotTasks_417_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_st_ref_put(v___y_404_, v___x_426_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
}
v___jp_432_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_456_; 
v___x_441_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_387_);
v___x_442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_441_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
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
lean_inc_ref_n(v___y_435_, 2);
v___x_447_ = l_Lean_FileMap_toPosition(v___y_435_, v___y_438_);
lean_dec(v___y_438_);
v___x_448_ = l_Lean_FileMap_toPosition(v___y_435_, v___y_440_);
lean_dec(v___y_440_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_436_ == 0)
{
lean_del_object(v___x_445_);
lean_dec_ref(v___y_433_);
v___y_396_ = v___x_450_;
v___y_397_ = v_a_443_;
v___y_398_ = v___y_434_;
v___y_399_ = v___x_447_;
v___y_400_ = v___y_437_;
v___y_401_ = v___x_449_;
v___y_402_ = v___y_439_;
v___y_403_ = v___y_392_;
v___y_404_ = v___y_393_;
goto v___jp_395_;
}
else
{
uint8_t v___x_451_; 
lean_inc(v_a_443_);
v___x_451_ = l_Lean_MessageData_hasTag(v___y_433_, v_a_443_);
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
v___y_396_ = v___x_450_;
v___y_397_ = v_a_443_;
v___y_398_ = v___y_434_;
v___y_399_ = v___x_447_;
v___y_400_ = v___y_437_;
v___y_401_ = v___x_449_;
v___y_402_ = v___y_439_;
v___y_403_ = v___y_392_;
v___y_404_ = v___y_393_;
goto v___jp_395_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Syntax_getTailPos_x3f(v___y_461_, v___y_463_);
lean_dec(v___y_461_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_inc(v___y_465_);
v___y_433_ = v___y_458_;
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_463_;
v___y_438_ = v___y_465_;
v___y_439_ = v___y_464_;
v___y_440_ = v___y_465_;
goto v___jp_432_;
}
else
{
lean_object* v_val_467_; 
v_val_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_466_, 1);
v___y_433_ = v___y_458_;
v___y_434_ = v___y_459_;
v___y_435_ = v___y_460_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_463_;
v___y_438_ = v___y_465_;
v___y_439_ = v___y_464_;
v___y_440_ = v_val_467_;
goto v___jp_432_;
}
}
v___jp_468_:
{
lean_object* v_ref_476_; lean_object* v___x_477_; 
v_ref_476_ = l_Lean_replaceRef(v_ref_386_, v___y_472_);
v___x_477_ = l_Lean_Syntax_getPos_x3f(v_ref_476_, v___y_473_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___y_458_ = v___y_469_;
v___y_459_ = v___y_475_;
v___y_460_ = v___y_470_;
v___y_461_ = v_ref_476_;
v___y_462_ = v___y_471_;
v___y_463_ = v___y_473_;
v___y_464_ = v___y_474_;
v___y_465_ = v___x_478_;
goto v___jp_457_;
}
else
{
lean_object* v_val_479_; 
v_val_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v___x_477_, 1);
v___y_458_ = v___y_469_;
v___y_459_ = v___y_475_;
v___y_460_ = v___y_470_;
v___y_461_ = v_ref_476_;
v___y_462_ = v___y_471_;
v___y_463_ = v___y_473_;
v___y_464_ = v___y_474_;
v___y_465_ = v_val_479_;
goto v___jp_457_;
}
}
v___jp_481_:
{
if (v___y_488_ == 0)
{
v___y_469_ = v___y_483_;
v___y_470_ = v___y_482_;
v___y_471_ = v___y_485_;
v___y_472_ = v___y_486_;
v___y_473_ = v___y_487_;
v___y_474_ = v___y_484_;
v___y_475_ = v_severity_388_;
goto v___jp_468_;
}
else
{
v___y_469_ = v___y_483_;
v___y_470_ = v___y_482_;
v___y_471_ = v___y_485_;
v___y_472_ = v___y_486_;
v___y_473_ = v___y_487_;
v___y_474_ = v___y_484_;
v___y_475_ = v___x_480_;
goto v___jp_468_;
}
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
lean_object* v_toCold_491_; lean_object* v_ref_492_; uint8_t v_suppressElabErrors_493_; lean_object* v_fileName_494_; lean_object* v_fileMap_495_; lean_object* v_options_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___f_499_; uint8_t v___x_500_; uint8_t v___x_501_; 
v_toCold_491_ = lean_ctor_get(v___y_392_, 0);
v_ref_492_ = lean_ctor_get(v___y_392_, 2);
v_suppressElabErrors_493_ = lean_ctor_get_uint8(v___y_392_, sizeof(void*)*3 + 1);
v_fileName_494_ = lean_ctor_get(v_toCold_491_, 0);
v_fileMap_495_ = lean_ctor_get(v_toCold_491_, 1);
v_options_496_ = lean_ctor_get(v_toCold_491_, 2);
v___x_497_ = lean_box(v_suppressElabErrors_493_);
v___x_498_ = lean_box(v___y_490_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_499_, 0, v___x_497_);
lean_closure_set(v___f_499_, 1, v___x_498_);
v___x_500_ = 1;
v___x_501_ = l_Lean_instBEqMessageSeverity_beq(v_severity_388_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_482_ = v_fileMap_495_;
v___y_483_ = v___f_499_;
v___y_484_ = v_fileName_494_;
v___y_485_ = v_suppressElabErrors_493_;
v___y_486_ = v_ref_492_;
v___y_487_ = v___y_490_;
v___y_488_ = v___x_501_;
goto v___jp_481_;
}
else
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = l_Lean_warningAsError;
v___x_503_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_496_, v___x_502_);
v___y_482_ = v_fileMap_495_;
v___y_483_ = v___f_499_;
v___y_484_ = v_fileName_494_;
v___y_485_ = v_suppressElabErrors_493_;
v___y_486_ = v_ref_492_;
v___y_487_ = v___y_490_;
v___y_488_ = v___x_503_;
goto v___jp_481_;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v_msgData_387_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_508_, lean_object* v_msgData_509_, lean_object* v_severity_510_, lean_object* v_isSilent_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v_severity_boxed_517_; uint8_t v_isSilent_boxed_518_; lean_object* v_res_519_; 
v_severity_boxed_517_ = lean_unbox(v_severity_510_);
v_isSilent_boxed_518_ = lean_unbox(v_isSilent_511_);
v_res_519_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_508_, v_msgData_509_, v_severity_boxed_517_, v_isSilent_boxed_518_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v_ref_508_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_520_, uint8_t v_severity_521_, uint8_t v_isSilent_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_ref_532_; lean_object* v___x_533_; 
v_ref_532_ = lean_ctor_get(v___y_529_, 2);
v___x_533_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_532_, v_msgData_520_, v_severity_521_, v_isSilent_522_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_534_, lean_object* v_severity_535_, lean_object* v_isSilent_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v_severity_boxed_546_; uint8_t v_isSilent_boxed_547_; lean_object* v_res_548_; 
v_severity_boxed_546_ = lean_unbox(v_severity_535_);
v_isSilent_boxed_547_ = lean_unbox(v_isSilent_536_);
v_res_548_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_534_, v_severity_boxed_546_, v_isSilent_boxed_547_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_559_ = 1;
v___x_560_ = 0;
v___x_561_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_549_, v___x_559_, v___x_560_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v_env_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_612_; 
v___x_589_ = lean_st_ref_get(v___y_587_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_589_);
v___x_591_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_592_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_591_, v___y_586_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v_isExporting_602_; 
v_isExporting_602_ = lean_ctor_get_uint8(v_env_590_, sizeof(void*)*8);
lean_dec_ref(v_env_590_);
if (v_isExporting_602_ == 0)
{
lean_dec(v_a_593_);
lean_dec(v_id_579_);
goto v___jp_597_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_isPrivateName(v_id_579_);
if (v___x_603_ == 0)
{
lean_dec(v_a_593_);
lean_dec(v_id_579_);
goto v___jp_597_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
if (v___x_604_ == 0)
{
lean_dec(v_id_579_);
goto v___jp_597_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_595_);
v___x_605_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_606_ = 0;
v___x_607_ = l_Lean_MessageData_ofConstName(v_id_579_, v___x_606_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_610_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_611_;
}
}
}
v___jp_597_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_box(0);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_624_, uint8_t v_enableLog_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_toCold_636_; lean_object* v_env_637_; lean_object* v_options_638_; lean_object* v_currNamespace_639_; lean_object* v_openDecls_640_; lean_object* v___x_641_; lean_object* v_env_642_; lean_object* v_res_643_; 
v___x_635_ = lean_st_ref_get(v___y_633_);
v_toCold_636_ = lean_ctor_get(v___y_632_, 0);
v_env_637_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_635_);
v_options_638_ = lean_ctor_get(v_toCold_636_, 2);
v_currNamespace_639_ = lean_ctor_get(v_toCold_636_, 4);
v_openDecls_640_ = lean_ctor_get(v_toCold_636_, 5);
v___x_641_ = lean_st_ref_get(v___y_633_);
v_env_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc_ref(v_env_642_);
lean_dec(v___x_641_);
lean_inc(v_openDecls_640_);
lean_inc(v_currNamespace_639_);
v_res_643_ = l_Lean_ResolveName_resolveGlobalName(v_env_637_, v_options_638_, v_currNamespace_639_, v_openDecls_640_, v_id_624_);
if (v_enableLog_625_ == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v_env_642_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v_res_643_);
return v___x_644_;
}
else
{
uint8_t v_isExporting_645_; 
v_isExporting_645_ = lean_ctor_get_uint8(v_env_642_, sizeof(void*)*8);
lean_dec_ref(v_env_642_);
if (v_isExporting_645_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_res_643_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_643_);
if (lean_obj_tag(v___x_647_) == 1)
{
lean_object* v_val_648_; lean_object* v_fst_649_; lean_object* v___x_650_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_647_, 1);
v_fst_649_ = lean_ctor_get(v_val_648_, 0);
lean_inc(v_fst_649_);
lean_dec(v_val_648_);
v___x_650_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_649_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_658_);
v___x_652_ = v___x_650_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_dec(v___x_650_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_res_643_);
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_res_643_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_res_643_);
v_a_659_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_650_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_650_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v___x_667_; 
lean_dec(v___x_647_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v_res_643_);
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_668_, lean_object* v_enableLog_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
uint8_t v_enableLog_boxed_679_; lean_object* v_res_680_; 
v_enableLog_boxed_679_ = lean_unbox(v_enableLog_669_);
v_res_680_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_668_, v_enableLog_boxed_679_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = l_List_reverse___redArg(v_a_682_);
return v___x_683_;
}
else
{
lean_object* v_head_684_; lean_object* v_tail_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_696_; 
v_head_684_ = lean_ctor_get(v_a_681_, 0);
v_tail_685_ = lean_ctor_get(v_a_681_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_696_ == 0)
{
v___x_687_ = v_a_681_;
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_tail_685_);
lean_inc(v_head_684_);
lean_dec(v_a_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_snd_689_; uint8_t v___x_690_; 
v_snd_689_ = lean_ctor_get(v_head_684_, 1);
v___x_690_ = l_List_isEmpty___redArg(v_snd_689_);
if (v___x_690_ == 0)
{
lean_del_object(v___x_687_);
lean_dec(v_head_684_);
v_a_681_ = v_tail_685_;
goto _start;
}
else
{
lean_object* v___x_693_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_a_682_);
v___x_693_ = v___x_687_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_head_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_682_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v_a_681_ = v_tail_685_;
v_a_682_ = v___x_693_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
if (lean_obj_tag(v_a_697_) == 0)
{
lean_object* v___x_699_; 
v___x_699_ = l_List_reverse___redArg(v_a_698_);
return v___x_699_;
}
else
{
lean_object* v_head_700_; lean_object* v_tail_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_710_; 
v_head_700_ = lean_ctor_get(v_a_697_, 0);
v_tail_701_ = lean_ctor_get(v_a_697_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_710_ == 0)
{
v___x_703_ = v_a_697_;
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_tail_701_);
lean_inc(v_head_700_);
lean_dec(v_a_697_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_fst_705_; lean_object* v___x_707_; 
v_fst_705_ = lean_ctor_get(v_head_700_, 0);
lean_inc(v_fst_705_);
lean_dec(v_head_700_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_a_698_);
lean_ctor_set(v___x_703_, 0, v_fst_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_fst_705_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_a_698_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
v_a_697_ = v_tail_701_;
v_a_698_ = v___x_707_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_ref_717_; lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_ref_717_ = lean_ctor_get(v___y_714_, 2);
v___x_718_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_inc(v_ref_717_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_ref_717_);
lean_ctor_set(v___x_723_, 1, v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 1);
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_735_, lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_toCold_746_; lean_object* v_currRecDepth_747_; lean_object* v_ref_748_; uint8_t v_diag_749_; uint8_t v_suppressElabErrors_750_; lean_object* v_ref_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_toCold_746_ = lean_ctor_get(v___y_743_, 0);
v_currRecDepth_747_ = lean_ctor_get(v___y_743_, 1);
v_ref_748_ = lean_ctor_get(v___y_743_, 2);
v_diag_749_ = lean_ctor_get_uint8(v___y_743_, sizeof(void*)*3);
v_suppressElabErrors_750_ = lean_ctor_get_uint8(v___y_743_, sizeof(void*)*3 + 1);
v_ref_751_ = l_Lean_replaceRef(v_ref_735_, v_ref_748_);
lean_inc(v_currRecDepth_747_);
lean_inc_ref(v_toCold_746_);
v___x_752_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_752_, 0, v_toCold_746_);
lean_ctor_set(v___x_752_, 1, v_currRecDepth_747_);
lean_ctor_set(v___x_752_, 2, v_ref_751_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*3, v_diag_749_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*3 + 1, v_suppressElabErrors_750_);
v___x_753_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_736_, v___y_741_, v___y_742_, v___x_752_, v___y_744_);
lean_dec_ref_known(v___x_752_, 3);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_754_, lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_754_, v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v_ref_754_);
return v_res_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_ctor_set(v___x_771_, 2, v___x_770_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
lean_ctor_set(v___x_771_, 4, v___x_769_);
lean_ctor_set(v___x_771_, 5, v___x_769_);
lean_ctor_set(v___x_771_, 6, v___x_769_);
lean_ctor_set(v___x_771_, 7, v___x_769_);
lean_ctor_set(v___x_771_, 8, v___x_769_);
lean_ctor_set(v___x_771_, 9, v___x_769_);
lean_ctor_set(v___x_771_, 10, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_unsigned_to_nat(32u);
v___x_773_ = lean_mk_empty_array_with_capacity(v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_775_ = ((size_t)5ULL);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_unsigned_to_nat(32u);
v___x_778_ = lean_mk_empty_array_with_capacity(v___x_777_);
v___x_779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_780_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_778_);
lean_ctor_set(v___x_780_, 2, v___x_776_);
lean_ctor_set(v___x_780_, 3, v___x_776_);
lean_ctor_set_usize(v___x_780_, 4, v___x_775_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_box(1);
v___x_782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
lean_ctor_set(v___x_784_, 2, v___x_781_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_806_, lean_object* v_declHint_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_env_811_; uint8_t v___x_812_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = l_Lean_Name_isAnonymous(v_declHint_807_);
if (v___x_812_ == 0)
{
uint8_t v_isExporting_813_; 
v_isExporting_813_ = lean_ctor_get_uint8(v_env_811_, sizeof(void*)*8);
if (v_isExporting_813_ == 0)
{
lean_object* v___x_814_; 
lean_dec_ref(v_env_811_);
lean_dec(v_declHint_807_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_msg_806_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; uint8_t v___x_816_; 
lean_inc_ref(v_env_811_);
v___x_815_ = l_Lean_Environment_setExporting(v_env_811_, v___x_812_);
lean_inc(v_declHint_807_);
lean_inc_ref(v___x_815_);
v___x_816_ = l_Lean_Environment_contains(v___x_815_, v_declHint_807_, v_isExporting_813_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec_ref(v___x_815_);
lean_dec_ref(v_env_811_);
lean_dec(v_declHint_807_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v_msg_806_);
return v___x_817_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_c_823_; lean_object* v___x_824_; 
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_820_ = l_Lean_Options_empty;
v___x_821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_821_, 0, v___x_815_);
lean_ctor_set(v___x_821_, 1, v___x_818_);
lean_ctor_set(v___x_821_, 2, v___x_819_);
lean_ctor_set(v___x_821_, 3, v___x_820_);
lean_inc(v_declHint_807_);
v___x_822_ = l_Lean_MessageData_ofConstName(v_declHint_807_, v___x_812_);
v_c_823_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_823_, 0, v___x_821_);
lean_ctor_set(v_c_823_, 1, v___x_822_);
v___x_824_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_811_, v_declHint_807_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v_env_811_);
lean_dec(v_declHint_807_);
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_c_823_);
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_MessageData_note(v___x_828_);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v_msg_806_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_867_; 
v_val_832_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_867_ == 0)
{
v___x_834_ = v___x_824_;
v_isShared_835_ = v_isSharedCheck_867_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v___x_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_867_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_mod_839_; uint8_t v___x_840_; 
v___x_836_ = lean_box(0);
v___x_837_ = l_Lean_Environment_header(v_env_811_);
lean_dec_ref(v_env_811_);
v___x_838_ = l_Lean_EnvironmentHeader_moduleNames(v___x_837_);
v_mod_839_ = lean_array_get(v___x_836_, v___x_838_, v_val_832_);
lean_dec(v_val_832_);
lean_dec_ref(v___x_838_);
v___x_840_ = l_Lean_isPrivateName(v_declHint_807_);
lean_dec(v_declHint_807_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_c_823_);
v___x_843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_MessageData_ofName(v_mod_839_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_MessageData_note(v___x_848_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v_msg_806_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_850_);
v___x_852_ = v___x_834_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_c_823_);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_MessageData_ofName(v_mod_839_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_MessageData_note(v___x_861_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v_msg_806_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_863_);
v___x_865_ = v___x_834_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_868_; 
lean_dec_ref(v_env_811_);
lean_dec(v_declHint_807_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_msg_806_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_869_, lean_object* v_declHint_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_869_, v_declHint_870_, v___y_871_);
lean_dec(v___y_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_874_, lean_object* v_declHint_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_895_; 
v___x_885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_874_, v_declHint_875_, v___y_883_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_895_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_890_ = l_Lean_unknownIdentifierMessageTag;
v___x_891_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_896_, lean_object* v_declHint_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_896_, v_declHint_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_908_, lean_object* v_msg_909_, lean_object* v_declHint_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_a_921_; lean_object* v___x_922_; 
v___x_920_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_909_, v_declHint_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_908_, v_a_921_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_923_, lean_object* v_msg_924_, lean_object* v_declHint_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_923_, v_msg_924_, v_declHint_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v_ref_923_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_942_, lean_object* v_constName_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_953_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_954_ = 0;
lean_inc(v_constName_943_);
v___x_955_ = l_Lean_MessageData_ofConstName(v_constName_943_, v___x_954_);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_953_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_942_, v___x_958_, v_constName_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_960_, lean_object* v_constName_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_960_, v_constName_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v_ref_960_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_972_, lean_object* v_cs_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; lean_object* v_cs_984_; uint8_t v___x_988_; 
v___x_983_ = lean_box(0);
v_cs_984_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_973_, v___x_983_);
v___x_988_ = l_List_isEmpty___redArg(v_cs_984_);
if (v___x_988_ == 0)
{
lean_dec(v_n_972_);
goto v___jp_985_;
}
else
{
lean_object* v_ref_989_; lean_object* v___x_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_cs_984_);
v_ref_989_ = lean_ctor_get(v___y_980_, 2);
v___x_990_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_989_, v_n_972_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
v___jp_985_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_984_, v___x_983_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_999_, lean_object* v_cs_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_999_, v_cs_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = 1;
lean_inc(v_n_1011_);
v___x_1022_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1011_, v___x_1021_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1011_, v_a_1023_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1024_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_n_1011_);
v_a_1025_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1022_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1022_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
if (lean_obj_tag(v_a_1044_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_array_to_list(v_a_1045_);
return v___x_1046_;
}
else
{
lean_object* v_head_1047_; 
v_head_1047_ = lean_ctor_get(v_a_1044_, 0);
if (lean_obj_tag(v_head_1047_) == 1)
{
lean_object* v_fields_1048_; 
v_fields_1048_ = lean_ctor_get(v_head_1047_, 1);
if (lean_obj_tag(v_fields_1048_) == 0)
{
lean_object* v_tail_1049_; lean_object* v_n_1050_; lean_object* v___x_1051_; 
lean_inc_ref(v_head_1047_);
v_tail_1049_ = lean_ctor_get(v_a_1044_, 1);
lean_inc(v_tail_1049_);
lean_dec_ref_known(v_a_1044_, 2);
v_n_1050_ = lean_ctor_get(v_head_1047_, 0);
lean_inc(v_n_1050_);
lean_dec_ref_known(v_head_1047_, 2);
v___x_1051_ = lean_array_push(v_a_1045_, v_n_1050_);
v_a_1044_ = v_tail_1049_;
v_a_1045_ = v___x_1051_;
goto _start;
}
else
{
lean_object* v_tail_1053_; 
v_tail_1053_ = lean_ctor_get(v_a_1044_, 1);
lean_inc(v_tail_1053_);
lean_dec_ref_known(v_a_1044_, 2);
v_a_1044_ = v_tail_1053_;
goto _start;
}
}
else
{
lean_object* v_tail_1055_; 
v_tail_1055_ = lean_ctor_get(v_a_1044_, 1);
lean_inc(v_tail_1055_);
lean_dec_ref_known(v_a_1044_, 2);
v_a_1044_ = v_tail_1055_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1063_ = l_Lean_MessageData_ofFormat(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1064_, lean_object* v_k_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
if (lean_obj_tag(v_stx_1064_) == 3)
{
lean_object* v_val_1075_; lean_object* v_preresolved_1076_; lean_object* v___x_1077_; lean_object* v_pre_1078_; uint8_t v___x_1079_; 
v_val_1075_ = lean_ctor_get(v_stx_1064_, 2);
lean_inc(v_val_1075_);
v_preresolved_1076_ = lean_ctor_get(v_stx_1064_, 3);
v___x_1077_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1076_);
v_pre_1078_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1076_, v___x_1077_);
v___x_1079_ = l_List_isEmpty___redArg(v_pre_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_val_1075_);
lean_dec_ref_known(v_stx_1064_, 4);
lean_dec_ref(v_k_1065_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_pre_1078_);
return v___x_1080_;
}
else
{
lean_object* v_toCold_1081_; lean_object* v_currRecDepth_1082_; lean_object* v_ref_1083_; uint8_t v_diag_1084_; uint8_t v_suppressElabErrors_1085_; lean_object* v_ref_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v_pre_1078_);
v_toCold_1081_ = lean_ctor_get(v___y_1072_, 0);
v_currRecDepth_1082_ = lean_ctor_get(v___y_1072_, 1);
v_ref_1083_ = lean_ctor_get(v___y_1072_, 2);
v_diag_1084_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*3);
v_suppressElabErrors_1085_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*3 + 1);
v_ref_1086_ = l_Lean_replaceRef(v_stx_1064_, v_ref_1083_);
lean_dec_ref_known(v_stx_1064_, 4);
lean_inc(v_currRecDepth_1082_);
lean_inc_ref(v_toCold_1081_);
v___x_1087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1087_, 0, v_toCold_1081_);
lean_ctor_set(v___x_1087_, 1, v_currRecDepth_1082_);
lean_ctor_set(v___x_1087_, 2, v_ref_1086_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*3, v_diag_1084_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*3 + 1, v_suppressElabErrors_1085_);
lean_inc(v___y_1073_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
v___x_1088_ = lean_apply_10(v_k_1065_, v_val_1075_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___x_1087_, v___y_1073_, lean_box(0));
return v___x_1088_;
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v_k_1065_);
v___x_1089_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1090_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1064_, v___x_1089_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v_stx_1064_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1091_, lean_object* v_k_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1091_, v_k_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1115_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1104_, v___x_1114_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1127_, size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_lt(v_i_1129_, v_sz_1128_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_b_1130_);
return v___x_1141_;
}
else
{
lean_object* v_a_1142_; lean_object* v_name_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_a_1142_ = lean_array_uget_borrowed(v_as_1127_, v_i_1129_);
v_name_1143_ = lean_ctor_get(v_a_1142_, 0);
lean_inc(v_name_1143_);
v___x_1144_ = l_Lean_mkIdent(v_name_1143_);
lean_inc(v___x_1144_);
v___x_1145_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1144_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1144_, v_a_1146_, v_b_1130_, v___y_1137_);
lean_dec(v_a_1146_);
lean_dec(v___x_1144_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; size_t v___x_1149_; size_t v___x_1150_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1129_, v___x_1149_);
v_i_1129_ = v___x_1150_;
v_b_1130_ = v_a_1148_;
goto _start;
}
else
{
return v___x_1147_;
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v___x_1144_);
lean_dec_ref(v_b_1130_);
v_a_1152_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1145_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1145_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1160_, lean_object* v_sz_1161_, lean_object* v_i_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
size_t v_sz_boxed_1173_; size_t v_i_boxed_1174_; lean_object* v_res_1175_; 
v_sz_boxed_1173_ = lean_unbox_usize(v_sz_1161_);
lean_dec(v_sz_1161_);
v_i_boxed_1174_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1160_, v_sz_boxed_1173_, v_i_boxed_1174_, v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v_as_1160_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1195_, lean_object* v_stx_1196_, uint8_t v___x_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___f_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
if (v___x_1195_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_1211_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; lean_object* v_tk_1213_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1285_; uint8_t v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___y_1289_; lean_object* v_stxForSuggestion_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; uint8_t v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; uint8_t v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; uint8_t v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; uint8_t v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; uint8_t v___y_1555_; lean_object* v_stxForExecution_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; uint8_t v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; uint8_t v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; uint8_t v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; uint8_t v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; uint8_t v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; uint8_t v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; uint8_t v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1816_; lean_object* v___y_1817_; uint8_t v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v___y_1823_; lean_object* v_argsArray_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; uint8_t v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; uint8_t v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v_args_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___x_2011_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v_o_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v_bang_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v_tk_1213_ = l_Lean_Syntax_getArg(v_stx_1196_, v___x_1212_);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2070_ = l_Lean_Syntax_getArg(v_stx_1196_, v___x_2011_);
v___x_2071_ = l_Lean_Syntax_isNone(v___x_2070_);
if (v___x_2071_ == 0)
{
uint8_t v___x_2072_; 
lean_inc(v___x_2070_);
v___x_2072_ = l_Lean_Syntax_matchesNull(v___x_2070_, v___x_2011_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v___x_2070_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_2073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2073_;
}
else
{
lean_object* v_bang_2074_; lean_object* v___x_2075_; 
v_bang_2074_ = l_Lean_Syntax_getArg(v___x_2070_, v___x_1212_);
lean_dec(v___x_2070_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_bang_2074_);
v_bang_2042_ = v___x_2075_;
v___y_2043_ = v___y_1202_;
v___y_2044_ = v___y_1203_;
v___y_2045_ = v___y_1204_;
v___y_2046_ = v___y_1205_;
v___y_2047_ = v___y_1206_;
v___y_2048_ = v___y_1207_;
v___y_2049_ = v___y_1208_;
v___y_2050_ = v___y_1209_;
goto v___jp_2041_;
}
}
else
{
lean_object* v___x_2076_; 
lean_dec(v___x_2070_);
v___x_2076_ = lean_box(0);
v_bang_2042_ = v___x_2076_;
v___y_2043_ = v___y_1202_;
v___y_2044_ = v___y_1203_;
v___y_2045_ = v___y_1204_;
v___y_2046_ = v___y_1205_;
v___y_2047_ = v___y_1206_;
v___y_2048_ = v___y_1207_;
v___y_2049_ = v___y_1208_;
v___y_2050_ = v___y_1209_;
goto v___jp_2041_;
}
v___jp_1214_:
{
lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(v___x_1197_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1229_, 0, v___y_1217_);
lean_closure_set(v___f_1229_, 1, v___x_1212_);
lean_closure_set(v___f_1229_, 2, v___x_1228_);
lean_closure_set(v___f_1229_, 3, v___y_1227_);
lean_closure_set(v___f_1229_, 4, v___y_1216_);
v___x_1230_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1215_, v___f_1229_, v___y_1221_, v___y_1220_, v___y_1225_, v___y_1226_, v___y_1222_, v___y_1223_, v___y_1219_, v___y_1224_);
lean_dec(v___y_1215_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v_usedTheorems_1232_; lean_object* v_diag_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1275_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v_usedTheorems_1232_ = lean_ctor_get(v_a_1231_, 0);
v_diag_1233_ = lean_ctor_get(v_a_1231_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1231_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1235_ = v_a_1231_;
v_isShared_1236_ = v_isSharedCheck_1275_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_diag_1233_);
lean_inc(v_usedTheorems_1232_);
lean_dec(v_a_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1275_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1218_, v_usedTheorems_1232_, v___y_1222_, v___y_1223_, v___y_1219_, v___y_1224_);
lean_dec_ref(v_usedTheorems_1232_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_ref_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v_ref_1239_ = lean_ctor_get(v___y_1219_, 2);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_a_1238_);
lean_ctor_set(v___x_1235_, 0, v___x_1240_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_a_1238_);
v___x_1242_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_ctor_set(v___x_1244_, 2, v___x_1243_);
lean_ctor_set(v___x_1244_, 3, v___x_1243_);
lean_ctor_set(v___x_1244_, 4, v___x_1243_);
lean_ctor_set(v___x_1244_, 5, v___x_1243_);
lean_inc(v_ref_1239_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_ref_1239_);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1247_ = 4;
v___x_1248_ = l_Lean_MessageData_nil;
v___x_1249_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1213_, v___x_1244_, v___x_1245_, v___x_1246_, v___x_1243_, v___x_1247_, v___x_1248_, v___y_1219_, v___y_1224_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1257_);
v___x_1251_ = v___x_1249_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v___x_1249_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_diag_1233_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_diag_1233_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v_diag_1233_);
v_a_1258_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1249_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1249_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_del_object(v___x_1235_);
lean_dec_ref(v_diag_1233_);
lean_dec(v_tk_1213_);
v_a_1267_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1237_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1237_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v___y_1218_);
lean_dec(v_tk_1213_);
v_a_1276_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1230_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1230_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
v___jp_1284_:
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = 0;
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1301_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1287_, v___x_1299_, v___y_1289_, v___x_1299_, v___x_1300_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1287_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
if (lean_obj_tag(v___y_1288_) == 0)
{
lean_object* v_ctx_1303_; lean_object* v_simprocs_1304_; lean_object* v_dischargeWrapper_1305_; 
v_ctx_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_ctx_1303_);
v_simprocs_1304_ = lean_ctor_get(v_a_1302_, 1);
lean_inc_ref(v_simprocs_1304_);
v_dischargeWrapper_1305_ = lean_ctor_get(v_a_1302_, 2);
lean_inc(v_dischargeWrapper_1305_);
lean_dec(v_a_1302_);
v___y_1215_ = v_dischargeWrapper_1305_;
v___y_1216_ = v_simprocs_1304_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v_stxForSuggestion_1290_;
v___y_1219_ = v___y_1297_;
v___y_1220_ = v___y_1292_;
v___y_1221_ = v___y_1291_;
v___y_1222_ = v___y_1295_;
v___y_1223_ = v___y_1296_;
v___y_1224_ = v___y_1298_;
v___y_1225_ = v___y_1293_;
v___y_1226_ = v___y_1294_;
v___y_1227_ = v_ctx_1303_;
goto v___jp_1214_;
}
else
{
lean_dec_ref_known(v___y_1288_, 1);
if (v___y_1286_ == 0)
{
lean_object* v_ctx_1306_; lean_object* v_simprocs_1307_; lean_object* v_dischargeWrapper_1308_; 
v_ctx_1306_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_ctx_1306_);
v_simprocs_1307_ = lean_ctor_get(v_a_1302_, 1);
lean_inc_ref(v_simprocs_1307_);
v_dischargeWrapper_1308_ = lean_ctor_get(v_a_1302_, 2);
lean_inc(v_dischargeWrapper_1308_);
lean_dec(v_a_1302_);
v___y_1215_ = v_dischargeWrapper_1308_;
v___y_1216_ = v_simprocs_1307_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v_stxForSuggestion_1290_;
v___y_1219_ = v___y_1297_;
v___y_1220_ = v___y_1292_;
v___y_1221_ = v___y_1291_;
v___y_1222_ = v___y_1295_;
v___y_1223_ = v___y_1296_;
v___y_1224_ = v___y_1298_;
v___y_1225_ = v___y_1293_;
v___y_1226_ = v___y_1294_;
v___y_1227_ = v_ctx_1306_;
goto v___jp_1214_;
}
else
{
lean_object* v_ctx_1309_; lean_object* v_simprocs_1310_; lean_object* v_dischargeWrapper_1311_; lean_object* v___x_1312_; 
v_ctx_1309_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_ctx_1309_);
v_simprocs_1310_ = lean_ctor_get(v_a_1302_, 1);
lean_inc_ref(v_simprocs_1310_);
v_dischargeWrapper_1311_ = lean_ctor_get(v_a_1302_, 2);
lean_inc(v_dischargeWrapper_1311_);
lean_dec(v_a_1302_);
v___x_1312_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1309_);
v___y_1215_ = v_dischargeWrapper_1311_;
v___y_1216_ = v_simprocs_1310_;
v___y_1217_ = v___y_1285_;
v___y_1218_ = v_stxForSuggestion_1290_;
v___y_1219_ = v___y_1297_;
v___y_1220_ = v___y_1292_;
v___y_1221_ = v___y_1291_;
v___y_1222_ = v___y_1295_;
v___y_1223_ = v___y_1296_;
v___y_1224_ = v___y_1298_;
v___y_1225_ = v___y_1293_;
v___y_1226_ = v___y_1294_;
v___y_1227_ = v___x_1312_;
goto v___jp_1214_;
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_stxForSuggestion_1290_);
lean_dec(v___y_1288_);
lean_dec(v___y_1285_);
lean_dec(v_tk_1213_);
v_a_1313_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1301_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1301_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
v___jp_1321_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_inc_ref(v___y_1339_);
v___x_1345_ = l_Array_append___redArg(v___y_1339_, v___y_1344_);
lean_dec_ref(v___y_1344_);
lean_inc(v___y_1327_);
lean_inc(v___y_1343_);
v___x_1346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___y_1343_);
lean_ctor_set(v___x_1346_, 1, v___y_1327_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
v___x_1347_ = l_Lean_Syntax_node6(v___y_1343_, v___y_1331_, v___y_1330_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___x_1346_);
v___y_1285_ = v___y_1322_;
v___y_1286_ = v___y_1334_;
v___y_1287_ = v___y_1333_;
v___y_1288_ = v___y_1340_;
v___y_1289_ = v___y_1342_;
v_stxForSuggestion_1290_ = v___x_1347_;
v___y_1291_ = v___y_1338_;
v___y_1292_ = v___y_1336_;
v___y_1293_ = v___y_1332_;
v___y_1294_ = v___y_1337_;
v___y_1295_ = v___y_1341_;
v___y_1296_ = v___y_1335_;
v___y_1297_ = v___y_1328_;
v___y_1298_ = v___y_1329_;
goto v___jp_1284_;
}
v___jp_1348_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_inc_ref_n(v___y_1366_, 2);
v___x_1372_ = l_Array_append___redArg(v___y_1366_, v___y_1371_);
lean_dec_ref(v___y_1371_);
lean_inc_n(v___y_1353_, 3);
lean_inc_n(v___y_1370_, 5);
v___x_1373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1370_);
lean_ctor_set(v___x_1373_, 1, v___y_1353_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1370_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1377_ = l_Lean_Syntax_SepArray_ofElems(v___x_1376_, v___y_1365_);
lean_dec_ref(v___y_1365_);
v___x_1378_ = l_Array_append___redArg(v___y_1366_, v___x_1377_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1370_);
lean_ctor_set(v___x_1379_, 1, v___y_1353_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1370_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_Syntax_node3(v___y_1370_, v___y_1353_, v___x_1375_, v___x_1379_, v___x_1381_);
if (lean_obj_tag(v___y_1352_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1384_; 
v_val_1383_ = lean_ctor_get(v___y_1352_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v___y_1352_, 1);
v___x_1384_ = l_Array_mkArray1___redArg(v_val_1383_);
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1350_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___x_1373_;
v___y_1326_ = v___x_1382_;
v___y_1327_ = v___y_1353_;
v___y_1328_ = v___y_1354_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1357_;
v___y_1332_ = v___y_1358_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___y_1361_;
v___y_1335_ = v___y_1359_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1362_;
v___y_1338_ = v___y_1364_;
v___y_1339_ = v___y_1366_;
v___y_1340_ = v___y_1368_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___x_1384_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1385_; 
lean_dec(v___y_1352_);
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1322_ = v___y_1349_;
v___y_1323_ = v___y_1350_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___x_1373_;
v___y_1326_ = v___x_1382_;
v___y_1327_ = v___y_1353_;
v___y_1328_ = v___y_1354_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1357_;
v___y_1332_ = v___y_1358_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___y_1361_;
v___y_1335_ = v___y_1359_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1362_;
v___y_1338_ = v___y_1364_;
v___y_1339_ = v___y_1366_;
v___y_1340_ = v___y_1368_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___x_1385_;
goto v___jp_1321_;
}
}
v___jp_1386_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc_ref(v___y_1404_);
v___x_1410_ = l_Array_append___redArg(v___y_1404_, v___y_1409_);
lean_dec_ref(v___y_1409_);
lean_inc(v___y_1390_);
lean_inc(v___y_1408_);
v___x_1411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1408_);
lean_ctor_set(v___x_1411_, 1, v___y_1390_);
lean_ctor_set(v___x_1411_, 2, v___x_1410_);
if (lean_obj_tag(v___y_1394_) == 1)
{
lean_object* v_val_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_val_1412_ = lean_ctor_get(v___y_1394_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___y_1394_, 1);
v___x_1413_ = l_Lean_SourceInfo_fromRef(v_val_1412_, v___x_1197_);
lean_dec(v_val_1412_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Array_mkArray1___redArg(v___x_1415_);
v___y_1349_ = v___y_1387_;
v___y_1350_ = v___y_1388_;
v___y_1351_ = v___x_1411_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___y_1390_;
v___y_1354_ = v___y_1391_;
v___y_1355_ = v___y_1392_;
v___y_1356_ = v___y_1393_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1396_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___y_1398_;
v___y_1361_ = v___y_1399_;
v___y_1362_ = v___y_1401_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1402_;
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1406_;
v___y_1368_ = v___y_1405_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___x_1416_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1417_; 
lean_dec(v___y_1394_);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1349_ = v___y_1387_;
v___y_1350_ = v___y_1388_;
v___y_1351_ = v___x_1411_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___y_1390_;
v___y_1354_ = v___y_1391_;
v___y_1355_ = v___y_1392_;
v___y_1356_ = v___y_1393_;
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1396_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___y_1398_;
v___y_1361_ = v___y_1399_;
v___y_1362_ = v___y_1401_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1402_;
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1406_;
v___y_1368_ = v___y_1405_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___x_1417_;
goto v___jp_1348_;
}
}
v___jp_1418_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_inc_ref(v___y_1431_);
v___x_1442_ = l_Array_append___redArg(v___y_1431_, v___y_1441_);
lean_dec_ref(v___y_1441_);
lean_inc(v___y_1425_);
lean_inc(v___y_1434_);
v___x_1443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1434_);
lean_ctor_set(v___x_1443_, 1, v___y_1425_);
lean_ctor_set(v___x_1443_, 2, v___x_1442_);
v___x_1444_ = l_Lean_Syntax_node6(v___y_1434_, v___y_1430_, v___y_1426_, v___y_1420_, v___y_1437_, v___y_1435_, v___y_1423_, v___x_1443_);
v___y_1285_ = v___y_1419_;
v___y_1286_ = v___y_1428_;
v___y_1287_ = v___y_1427_;
v___y_1288_ = v___y_1438_;
v___y_1289_ = v___y_1440_;
v_stxForSuggestion_1290_ = v___x_1444_;
v___y_1291_ = v___y_1436_;
v___y_1292_ = v___y_1432_;
v___y_1293_ = v___y_1424_;
v___y_1294_ = v___y_1433_;
v___y_1295_ = v___y_1439_;
v___y_1296_ = v___y_1429_;
v___y_1297_ = v___y_1421_;
v___y_1298_ = v___y_1422_;
goto v___jp_1284_;
}
v___jp_1445_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_inc_ref_n(v___y_1458_, 2);
v___x_1469_ = l_Array_append___redArg(v___y_1458_, v___y_1468_);
lean_dec_ref(v___y_1468_);
lean_inc_n(v___y_1452_, 3);
lean_inc_n(v___y_1462_, 5);
v___x_1470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1462_);
lean_ctor_set(v___x_1470_, 1, v___y_1452_);
lean_ctor_set(v___x_1470_, 2, v___x_1469_);
v___x_1471_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1462_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1474_ = l_Lean_Syntax_SepArray_ofElems(v___x_1473_, v___y_1463_);
lean_dec_ref(v___y_1463_);
v___x_1475_ = l_Array_append___redArg(v___y_1458_, v___x_1474_);
lean_dec_ref(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1476_, 0, v___y_1462_);
lean_ctor_set(v___x_1476_, 1, v___y_1452_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1462_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_Syntax_node3(v___y_1462_, v___y_1452_, v___x_1472_, v___x_1476_, v___x_1478_);
if (lean_obj_tag(v___y_1448_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; 
v_val_1480_ = lean_ctor_get(v___y_1448_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v___y_1448_, 1);
v___x_1481_ = l_Array_mkArray1___redArg(v_val_1480_);
v___y_1419_ = v___y_1446_;
v___y_1420_ = v___y_1447_;
v___y_1421_ = v___y_1449_;
v___y_1422_ = v___y_1450_;
v___y_1423_ = v___x_1479_;
v___y_1424_ = v___y_1451_;
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___y_1453_;
v___y_1427_ = v___y_1454_;
v___y_1428_ = v___y_1455_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1457_;
v___y_1431_ = v___y_1458_;
v___y_1432_ = v___y_1460_;
v___y_1433_ = v___y_1459_;
v___y_1434_ = v___y_1462_;
v___y_1435_ = v___x_1470_;
v___y_1436_ = v___y_1461_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1466_;
v___y_1439_ = v___y_1465_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___x_1481_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1482_; 
lean_dec(v___y_1448_);
v___x_1482_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1419_ = v___y_1446_;
v___y_1420_ = v___y_1447_;
v___y_1421_ = v___y_1449_;
v___y_1422_ = v___y_1450_;
v___y_1423_ = v___x_1479_;
v___y_1424_ = v___y_1451_;
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___y_1453_;
v___y_1427_ = v___y_1454_;
v___y_1428_ = v___y_1455_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1457_;
v___y_1431_ = v___y_1458_;
v___y_1432_ = v___y_1460_;
v___y_1433_ = v___y_1459_;
v___y_1434_ = v___y_1462_;
v___y_1435_ = v___x_1470_;
v___y_1436_ = v___y_1461_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1466_;
v___y_1439_ = v___y_1465_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___x_1482_;
goto v___jp_1418_;
}
}
v___jp_1483_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_inc_ref(v___y_1497_);
v___x_1507_ = l_Array_append___redArg(v___y_1497_, v___y_1506_);
lean_dec_ref(v___y_1506_);
lean_inc(v___y_1491_);
lean_inc(v___y_1501_);
v___x_1508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___y_1501_);
lean_ctor_set(v___x_1508_, 1, v___y_1491_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
if (lean_obj_tag(v___y_1489_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_val_1509_ = lean_ctor_get(v___y_1489_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___y_1489_, 1);
v___x_1510_ = l_Lean_SourceInfo_fromRef(v_val_1509_, v___x_1197_);
lean_dec(v_val_1509_);
v___x_1511_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Array_mkArray1___redArg(v___x_1512_);
v___y_1446_ = v___y_1484_;
v___y_1447_ = v___y_1485_;
v___y_1448_ = v___y_1486_;
v___y_1449_ = v___y_1487_;
v___y_1450_ = v___y_1488_;
v___y_1451_ = v___y_1490_;
v___y_1452_ = v___y_1491_;
v___y_1453_ = v___y_1492_;
v___y_1454_ = v___y_1493_;
v___y_1455_ = v___y_1494_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___y_1496_;
v___y_1458_ = v___y_1497_;
v___y_1459_ = v___y_1499_;
v___y_1460_ = v___y_1498_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1501_;
v___y_1463_ = v___y_1502_;
v___y_1464_ = v___x_1508_;
v___y_1465_ = v___y_1504_;
v___y_1466_ = v___y_1503_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___x_1513_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1514_; 
lean_dec(v___y_1489_);
v___x_1514_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1446_ = v___y_1484_;
v___y_1447_ = v___y_1485_;
v___y_1448_ = v___y_1486_;
v___y_1449_ = v___y_1487_;
v___y_1450_ = v___y_1488_;
v___y_1451_ = v___y_1490_;
v___y_1452_ = v___y_1491_;
v___y_1453_ = v___y_1492_;
v___y_1454_ = v___y_1493_;
v___y_1455_ = v___y_1494_;
v___y_1456_ = v___y_1495_;
v___y_1457_ = v___y_1496_;
v___y_1458_ = v___y_1497_;
v___y_1459_ = v___y_1499_;
v___y_1460_ = v___y_1498_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1501_;
v___y_1463_ = v___y_1502_;
v___y_1464_ = v___x_1508_;
v___y_1465_ = v___y_1504_;
v___y_1466_ = v___y_1503_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___x_1514_;
goto v___jp_1445_;
}
}
v___jp_1515_:
{
lean_object* v_ref_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_ref_1535_ = lean_ctor_get(v___y_1520_, 2);
v___x_1536_ = l_Lean_SourceInfo_fromRef(v_ref_1535_, v___y_1534_);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1538_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1537_);
v___x_1539_ = l_Lean_SourceInfo_fromRef(v_tk_1213_, v___x_1197_);
v___x_1540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1537_);
v___x_1541_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1542_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1518_) == 1)
{
lean_object* v_val_1543_; lean_object* v___x_1544_; 
v_val_1543_ = lean_ctor_get(v___y_1518_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v___y_1518_, 1);
v___x_1544_ = l_Array_mkArray1___redArg(v_val_1543_);
v___y_1484_ = v___y_1516_;
v___y_1485_ = v___y_1517_;
v___y_1486_ = v___y_1519_;
v___y_1487_ = v___y_1520_;
v___y_1488_ = v___y_1521_;
v___y_1489_ = v___y_1522_;
v___y_1490_ = v___y_1523_;
v___y_1491_ = v___x_1541_;
v___y_1492_ = v___x_1540_;
v___y_1493_ = v___y_1524_;
v___y_1494_ = v___y_1525_;
v___y_1495_ = v___y_1526_;
v___y_1496_ = v___x_1538_;
v___y_1497_ = v___x_1542_;
v___y_1498_ = v___y_1527_;
v___y_1499_ = v___y_1528_;
v___y_1500_ = v___y_1529_;
v___y_1501_ = v___x_1536_;
v___y_1502_ = v___y_1530_;
v___y_1503_ = v___y_1532_;
v___y_1504_ = v___y_1531_;
v___y_1505_ = v___y_1533_;
v___y_1506_ = v___x_1544_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1545_; 
lean_dec(v___y_1518_);
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1484_ = v___y_1516_;
v___y_1485_ = v___y_1517_;
v___y_1486_ = v___y_1519_;
v___y_1487_ = v___y_1520_;
v___y_1488_ = v___y_1521_;
v___y_1489_ = v___y_1522_;
v___y_1490_ = v___y_1523_;
v___y_1491_ = v___x_1541_;
v___y_1492_ = v___x_1540_;
v___y_1493_ = v___y_1524_;
v___y_1494_ = v___y_1525_;
v___y_1495_ = v___y_1526_;
v___y_1496_ = v___x_1538_;
v___y_1497_ = v___x_1542_;
v___y_1498_ = v___y_1527_;
v___y_1499_ = v___y_1528_;
v___y_1500_ = v___y_1529_;
v___y_1501_ = v___x_1536_;
v___y_1502_ = v___y_1530_;
v___y_1503_ = v___y_1532_;
v___y_1504_ = v___y_1531_;
v___y_1505_ = v___y_1533_;
v___y_1506_ = v___x_1545_;
goto v___jp_1483_;
}
}
v___jp_1546_:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1548_);
if (lean_obj_tag(v___y_1554_) == 0)
{
lean_object* v_a_1566_; uint8_t v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = 0;
v___y_1516_ = v___y_1547_;
v___y_1517_ = v_a_1566_;
v___y_1518_ = v___y_1551_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1563_;
v___y_1521_ = v___y_1564_;
v___y_1522_ = v___y_1553_;
v___y_1523_ = v___y_1559_;
v___y_1524_ = v_stxForExecution_1556_;
v___y_1525_ = v___y_1549_;
v___y_1526_ = v___y_1562_;
v___y_1527_ = v___y_1558_;
v___y_1528_ = v___y_1560_;
v___y_1529_ = v___y_1557_;
v___y_1530_ = v___y_1552_;
v___y_1531_ = v___y_1561_;
v___y_1532_ = v___y_1554_;
v___y_1533_ = v___y_1555_;
v___y_1534_ = v___x_1567_;
goto v___jp_1515_;
}
else
{
if (v___y_1549_ == 0)
{
lean_object* v_a_1568_; 
v_a_1568_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1565_);
v___y_1516_ = v___y_1547_;
v___y_1517_ = v_a_1568_;
v___y_1518_ = v___y_1551_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1563_;
v___y_1521_ = v___y_1564_;
v___y_1522_ = v___y_1553_;
v___y_1523_ = v___y_1559_;
v___y_1524_ = v_stxForExecution_1556_;
v___y_1525_ = v___y_1549_;
v___y_1526_ = v___y_1562_;
v___y_1527_ = v___y_1558_;
v___y_1528_ = v___y_1560_;
v___y_1529_ = v___y_1557_;
v___y_1530_ = v___y_1552_;
v___y_1531_ = v___y_1561_;
v___y_1532_ = v___y_1554_;
v___y_1533_ = v___y_1555_;
v___y_1534_ = v___y_1549_;
goto v___jp_1515_;
}
else
{
lean_object* v_a_1569_; lean_object* v_ref_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_a_1569_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1565_);
v_ref_1570_ = lean_ctor_get(v___y_1563_, 2);
v___x_1571_ = 0;
v___x_1572_ = l_Lean_SourceInfo_fromRef(v_ref_1570_, v___x_1571_);
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1574_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1573_);
v___x_1575_ = l_Lean_SourceInfo_fromRef(v_tk_1213_, v___x_1197_);
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1579_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1551_) == 1)
{
lean_object* v_val_1580_; lean_object* v___x_1581_; 
v_val_1580_ = lean_ctor_get(v___y_1551_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___y_1551_, 1);
v___x_1581_ = l_Array_mkArray1___redArg(v_val_1580_);
v___y_1387_ = v___y_1547_;
v___y_1388_ = v_a_1569_;
v___y_1389_ = v___y_1550_;
v___y_1390_ = v___x_1578_;
v___y_1391_ = v___y_1563_;
v___y_1392_ = v___y_1564_;
v___y_1393_ = v___x_1577_;
v___y_1394_ = v___y_1553_;
v___y_1395_ = v___x_1574_;
v___y_1396_ = v___y_1559_;
v___y_1397_ = v___y_1562_;
v___y_1398_ = v_stxForExecution_1556_;
v___y_1399_ = v___y_1549_;
v___y_1400_ = v___y_1558_;
v___y_1401_ = v___y_1560_;
v___y_1402_ = v___y_1557_;
v___y_1403_ = v___y_1552_;
v___y_1404_ = v___x_1579_;
v___y_1405_ = v___y_1554_;
v___y_1406_ = v___y_1561_;
v___y_1407_ = v___y_1555_;
v___y_1408_ = v___x_1572_;
v___y_1409_ = v___x_1581_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1582_; 
lean_dec(v___y_1551_);
v___x_1582_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1387_ = v___y_1547_;
v___y_1388_ = v_a_1569_;
v___y_1389_ = v___y_1550_;
v___y_1390_ = v___x_1578_;
v___y_1391_ = v___y_1563_;
v___y_1392_ = v___y_1564_;
v___y_1393_ = v___x_1577_;
v___y_1394_ = v___y_1553_;
v___y_1395_ = v___x_1574_;
v___y_1396_ = v___y_1559_;
v___y_1397_ = v___y_1562_;
v___y_1398_ = v_stxForExecution_1556_;
v___y_1399_ = v___y_1549_;
v___y_1400_ = v___y_1558_;
v___y_1401_ = v___y_1560_;
v___y_1402_ = v___y_1557_;
v___y_1403_ = v___y_1552_;
v___y_1404_ = v___x_1579_;
v___y_1405_ = v___y_1554_;
v___y_1406_ = v___y_1561_;
v___y_1407_ = v___y_1555_;
v___y_1408_ = v___x_1572_;
v___y_1409_ = v___x_1582_;
goto v___jp_1386_;
}
}
}
}
v___jp_1583_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_inc_ref(v___y_1598_);
v___x_1610_ = l_Array_append___redArg(v___y_1598_, v___y_1609_);
lean_dec_ref(v___y_1609_);
lean_inc(v___y_1603_);
lean_inc(v___y_1588_);
v___x_1611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1588_);
lean_ctor_set(v___x_1611_, 1, v___y_1603_);
lean_ctor_set(v___x_1611_, 2, v___x_1610_);
lean_inc(v___y_1602_);
v___x_1612_ = l_Lean_Syntax_node6(v___y_1588_, v___y_1594_, v___y_1597_, v___y_1602_, v___y_1606_, v___y_1592_, v___y_1585_, v___x_1611_);
v___y_1547_ = v___y_1584_;
v___y_1548_ = v___y_1602_;
v___y_1549_ = v___y_1591_;
v___y_1550_ = v___y_1599_;
v___y_1551_ = v___y_1587_;
v___y_1552_ = v___y_1604_;
v___y_1553_ = v___y_1590_;
v___y_1554_ = v___y_1607_;
v___y_1555_ = v___y_1608_;
v_stxForExecution_1556_ = v___x_1612_;
v___y_1557_ = v___y_1600_;
v___y_1558_ = v___y_1596_;
v___y_1559_ = v___y_1593_;
v___y_1560_ = v___y_1589_;
v___y_1561_ = v___y_1601_;
v___y_1562_ = v___y_1586_;
v___y_1563_ = v___y_1605_;
v___y_1564_ = v___y_1595_;
goto v___jp_1546_;
}
v___jp_1613_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_inc_ref_n(v___y_1616_, 2);
v___x_1638_ = l_Array_append___redArg(v___y_1616_, v___y_1637_);
lean_dec_ref(v___y_1637_);
lean_inc_n(v___y_1627_, 3);
lean_inc_n(v___y_1620_, 5);
v___x_1639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1620_);
lean_ctor_set(v___x_1639_, 1, v___y_1627_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___y_1620_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1643_ = l_Lean_Syntax_SepArray_ofElems(v___x_1642_, v___y_1628_);
v___x_1644_ = l_Array_append___redArg(v___y_1616_, v___x_1643_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___y_1620_);
lean_ctor_set(v___x_1645_, 1, v___y_1627_);
lean_ctor_set(v___x_1645_, 2, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1620_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_Syntax_node3(v___y_1620_, v___y_1627_, v___x_1641_, v___x_1645_, v___x_1647_);
if (lean_obj_tag(v___y_1617_) == 1)
{
lean_object* v_val_1649_; lean_object* v___x_1650_; 
v_val_1649_ = lean_ctor_get(v___y_1617_, 0);
lean_inc(v_val_1649_);
v___x_1650_ = l_Array_mkArray1___redArg(v_val_1649_);
v___y_1584_ = v___y_1614_;
v___y_1585_ = v___x_1648_;
v___y_1586_ = v___y_1618_;
v___y_1587_ = v___y_1619_;
v___y_1588_ = v___y_1620_;
v___y_1589_ = v___y_1621_;
v___y_1590_ = v___y_1624_;
v___y_1591_ = v___y_1626_;
v___y_1592_ = v___x_1639_;
v___y_1593_ = v___y_1629_;
v___y_1594_ = v___y_1632_;
v___y_1595_ = v___y_1634_;
v___y_1596_ = v___y_1636_;
v___y_1597_ = v___y_1615_;
v___y_1598_ = v___y_1616_;
v___y_1599_ = v___y_1617_;
v___y_1600_ = v___y_1622_;
v___y_1601_ = v___y_1623_;
v___y_1602_ = v___y_1625_;
v___y_1603_ = v___y_1627_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___y_1633_;
v___y_1608_ = v___y_1635_;
v___y_1609_ = v___x_1650_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1584_ = v___y_1614_;
v___y_1585_ = v___x_1648_;
v___y_1586_ = v___y_1618_;
v___y_1587_ = v___y_1619_;
v___y_1588_ = v___y_1620_;
v___y_1589_ = v___y_1621_;
v___y_1590_ = v___y_1624_;
v___y_1591_ = v___y_1626_;
v___y_1592_ = v___x_1639_;
v___y_1593_ = v___y_1629_;
v___y_1594_ = v___y_1632_;
v___y_1595_ = v___y_1634_;
v___y_1596_ = v___y_1636_;
v___y_1597_ = v___y_1615_;
v___y_1598_ = v___y_1616_;
v___y_1599_ = v___y_1617_;
v___y_1600_ = v___y_1622_;
v___y_1601_ = v___y_1623_;
v___y_1602_ = v___y_1625_;
v___y_1603_ = v___y_1627_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___y_1633_;
v___y_1608_ = v___y_1635_;
v___y_1609_ = v___x_1651_;
goto v___jp_1583_;
}
}
v___jp_1652_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_inc_ref(v___y_1654_);
v___x_1676_ = l_Array_append___redArg(v___y_1654_, v___y_1675_);
lean_dec_ref(v___y_1675_);
lean_inc(v___y_1666_);
lean_inc(v___y_1659_);
v___x_1677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1659_);
lean_ctor_set(v___x_1677_, 1, v___y_1666_);
lean_ctor_set(v___x_1677_, 2, v___x_1676_);
if (lean_obj_tag(v___y_1663_) == 1)
{
lean_object* v_val_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_val_1678_ = lean_ctor_get(v___y_1663_, 0);
v___x_1679_ = l_Lean_SourceInfo_fromRef(v_val_1678_, v___x_1197_);
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Array_mkArray1___redArg(v___x_1681_);
v___y_1614_ = v___y_1653_;
v___y_1615_ = v___y_1655_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1656_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1658_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1661_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___y_1663_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1665_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___y_1668_;
v___y_1629_ = v___y_1667_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___x_1677_;
v___y_1632_ = v___y_1670_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1671_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1673_;
v___y_1637_ = v___x_1682_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1614_ = v___y_1653_;
v___y_1615_ = v___y_1655_;
v___y_1616_ = v___y_1654_;
v___y_1617_ = v___y_1656_;
v___y_1618_ = v___y_1657_;
v___y_1619_ = v___y_1658_;
v___y_1620_ = v___y_1659_;
v___y_1621_ = v___y_1660_;
v___y_1622_ = v___y_1661_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___y_1663_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1665_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___y_1668_;
v___y_1629_ = v___y_1667_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___x_1677_;
v___y_1632_ = v___y_1670_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1671_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1673_;
v___y_1637_ = v___x_1683_;
goto v___jp_1613_;
}
}
v___jp_1684_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_inc_ref(v___y_1707_);
v___x_1711_ = l_Array_append___redArg(v___y_1707_, v___y_1710_);
lean_dec_ref(v___y_1710_);
lean_inc(v___y_1704_);
lean_inc(v___y_1686_);
v___x_1712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1712_, 0, v___y_1686_);
lean_ctor_set(v___x_1712_, 1, v___y_1704_);
lean_ctor_set(v___x_1712_, 2, v___x_1711_);
lean_inc(v___y_1702_);
v___x_1713_ = l_Lean_Syntax_node6(v___y_1686_, v___y_1703_, v___y_1691_, v___y_1702_, v___y_1701_, v___y_1692_, v___y_1700_, v___x_1712_);
v___y_1547_ = v___y_1685_;
v___y_1548_ = v___y_1702_;
v___y_1549_ = v___y_1693_;
v___y_1550_ = v___y_1697_;
v___y_1551_ = v___y_1688_;
v___y_1552_ = v___y_1705_;
v___y_1553_ = v___y_1690_;
v___y_1554_ = v___y_1708_;
v___y_1555_ = v___y_1709_;
v_stxForExecution_1556_ = v___x_1713_;
v___y_1557_ = v___y_1698_;
v___y_1558_ = v___y_1696_;
v___y_1559_ = v___y_1694_;
v___y_1560_ = v___y_1689_;
v___y_1561_ = v___y_1699_;
v___y_1562_ = v___y_1687_;
v___y_1563_ = v___y_1706_;
v___y_1564_ = v___y_1695_;
goto v___jp_1546_;
}
v___jp_1714_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_inc_ref_n(v___y_1733_, 2);
v___x_1739_ = l_Array_append___redArg(v___y_1733_, v___y_1738_);
lean_dec_ref(v___y_1738_);
lean_inc_n(v___y_1728_, 3);
lean_inc_n(v___y_1716_, 5);
v___x_1740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1740_, 0, v___y_1716_);
lean_ctor_set(v___x_1740_, 1, v___y_1728_);
lean_ctor_set(v___x_1740_, 2, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___y_1716_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1744_ = l_Lean_Syntax_SepArray_ofElems(v___x_1743_, v___y_1730_);
v___x_1745_ = l_Array_append___redArg(v___y_1733_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1716_);
lean_ctor_set(v___x_1746_, 1, v___y_1728_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1716_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = l_Lean_Syntax_node3(v___y_1716_, v___y_1728_, v___x_1742_, v___x_1746_, v___x_1748_);
if (lean_obj_tag(v___y_1717_) == 1)
{
lean_object* v_val_1750_; lean_object* v___x_1751_; 
v_val_1750_ = lean_ctor_get(v___y_1717_, 0);
lean_inc(v_val_1750_);
v___x_1751_ = l_Array_mkArray1___redArg(v_val_1750_);
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1718_;
v___y_1688_ = v___y_1719_;
v___y_1689_ = v___y_1720_;
v___y_1690_ = v___y_1723_;
v___y_1691_ = v___y_1725_;
v___y_1692_ = v___x_1740_;
v___y_1693_ = v___y_1729_;
v___y_1694_ = v___y_1731_;
v___y_1695_ = v___y_1735_;
v___y_1696_ = v___y_1737_;
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___y_1721_;
v___y_1699_ = v___y_1722_;
v___y_1700_ = v___x_1749_;
v___y_1701_ = v___y_1724_;
v___y_1702_ = v___y_1726_;
v___y_1703_ = v___y_1727_;
v___y_1704_ = v___y_1728_;
v___y_1705_ = v___y_1730_;
v___y_1706_ = v___y_1732_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1736_;
v___y_1710_ = v___x_1751_;
goto v___jp_1684_;
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1718_;
v___y_1688_ = v___y_1719_;
v___y_1689_ = v___y_1720_;
v___y_1690_ = v___y_1723_;
v___y_1691_ = v___y_1725_;
v___y_1692_ = v___x_1740_;
v___y_1693_ = v___y_1729_;
v___y_1694_ = v___y_1731_;
v___y_1695_ = v___y_1735_;
v___y_1696_ = v___y_1737_;
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___y_1721_;
v___y_1699_ = v___y_1722_;
v___y_1700_ = v___x_1749_;
v___y_1701_ = v___y_1724_;
v___y_1702_ = v___y_1726_;
v___y_1703_ = v___y_1727_;
v___y_1704_ = v___y_1728_;
v___y_1705_ = v___y_1730_;
v___y_1706_ = v___y_1732_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1736_;
v___y_1710_ = v___x_1752_;
goto v___jp_1684_;
}
}
v___jp_1753_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_inc_ref(v___y_1771_);
v___x_1777_ = l_Array_append___redArg(v___y_1771_, v___y_1776_);
lean_dec_ref(v___y_1776_);
lean_inc(v___y_1766_);
lean_inc(v___y_1755_);
v___x_1778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1755_);
lean_ctor_set(v___x_1778_, 1, v___y_1766_);
lean_ctor_set(v___x_1778_, 2, v___x_1777_);
if (lean_obj_tag(v___y_1762_) == 1)
{
lean_object* v_val_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_val_1779_ = lean_ctor_get(v___y_1762_, 0);
v___x_1780_ = l_Lean_SourceInfo_fromRef(v_val_1779_, v___x_1197_);
v___x_1781_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Array_mkArray1___redArg(v___x_1782_);
v___y_1715_ = v___y_1754_;
v___y_1716_ = v___y_1755_;
v___y_1717_ = v___y_1756_;
v___y_1718_ = v___y_1757_;
v___y_1719_ = v___y_1758_;
v___y_1720_ = v___y_1759_;
v___y_1721_ = v___y_1760_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___x_1778_;
v___y_1725_ = v___y_1763_;
v___y_1726_ = v___y_1764_;
v___y_1727_ = v___y_1767_;
v___y_1728_ = v___y_1766_;
v___y_1729_ = v___y_1765_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1768_;
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1772_;
v___y_1736_ = v___y_1775_;
v___y_1737_ = v___y_1774_;
v___y_1738_ = v___x_1783_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1715_ = v___y_1754_;
v___y_1716_ = v___y_1755_;
v___y_1717_ = v___y_1756_;
v___y_1718_ = v___y_1757_;
v___y_1719_ = v___y_1758_;
v___y_1720_ = v___y_1759_;
v___y_1721_ = v___y_1760_;
v___y_1722_ = v___y_1761_;
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___x_1778_;
v___y_1725_ = v___y_1763_;
v___y_1726_ = v___y_1764_;
v___y_1727_ = v___y_1767_;
v___y_1728_ = v___y_1766_;
v___y_1729_ = v___y_1765_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1768_;
v___y_1732_ = v___y_1770_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1772_;
v___y_1736_ = v___y_1775_;
v___y_1737_ = v___y_1774_;
v___y_1738_ = v___x_1784_;
goto v___jp_1714_;
}
}
v___jp_1785_:
{
lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_ref_1804_ = lean_ctor_get(v___y_1798_, 2);
v___x_1805_ = l_Lean_SourceInfo_fromRef(v_ref_1804_, v___y_1803_);
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1200_);
lean_inc_ref(v___x_1199_);
lean_inc_ref(v___x_1198_);
v___x_1807_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1806_);
v___x_1808_ = l_Lean_SourceInfo_fromRef(v_tk_1213_, v___x_1197_);
v___x_1809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1806_);
v___x_1810_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1811_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1789_) == 1)
{
lean_object* v_val_1812_; lean_object* v___x_1813_; 
v_val_1812_ = lean_ctor_get(v___y_1789_, 0);
lean_inc(v_val_1812_);
v___x_1813_ = l_Array_mkArray1___redArg(v_val_1812_);
v___y_1754_ = v___y_1786_;
v___y_1755_ = v___x_1805_;
v___y_1756_ = v___y_1787_;
v___y_1757_ = v___y_1788_;
v___y_1758_ = v___y_1789_;
v___y_1759_ = v___y_1790_;
v___y_1760_ = v___y_1791_;
v___y_1761_ = v___y_1792_;
v___y_1762_ = v___y_1793_;
v___y_1763_ = v___x_1809_;
v___y_1764_ = v___y_1794_;
v___y_1765_ = v___y_1795_;
v___y_1766_ = v___x_1810_;
v___y_1767_ = v___x_1807_;
v___y_1768_ = v___y_1796_;
v___y_1769_ = v___y_1797_;
v___y_1770_ = v___y_1798_;
v___y_1771_ = v___x_1811_;
v___y_1772_ = v___y_1800_;
v___y_1773_ = v___y_1799_;
v___y_1774_ = v___y_1802_;
v___y_1775_ = v___y_1801_;
v___y_1776_ = v___x_1813_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1754_ = v___y_1786_;
v___y_1755_ = v___x_1805_;
v___y_1756_ = v___y_1787_;
v___y_1757_ = v___y_1788_;
v___y_1758_ = v___y_1789_;
v___y_1759_ = v___y_1790_;
v___y_1760_ = v___y_1791_;
v___y_1761_ = v___y_1792_;
v___y_1762_ = v___y_1793_;
v___y_1763_ = v___x_1809_;
v___y_1764_ = v___y_1794_;
v___y_1765_ = v___y_1795_;
v___y_1766_ = v___x_1810_;
v___y_1767_ = v___x_1807_;
v___y_1768_ = v___y_1796_;
v___y_1769_ = v___y_1797_;
v___y_1770_ = v___y_1798_;
v___y_1771_ = v___x_1811_;
v___y_1772_ = v___y_1800_;
v___y_1773_ = v___y_1799_;
v___y_1774_ = v___y_1802_;
v___y_1775_ = v___y_1801_;
v___y_1776_ = v___x_1814_;
goto v___jp_1753_;
}
}
v___jp_1815_:
{
if (lean_obj_tag(v___y_1822_) == 0)
{
uint8_t v___x_1833_; 
v___x_1833_ = 0;
v___y_1786_ = v___y_1816_;
v___y_1787_ = v___y_1820_;
v___y_1788_ = v___y_1830_;
v___y_1789_ = v___y_1819_;
v___y_1790_ = v___y_1828_;
v___y_1791_ = v___y_1825_;
v___y_1792_ = v___y_1829_;
v___y_1793_ = v___y_1821_;
v___y_1794_ = v___y_1817_;
v___y_1795_ = v___y_1818_;
v___y_1796_ = v___y_1827_;
v___y_1797_ = v_argsArray_1824_;
v___y_1798_ = v___y_1831_;
v___y_1799_ = v___y_1822_;
v___y_1800_ = v___y_1832_;
v___y_1801_ = v___y_1823_;
v___y_1802_ = v___y_1826_;
v___y_1803_ = v___x_1833_;
goto v___jp_1785_;
}
else
{
if (v___y_1818_ == 0)
{
v___y_1786_ = v___y_1816_;
v___y_1787_ = v___y_1820_;
v___y_1788_ = v___y_1830_;
v___y_1789_ = v___y_1819_;
v___y_1790_ = v___y_1828_;
v___y_1791_ = v___y_1825_;
v___y_1792_ = v___y_1829_;
v___y_1793_ = v___y_1821_;
v___y_1794_ = v___y_1817_;
v___y_1795_ = v___y_1818_;
v___y_1796_ = v___y_1827_;
v___y_1797_ = v_argsArray_1824_;
v___y_1798_ = v___y_1831_;
v___y_1799_ = v___y_1822_;
v___y_1800_ = v___y_1832_;
v___y_1801_ = v___y_1823_;
v___y_1802_ = v___y_1826_;
v___y_1803_ = v___y_1818_;
goto v___jp_1785_;
}
else
{
lean_object* v_ref_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_ref_1834_ = lean_ctor_get(v___y_1831_, 2);
v___x_1835_ = 0;
v___x_1836_ = l_Lean_SourceInfo_fromRef(v_ref_1834_, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1200_);
lean_inc_ref(v___x_1199_);
lean_inc_ref(v___x_1198_);
v___x_1838_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1837_);
v___x_1839_ = l_Lean_SourceInfo_fromRef(v_tk_1213_, v___x_1197_);
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1843_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1819_) == 1)
{
lean_object* v_val_1844_; lean_object* v___x_1845_; 
v_val_1844_ = lean_ctor_get(v___y_1819_, 0);
lean_inc(v_val_1844_);
v___x_1845_ = l_Array_mkArray1___redArg(v_val_1844_);
v___y_1653_ = v___y_1816_;
v___y_1654_ = v___x_1843_;
v___y_1655_ = v___x_1841_;
v___y_1656_ = v___y_1820_;
v___y_1657_ = v___y_1830_;
v___y_1658_ = v___y_1819_;
v___y_1659_ = v___x_1836_;
v___y_1660_ = v___y_1828_;
v___y_1661_ = v___y_1825_;
v___y_1662_ = v___y_1829_;
v___y_1663_ = v___y_1821_;
v___y_1664_ = v___y_1817_;
v___y_1665_ = v___y_1818_;
v___y_1666_ = v___x_1842_;
v___y_1667_ = v___y_1827_;
v___y_1668_ = v_argsArray_1824_;
v___y_1669_ = v___y_1831_;
v___y_1670_ = v___x_1838_;
v___y_1671_ = v___y_1832_;
v___y_1672_ = v___y_1822_;
v___y_1673_ = v___y_1826_;
v___y_1674_ = v___y_1823_;
v___y_1675_ = v___x_1845_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1653_ = v___y_1816_;
v___y_1654_ = v___x_1843_;
v___y_1655_ = v___x_1841_;
v___y_1656_ = v___y_1820_;
v___y_1657_ = v___y_1830_;
v___y_1658_ = v___y_1819_;
v___y_1659_ = v___x_1836_;
v___y_1660_ = v___y_1828_;
v___y_1661_ = v___y_1825_;
v___y_1662_ = v___y_1829_;
v___y_1663_ = v___y_1821_;
v___y_1664_ = v___y_1817_;
v___y_1665_ = v___y_1818_;
v___y_1666_ = v___x_1842_;
v___y_1667_ = v___y_1827_;
v___y_1668_ = v_argsArray_1824_;
v___y_1669_ = v___y_1831_;
v___y_1670_ = v___x_1838_;
v___y_1671_ = v___y_1832_;
v___y_1672_ = v___y_1822_;
v___y_1673_ = v___y_1826_;
v___y_1674_ = v___y_1823_;
v___y_1675_ = v___x_1846_;
goto v___jp_1652_;
}
}
}
}
v___jp_1847_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1857_, v___y_1854_, v___y_1859_, v___y_1849_, v___y_1861_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = l_Lean_LibrarySuggestions_select(v_a_1867_, v___y_1865_, v___y_1854_, v___y_1859_, v___y_1849_, v___y_1861_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; size_t v_sz_1870_; size_t v___x_1871_; lean_object* v___x_1872_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v_sz_1870_ = lean_array_size(v_a_1869_);
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1869_, v_sz_1870_, v___x_1871_, v___y_1864_, v___y_1855_, v___y_1857_, v___y_1852_, v___y_1860_, v___y_1854_, v___y_1859_, v___y_1849_, v___y_1861_);
lean_dec(v_a_1869_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___y_1816_ = v___y_1848_;
v___y_1817_ = v___y_1856_;
v___y_1818_ = v___y_1858_;
v___y_1819_ = v___y_1851_;
v___y_1820_ = v___y_1850_;
v___y_1821_ = v___y_1853_;
v___y_1822_ = v___y_1862_;
v___y_1823_ = v___y_1863_;
v_argsArray_1824_ = v_a_1873_;
v___y_1825_ = v___y_1855_;
v___y_1826_ = v___y_1857_;
v___y_1827_ = v___y_1852_;
v___y_1828_ = v___y_1860_;
v___y_1829_ = v___y_1854_;
v___y_1830_ = v___y_1859_;
v___y_1831_ = v___y_1849_;
v___y_1832_ = v___y_1861_;
goto v___jp_1815_;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v___y_1862_);
lean_dec(v___y_1856_);
lean_dec(v___y_1853_);
lean_dec(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec(v___y_1848_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v_a_1874_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1872_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1872_);
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
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1862_);
lean_dec(v___y_1856_);
lean_dec(v___y_1853_);
lean_dec(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec(v___y_1848_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v_a_1882_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1868_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1868_);
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
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1862_);
lean_dec(v___y_1856_);
lean_dec(v___y_1853_);
lean_dec(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec(v___y_1848_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v_a_1890_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1866_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1866_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
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
v___jp_1898_:
{
lean_object* v_config_1917_; uint8_t v_suggestions_1918_; 
v_config_1917_ = lean_ctor_get(v___y_1904_, 0);
lean_inc_ref(v_config_1917_);
lean_dec_ref(v___y_1904_);
v_suggestions_1918_ = lean_ctor_get_uint8(v_config_1917_, sizeof(void*)*3 + 26);
if (v_suggestions_1918_ == 0)
{
lean_dec_ref(v_config_1917_);
lean_dec_ref(v___f_1201_);
v___y_1816_ = v___y_1899_;
v___y_1817_ = v___y_1908_;
v___y_1818_ = v___y_1910_;
v___y_1819_ = v___y_1902_;
v___y_1820_ = v___y_1901_;
v___y_1821_ = v___y_1905_;
v___y_1822_ = v___y_1914_;
v___y_1823_ = v___y_1915_;
v_argsArray_1824_ = v___y_1916_;
v___y_1825_ = v___y_1907_;
v___y_1826_ = v___y_1909_;
v___y_1827_ = v___y_1903_;
v___y_1828_ = v___y_1912_;
v___y_1829_ = v___y_1906_;
v___y_1830_ = v___y_1911_;
v___y_1831_ = v___y_1900_;
v___y_1832_ = v___y_1913_;
goto v___jp_1815_;
}
else
{
lean_object* v_maxSuggestions_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_maxSuggestions_1919_ = lean_ctor_get(v_config_1917_, 2);
lean_inc(v_maxSuggestions_1919_);
lean_dec_ref(v_config_1917_);
v___x_1920_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1921_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1919_) == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_unsigned_to_nat(100u);
v___x_1923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1920_);
lean_ctor_set(v___x_1923_, 2, v___f_1201_);
lean_ctor_set(v___x_1923_, 3, v___x_1921_);
v___y_1848_ = v___y_1899_;
v___y_1849_ = v___y_1900_;
v___y_1850_ = v___y_1901_;
v___y_1851_ = v___y_1902_;
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1905_;
v___y_1854_ = v___y_1906_;
v___y_1855_ = v___y_1907_;
v___y_1856_ = v___y_1908_;
v___y_1857_ = v___y_1909_;
v___y_1858_ = v___y_1910_;
v___y_1859_ = v___y_1911_;
v___y_1860_ = v___y_1912_;
v___y_1861_ = v___y_1913_;
v___y_1862_ = v___y_1914_;
v___y_1863_ = v___y_1915_;
v___y_1864_ = v___y_1916_;
v___y_1865_ = v___x_1923_;
goto v___jp_1847_;
}
else
{
lean_object* v_val_1924_; lean_object* v___x_1925_; 
v_val_1924_ = lean_ctor_get(v_maxSuggestions_1919_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v_maxSuggestions_1919_, 1);
v___x_1925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1925_, 0, v_val_1924_);
lean_ctor_set(v___x_1925_, 1, v___x_1920_);
lean_ctor_set(v___x_1925_, 2, v___f_1201_);
lean_ctor_set(v___x_1925_, 3, v___x_1921_);
v___y_1848_ = v___y_1899_;
v___y_1849_ = v___y_1900_;
v___y_1850_ = v___y_1901_;
v___y_1851_ = v___y_1902_;
v___y_1852_ = v___y_1903_;
v___y_1853_ = v___y_1905_;
v___y_1854_ = v___y_1906_;
v___y_1855_ = v___y_1907_;
v___y_1856_ = v___y_1908_;
v___y_1857_ = v___y_1909_;
v___y_1858_ = v___y_1910_;
v___y_1859_ = v___y_1911_;
v___y_1860_ = v___y_1912_;
v___y_1861_ = v___y_1913_;
v___y_1862_ = v___y_1914_;
v___y_1863_ = v___y_1915_;
v___y_1864_ = v___y_1916_;
v___y_1865_ = v___x_1925_;
goto v___jp_1847_;
}
}
}
v___jp_1926_:
{
uint8_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = 0;
lean_inc(v___y_1939_);
v___x_1943_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1939_, v___x_1942_, v___y_1932_, v___y_1930_, v___y_1935_);
if (lean_obj_tag(v___x_1943_) == 0)
{
if (lean_obj_tag(v___y_1927_) == 1)
{
lean_object* v_a_1944_; lean_object* v_val_1945_; lean_object* v___x_1946_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v_val_1945_ = lean_ctor_get(v___y_1927_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v___y_1927_, 1);
v___x_1946_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1945_);
lean_dec(v_val_1945_);
lean_inc(v___y_1934_);
v___y_1899_ = v___y_1934_;
v___y_1900_ = v___y_1930_;
v___y_1901_ = v___y_1934_;
v___y_1902_ = v___y_1941_;
v___y_1903_ = v___y_1933_;
v___y_1904_ = v_a_1944_;
v___y_1905_ = v___y_1929_;
v___y_1906_ = v___y_1931_;
v___y_1907_ = v___y_1932_;
v___y_1908_ = v___y_1939_;
v___y_1909_ = v___y_1940_;
v___y_1910_ = v___y_1937_;
v___y_1911_ = v___y_1938_;
v___y_1912_ = v___y_1936_;
v___y_1913_ = v___y_1935_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___x_1942_;
v___y_1916_ = v___x_1946_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1948_; 
lean_dec(v___y_1927_);
v_a_1947_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1948_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1934_);
v___y_1899_ = v___y_1934_;
v___y_1900_ = v___y_1930_;
v___y_1901_ = v___y_1934_;
v___y_1902_ = v___y_1941_;
v___y_1903_ = v___y_1933_;
v___y_1904_ = v_a_1947_;
v___y_1905_ = v___y_1929_;
v___y_1906_ = v___y_1931_;
v___y_1907_ = v___y_1932_;
v___y_1908_ = v___y_1939_;
v___y_1909_ = v___y_1940_;
v___y_1910_ = v___y_1937_;
v___y_1911_ = v___y_1938_;
v___y_1912_ = v___y_1936_;
v___y_1913_ = v___y_1935_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___x_1942_;
v___y_1916_ = v___x_1948_;
goto v___jp_1898_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v___y_1941_);
lean_dec(v___y_1939_);
lean_dec(v___y_1934_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v_a_1949_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1943_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1943_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
v___jp_1957_:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Syntax_getOptional_x3f(v___y_1971_);
lean_dec(v___y_1971_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_box(0);
v___y_1927_ = v___y_1968_;
v___y_1928_ = v___y_1970_;
v___y_1929_ = v___y_1960_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1959_;
v___y_1934_ = v___y_1972_;
v___y_1935_ = v___y_1969_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1964_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___y_1963_;
v___y_1940_ = v___y_1965_;
v___y_1941_ = v___x_1974_;
goto v___jp_1926_;
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_val_1975_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1973_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_dec(v___x_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_val_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v___y_1927_ = v___y_1968_;
v___y_1928_ = v___y_1970_;
v___y_1929_ = v___y_1960_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1959_;
v___y_1934_ = v___y_1972_;
v___y_1935_ = v___y_1969_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1964_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___y_1963_;
v___y_1940_ = v___y_1965_;
v___y_1941_ = v___x_1980_;
goto v___jp_1926_;
}
}
}
}
v___jp_1983_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = lean_unsigned_to_nat(4u);
v___x_2000_ = l_Lean_Syntax_getArg(v___y_1986_, v___x_1999_);
lean_dec(v___y_1986_);
v___x_2001_ = l_Lean_Syntax_getOptional_x3f(v___x_2000_);
lean_dec(v___x_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_box(0);
v___y_1958_ = v___y_1997_;
v___y_1959_ = v___y_1993_;
v___y_1960_ = v___y_1987_;
v___y_1961_ = v___y_1995_;
v___y_1962_ = v___y_1991_;
v___y_1963_ = v___y_1984_;
v___y_1964_ = v___y_1985_;
v___y_1965_ = v___y_1992_;
v___y_1966_ = v___y_1996_;
v___y_1967_ = v___y_1994_;
v___y_1968_ = v_args_1990_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_1988_;
v___y_1971_ = v___y_1989_;
v___y_1972_ = v___x_2002_;
goto v___jp_1957_;
}
else
{
lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_val_2003_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_2001_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_dec(v___x_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_val_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
v___y_1958_ = v___y_1997_;
v___y_1959_ = v___y_1993_;
v___y_1960_ = v___y_1987_;
v___y_1961_ = v___y_1995_;
v___y_1962_ = v___y_1991_;
v___y_1963_ = v___y_1984_;
v___y_1964_ = v___y_1985_;
v___y_1965_ = v___y_1992_;
v___y_1966_ = v___y_1996_;
v___y_1967_ = v___y_1994_;
v___y_1968_ = v_args_1990_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_1988_;
v___y_1971_ = v___y_1989_;
v___y_1972_ = v___x_2008_;
goto v___jp_1957_;
}
}
}
}
v___jp_2012_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2027_ = lean_unsigned_to_nat(3u);
v___x_2028_ = l_Lean_Syntax_getArg(v___y_2015_, v___x_2027_);
v___x_2029_ = l_Lean_Syntax_isNone(v___x_2028_);
if (v___x_2029_ == 0)
{
uint8_t v___x_2030_; 
lean_inc(v___x_2028_);
v___x_2030_ = l_Lean_Syntax_matchesNull(v___x_2028_, v___x_2011_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v___x_2028_);
lean_dec(v_o_2018_);
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2013_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_2031_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2031_;
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2032_ = l_Lean_Syntax_getArg(v___x_2028_, v___x_1212_);
lean_dec(v___x_2028_);
v___x_2033_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1200_);
lean_inc_ref(v___x_1199_);
lean_inc_ref(v___x_1198_);
v___x_2034_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_2033_);
lean_inc(v___x_2032_);
v___x_2035_ = l_Lean_Syntax_isOfKind(v___x_2032_, v___x_2034_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec(v___x_2032_);
lean_dec(v_o_2018_);
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2013_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_2036_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; lean_object* v_args_2038_; lean_object* v___x_2039_; 
v___x_2037_ = l_Lean_Syntax_getArg(v___x_2032_, v___x_2011_);
lean_dec(v___x_2032_);
v_args_2038_ = l_Lean_Syntax_getArgs(v___x_2037_);
lean_dec(v___x_2037_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_args_2038_);
v___y_1984_ = v___y_2013_;
v___y_1985_ = v___y_2014_;
v___y_1986_ = v___y_2015_;
v___y_1987_ = v_o_2018_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v_args_1990_ = v___x_2039_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2021_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___y_2023_;
v___y_1996_ = v___y_2024_;
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2026_;
goto v___jp_1983_;
}
}
}
else
{
lean_object* v___x_2040_; 
lean_dec(v___x_2028_);
v___x_2040_ = lean_box(0);
v___y_1984_ = v___y_2013_;
v___y_1985_ = v___y_2014_;
v___y_1986_ = v___y_2015_;
v___y_1987_ = v_o_2018_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v_args_1990_ = v___x_2040_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2021_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___y_2023_;
v___y_1996_ = v___y_2024_;
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2026_;
goto v___jp_1983_;
}
}
v___jp_2041_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2051_ = lean_unsigned_to_nat(2u);
v___x_2052_ = l_Lean_Syntax_getArg(v_stx_1196_, v___x_2051_);
v___x_2053_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1200_);
lean_inc_ref(v___x_1199_);
lean_inc_ref(v___x_1198_);
v___x_2054_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_2053_);
lean_inc(v___x_2052_);
v___x_2055_ = l_Lean_Syntax_isOfKind(v___x_2052_, v___x_2054_);
lean_dec(v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v___x_2052_);
lean_dec(v_bang_2042_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_2056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2056_;
}
else
{
lean_object* v_cfg_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_cfg_2057_ = l_Lean_Syntax_getArg(v___x_2052_, v___x_1212_);
v___x_2058_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1200_);
lean_inc_ref(v___x_1199_);
lean_inc_ref(v___x_1198_);
v___x_2059_ = l_Lean_Name_mkStr4(v___x_1198_, v___x_1199_, v___x_1200_, v___x_2058_);
lean_inc(v_cfg_2057_);
v___x_2060_ = l_Lean_Syntax_isOfKind(v_cfg_2057_, v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec(v_cfg_2057_);
lean_dec(v___x_2052_);
lean_dec(v_bang_2042_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_2061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = l_Lean_Syntax_getArg(v___x_2052_, v___x_2011_);
v___x_2063_ = l_Lean_Syntax_getArg(v___x_2052_, v___x_2051_);
v___x_2064_ = l_Lean_Syntax_isNone(v___x_2063_);
if (v___x_2064_ == 0)
{
uint8_t v___x_2065_; 
lean_inc(v___x_2063_);
v___x_2065_ = l_Lean_Syntax_matchesNull(v___x_2063_, v___x_2011_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; 
lean_dec(v___x_2063_);
lean_dec(v___x_2062_);
lean_dec(v_cfg_2057_);
lean_dec(v___x_2052_);
lean_dec(v_bang_2042_);
lean_dec(v_tk_1213_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
v___x_2066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2066_;
}
else
{
lean_object* v_o_2067_; lean_object* v___x_2068_; 
v_o_2067_ = l_Lean_Syntax_getArg(v___x_2063_, v___x_1212_);
lean_dec(v___x_2063_);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_o_2067_);
v___y_2013_ = v_cfg_2057_;
v___y_2014_ = v___x_2055_;
v___y_2015_ = v___x_2052_;
v___y_2016_ = v_bang_2042_;
v___y_2017_ = v___x_2062_;
v_o_2018_ = v___x_2068_;
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
v___y_2021_ = v___y_2045_;
v___y_2022_ = v___y_2046_;
v___y_2023_ = v___y_2047_;
v___y_2024_ = v___y_2048_;
v___y_2025_ = v___y_2049_;
v___y_2026_ = v___y_2050_;
goto v___jp_2012_;
}
}
else
{
lean_object* v___x_2069_; 
lean_dec(v___x_2063_);
v___x_2069_ = lean_box(0);
v___y_2013_ = v_cfg_2057_;
v___y_2014_ = v___x_2055_;
v___y_2015_ = v___x_2052_;
v___y_2016_ = v_bang_2042_;
v___y_2017_ = v___x_2062_;
v_o_2018_ = v___x_2069_;
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
v___y_2021_ = v___y_2045_;
v___y_2022_ = v___y_2046_;
v___y_2023_ = v___y_2047_;
v___y_2024_ = v___y_2048_;
v___y_2025_ = v___y_2049_;
v___y_2026_ = v___y_2050_;
goto v___jp_2012_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2077_, lean_object* v_stx_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v___f_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_35027__boxed_2093_; uint8_t v___x_35028__boxed_2094_; lean_object* v_res_2095_; 
v___x_35027__boxed_2093_ = lean_unbox(v___x_2077_);
v___x_35028__boxed_2094_ = lean_unbox(v___x_2079_);
v_res_2095_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35027__boxed_2093_, v_stx_2078_, v___x_35028__boxed_2094_, v___x_2080_, v___x_2081_, v___x_2082_, v___f_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v_stx_2078_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; uint8_t v___x_2120_; lean_object* v___f_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___y_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2105_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_stx_2105_, v___x_2118_);
v___x_2120_ = 1;
v___f_2121_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2122_ = lean_box(v___x_2119_);
v___x_2123_ = lean_box(v___x_2120_);
v___y_2124_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2124_, 0, v___x_2122_);
lean_closure_set(v___y_2124_, 1, v_stx_2105_);
lean_closure_set(v___y_2124_, 2, v___x_2123_);
lean_closure_set(v___y_2124_, 3, v___x_2115_);
lean_closure_set(v___y_2124_, 4, v___x_2116_);
lean_closure_set(v___y_2124_, 5, v___x_2117_);
lean_closure_set(v___y_2124_, 6, v___f_2121_);
v___x_2125_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2125_, 0, v___y_2124_);
v___x_2126_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2125_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2138_, lean_object* v_as_2139_, lean_object* v_as_x27_2140_, lean_object* v_b_2141_, lean_object* v_a_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2138_, v_as_x27_2140_, v_b_2141_, v___y_2149_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2153_, lean_object* v_as_2154_, lean_object* v_as_x27_2155_, lean_object* v_b_2156_, lean_object* v_a_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2153_, v_as_2154_, v_as_x27_2155_, v_b_2156_, v_a_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v_as_x27_2155_);
lean_dec(v_as_2154_);
lean_dec(v___x_2153_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2168_, lean_object* v_ref_2169_, lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2169_, v_msg_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_ref_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2181_, v_ref_2182_, v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v_ref_2182_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2194_, lean_object* v_ref_2195_, lean_object* v_constName_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2195_, v_constName_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_ref_2208_, lean_object* v_constName_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2207_, v_ref_2208_, v_constName_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v_ref_2208_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2221_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_msg_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2232_, v_msg_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2244_, v___y_2251_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_opt_2255_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2266_, lean_object* v_ref_2267_, lean_object* v_msg_2268_, lean_object* v_declHint_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2267_, v_msg_2268_, v_declHint_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_ref_2281_, lean_object* v_msg_2282_, lean_object* v_declHint_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2280_, v_ref_2281_, v_msg_2282_, v_declHint_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v_ref_2281_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2294_, lean_object* v_declHint_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2294_, v_declHint_2295_, v___y_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2306_, lean_object* v_declHint_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2306_, v_declHint_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2318_, lean_object* v_msgData_2319_, uint8_t v_severity_2320_, uint8_t v_isSilent_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2318_, v_msgData_2319_, v_severity_2320_, v_isSilent_2321_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2332_, lean_object* v_msgData_2333_, lean_object* v_severity_2334_, lean_object* v_isSilent_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v_severity_boxed_2345_; uint8_t v_isSilent_boxed_2346_; lean_object* v_res_2347_; 
v_severity_boxed_2345_ = lean_unbox(v_severity_2334_);
v_isSilent_boxed_2346_ = lean_unbox(v_isSilent_2335_);
v_res_2347_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2332_, v_msgData_2333_, v_severity_boxed_2345_, v_isSilent_boxed_2346_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v_ref_2332_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2355_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2358_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2359_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2355_, v___x_2356_, v___x_2357_, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2390_ = l_Lean_addBuiltinDeclarationRanges(v___x_2388_, v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2393_, lean_object* v_as_x27_2394_, lean_object* v_b_2395_, lean_object* v___y_2396_){
_start:
{
if (lean_obj_tag(v_as_x27_2394_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_b_2395_);
return v___x_2398_;
}
else
{
lean_object* v_head_2399_; lean_object* v_tail_2400_; lean_object* v_ref_2401_; uint8_t v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_head_2399_ = lean_ctor_get(v_as_x27_2394_, 0);
v_tail_2400_ = lean_ctor_get(v_as_x27_2394_, 1);
v_ref_2401_ = lean_ctor_get(v___y_2396_, 2);
v___x_2402_ = 1;
v___x_2403_ = 0;
v___x_2404_ = l_Lean_SourceInfo_fromRef(v_ref_2401_, v___x_2403_);
v___x_2405_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2406_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2407_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2404_);
v___x_2408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2404_);
lean_ctor_set(v___x_2408_, 1, v___x_2406_);
lean_ctor_set(v___x_2408_, 2, v___x_2407_);
lean_inc(v_head_2399_);
v___x_2409_ = l_Lean_mkCIdentFrom(v___x_2393_, v_head_2399_, v___x_2402_);
lean_inc_ref(v___x_2408_);
v___x_2410_ = l_Lean_Syntax_node3(v___x_2404_, v___x_2405_, v___x_2408_, v___x_2408_, v___x_2409_);
v___x_2411_ = lean_array_push(v_b_2395_, v___x_2410_);
v_as_x27_2394_ = v_tail_2400_;
v_b_2395_ = v___x_2411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2413_, lean_object* v_as_x27_2414_, lean_object* v_b_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2413_, v_as_x27_2414_, v_b_2415_, v___y_2416_);
lean_dec_ref(v___y_2416_);
lean_dec(v_as_x27_2414_);
lean_dec(v___x_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2419_, size_t v_sz_2420_, size_t v_i_2421_, lean_object* v_b_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_usize_dec_lt(v_i_2421_, v_sz_2420_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_b_2422_);
return v___x_2433_;
}
else
{
lean_object* v_a_2434_; lean_object* v_name_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_a_2434_ = lean_array_uget_borrowed(v_as_2419_, v_i_2421_);
v_name_2435_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_name_2435_);
v___x_2436_ = l_Lean_mkIdent(v_name_2435_);
lean_inc(v___x_2436_);
v___x_2437_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2436_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2436_, v_a_2438_, v_b_2422_, v___y_2429_);
lean_dec(v_a_2438_);
lean_dec(v___x_2436_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; size_t v___x_2441_; size_t v___x_2442_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2421_, v___x_2441_);
v_i_2421_ = v___x_2442_;
v_b_2422_ = v_a_2440_;
goto _start;
}
else
{
return v___x_2439_;
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___x_2436_);
lean_dec_ref(v_b_2422_);
v_a_2444_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2437_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2437_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2452_, lean_object* v_sz_2453_, lean_object* v_i_2454_, lean_object* v_b_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
size_t v_sz_boxed_2465_; size_t v_i_boxed_2466_; lean_object* v_res_2467_; 
v_sz_boxed_2465_ = lean_unbox_usize(v_sz_2453_);
lean_dec(v_sz_2453_);
v_i_boxed_2466_ = lean_unbox_usize(v_i_2454_);
lean_dec(v_i_2454_);
v_res_2467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2452_, v_sz_boxed_2465_, v_i_boxed_2466_, v_b_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_as_2452_);
return v_res_2467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2468_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2471_);
return v___x_2473_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_unsigned_to_nat(32u);
v___x_2475_ = lean_mk_empty_array_with_capacity(v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2477_ = ((size_t)5ULL);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_unsigned_to_nat(32u);
v___x_2480_ = lean_mk_empty_array_with_capacity(v___x_2479_);
v___x_2481_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2482_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v___x_2480_);
lean_ctor_set(v___x_2482_, 2, v___x_2478_);
lean_ctor_set(v___x_2482_, 3, v___x_2478_);
lean_ctor_set_usize(v___x_2482_, 4, v___x_2477_);
return v___x_2482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2484_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
lean_ctor_set(v___x_2485_, 2, v___x_2484_);
lean_ctor_set(v___x_2485_, 3, v___x_2483_);
return v___x_2485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2487_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2497_, lean_object* v_stx_2498_, uint8_t v___x_2499_, lean_object* v___x_2500_, lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v___f_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
if (v___x_2497_ == 0)
{
lean_object* v___x_2513_; 
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_2513_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2513_;
}
else
{
lean_object* v___x_2514_; lean_object* v_tk_2515_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2630_; uint8_t v___y_2631_; uint8_t v___y_2632_; lean_object* v___y_2633_; lean_object* v_stxForSuggestion_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; uint8_t v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; uint8_t v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; uint8_t v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; uint8_t v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; uint8_t v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; uint8_t v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; uint8_t v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2790_; lean_object* v___y_2791_; uint8_t v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2815_; lean_object* v___y_2816_; uint8_t v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; uint8_t v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; uint8_t v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; uint8_t v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; uint8_t v___y_2914_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; uint8_t v___y_2932_; uint8_t v___y_2933_; lean_object* v___y_2934_; lean_object* v_stxForExecution_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; uint8_t v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; uint8_t v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; uint8_t v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; uint8_t v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint8_t v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; uint8_t v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; uint8_t v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; uint8_t v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; uint8_t v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; uint8_t v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; uint8_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; uint8_t v___y_3263_; uint8_t v___y_3264_; lean_object* v___y_3265_; lean_object* v_argsArray_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; uint8_t v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; uint8_t v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3391_; lean_object* v___y_3392_; uint8_t v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; uint8_t v___y_3424_; lean_object* v___y_3425_; lean_object* v_args_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___x_3445_; lean_object* v___y_3447_; lean_object* v___y_3448_; uint8_t v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_o_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v_bang_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v_tk_2515_ = l_Lean_Syntax_getArg(v_stx_2498_, v___x_2514_);
v___x_3445_ = lean_unsigned_to_nat(1u);
v___x_3504_ = l_Lean_Syntax_getArg(v_stx_2498_, v___x_3445_);
v___x_3505_ = l_Lean_Syntax_isNone(v___x_3504_);
if (v___x_3505_ == 0)
{
uint8_t v___x_3506_; 
lean_inc(v___x_3504_);
v___x_3506_ = l_Lean_Syntax_matchesNull(v___x_3504_, v___x_3445_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v___x_3504_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_3507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3507_;
}
else
{
lean_object* v_bang_3508_; lean_object* v___x_3509_; 
v_bang_3508_ = l_Lean_Syntax_getArg(v___x_3504_, v___x_2514_);
lean_dec(v___x_3504_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_bang_3508_);
v_bang_3476_ = v___x_3509_;
v___y_3477_ = v___y_2504_;
v___y_3478_ = v___y_2505_;
v___y_3479_ = v___y_2506_;
v___y_3480_ = v___y_2507_;
v___y_3481_ = v___y_2508_;
v___y_3482_ = v___y_2509_;
v___y_3483_ = v___y_2510_;
v___y_3484_ = v___y_2511_;
goto v___jp_3475_;
}
}
else
{
lean_object* v___x_3510_; 
lean_dec(v___x_3504_);
v___x_3510_ = lean_box(0);
v_bang_3476_ = v___x_3510_;
v___y_3477_ = v___y_2504_;
v___y_3478_ = v___y_2505_;
v___y_3479_ = v___y_2506_;
v___y_3480_ = v___y_2507_;
v___y_3481_ = v___y_2508_;
v___y_3482_ = v___y_2509_;
v___y_3483_ = v___y_2510_;
v___y_3484_ = v___y_2511_;
goto v___jp_3475_;
}
v___jp_2516_:
{
lean_object* v_usedTheorems_2523_; lean_object* v_diag_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2566_; 
v_usedTheorems_2523_ = lean_ctor_get(v___y_2518_, 0);
v_diag_2524_ = lean_ctor_get(v___y_2518_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___y_2518_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2526_ = v___y_2518_;
v_isShared_2527_ = v_isSharedCheck_2566_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_diag_2524_);
lean_inc(v_usedTheorems_2523_);
lean_dec(v___y_2518_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2566_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2517_, v_usedTheorems_2523_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec_ref(v_usedTheorems_2523_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v_ref_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v_ref_2530_ = lean_ctor_get(v___y_2521_, 2);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v_a_2529_);
lean_ctor_set(v___x_2526_, 0, v___x_2531_);
v___x_2533_ = v___x_2526_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2529_);
v___x_2533_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2534_ = lean_box(0);
v___x_2535_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
lean_ctor_set(v___x_2535_, 2, v___x_2534_);
lean_ctor_set(v___x_2535_, 3, v___x_2534_);
lean_ctor_set(v___x_2535_, 4, v___x_2534_);
lean_ctor_set(v___x_2535_, 5, v___x_2534_);
lean_inc(v_ref_2530_);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_ref_2530_);
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2538_ = 4;
v___x_2539_ = l_Lean_MessageData_nil;
v___x_2540_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2515_, v___x_2535_, v___x_2536_, v___x_2537_, v___x_2534_, v___x_2538_, v___x_2539_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v___x_2540_, 0);
lean_dec(v_unused_2548_);
v___x_2542_ = v___x_2540_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_dec(v___x_2540_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_diag_2524_);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_diag_2524_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_diag_2524_);
v_a_2549_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2540_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2540_);
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
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_del_object(v___x_2526_);
lean_dec_ref(v_diag_2524_);
lean_dec(v_tk_2515_);
v_a_2558_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2528_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2528_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
v___jp_2567_:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2571_, v___y_2568_, v___y_2570_, v___y_2573_, v___y_2569_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2579_ = l_Lean_Meta_simpAll(v_a_2577_, v___y_2575_, v___y_2574_, v___x_2578_, v___y_2568_, v___y_2570_, v___y_2573_, v___y_2569_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v_fst_2581_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v_fst_2581_ = lean_ctor_get(v_a_2580_, 0);
if (lean_obj_tag(v_fst_2581_) == 0)
{
lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_snd_2582_ = lean_ctor_get(v_a_2580_, 1);
lean_inc(v_snd_2582_);
lean_dec(v_a_2580_);
v___x_2583_ = lean_box(0);
v___x_2584_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2583_, v___y_2571_, v___y_2568_, v___y_2570_, v___y_2573_, v___y_2569_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v___y_2517_ = v___y_2572_;
v___y_2518_ = v_snd_2582_;
v___y_2519_ = v___y_2568_;
v___y_2520_ = v___y_2570_;
v___y_2521_ = v___y_2573_;
v___y_2522_ = v___y_2569_;
goto v___jp_2516_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_snd_2582_);
lean_dec(v___y_2572_);
lean_dec(v_tk_2515_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_snd_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2611_; 
lean_inc_ref(v_fst_2581_);
v_snd_2593_ = lean_ctor_get(v_a_2580_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2580_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v_a_2580_, 0);
lean_dec(v_unused_2612_);
v___x_2595_ = v_a_2580_;
v_isShared_2596_ = v_isSharedCheck_2611_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snd_2593_);
lean_dec(v_a_2580_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2611_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_val_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v_val_2597_ = lean_ctor_get(v_fst_2581_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v_fst_2581_, 1);
v___x_2598_ = lean_box(0);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 1);
lean_ctor_set(v___x_2595_, 1, v___x_2598_);
lean_ctor_set(v___x_2595_, 0, v_val_2597_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_val_2597_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2600_, v___y_2571_, v___y_2568_, v___y_2570_, v___y_2573_, v___y_2569_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref_known(v___x_2601_, 1);
v___y_2517_ = v___y_2572_;
v___y_2518_ = v_snd_2593_;
v___y_2519_ = v___y_2568_;
v___y_2520_ = v___y_2570_;
v___y_2521_ = v___y_2573_;
v___y_2522_ = v___y_2569_;
goto v___jp_2516_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_snd_2593_);
lean_dec(v___y_2572_);
lean_dec(v_tk_2515_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___y_2572_);
lean_dec(v_tk_2515_);
v_a_2613_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2579_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2579_);
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
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2572_);
lean_dec(v_tk_2515_);
v_a_2621_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2576_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2576_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
v___jp_2629_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2644_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2633_, v___x_2499_, v___y_2631_, v___x_2499_, v___x_2643_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2633_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
if (lean_obj_tag(v___y_2630_) == 0)
{
lean_object* v_ctx_2646_; lean_object* v_simprocs_2647_; 
v_ctx_2646_ = lean_ctor_get(v_a_2645_, 0);
lean_inc_ref(v_ctx_2646_);
v_simprocs_2647_ = lean_ctor_get(v_a_2645_, 1);
lean_inc_ref(v_simprocs_2647_);
lean_dec(v_a_2645_);
v___y_2568_ = v___y_2639_;
v___y_2569_ = v___y_2642_;
v___y_2570_ = v___y_2640_;
v___y_2571_ = v___y_2636_;
v___y_2572_ = v_stxForSuggestion_2634_;
v___y_2573_ = v___y_2641_;
v___y_2574_ = v_simprocs_2647_;
v___y_2575_ = v_ctx_2646_;
goto v___jp_2567_;
}
else
{
lean_dec_ref_known(v___y_2630_, 1);
if (v___y_2632_ == 0)
{
lean_object* v_ctx_2648_; lean_object* v_simprocs_2649_; 
v_ctx_2648_ = lean_ctor_get(v_a_2645_, 0);
lean_inc_ref(v_ctx_2648_);
v_simprocs_2649_ = lean_ctor_get(v_a_2645_, 1);
lean_inc_ref(v_simprocs_2649_);
lean_dec(v_a_2645_);
v___y_2568_ = v___y_2639_;
v___y_2569_ = v___y_2642_;
v___y_2570_ = v___y_2640_;
v___y_2571_ = v___y_2636_;
v___y_2572_ = v_stxForSuggestion_2634_;
v___y_2573_ = v___y_2641_;
v___y_2574_ = v_simprocs_2649_;
v___y_2575_ = v_ctx_2648_;
goto v___jp_2567_;
}
else
{
lean_object* v_ctx_2650_; lean_object* v_simprocs_2651_; lean_object* v___x_2652_; 
v_ctx_2650_ = lean_ctor_get(v_a_2645_, 0);
lean_inc_ref(v_ctx_2650_);
v_simprocs_2651_ = lean_ctor_get(v_a_2645_, 1);
lean_inc_ref(v_simprocs_2651_);
lean_dec(v_a_2645_);
v___x_2652_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2650_);
v___y_2568_ = v___y_2639_;
v___y_2569_ = v___y_2642_;
v___y_2570_ = v___y_2640_;
v___y_2571_ = v___y_2636_;
v___y_2572_ = v_stxForSuggestion_2634_;
v___y_2573_ = v___y_2641_;
v___y_2574_ = v_simprocs_2651_;
v___y_2575_ = v___x_2652_;
goto v___jp_2567_;
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_stxForSuggestion_2634_);
lean_dec(v___y_2630_);
lean_dec(v_tk_2515_);
v_a_2653_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2644_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
v___jp_2661_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_inc_ref_n(v___y_2663_, 2);
v___x_2683_ = l_Array_append___redArg(v___y_2663_, v___y_2682_);
lean_dec_ref(v___y_2682_);
lean_inc_n(v___y_2666_, 3);
lean_inc_n(v___y_2664_, 5);
v___x_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2684_, 0, v___y_2664_);
lean_ctor_set(v___x_2684_, 1, v___y_2666_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
v___x_2685_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___y_2664_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2688_ = l_Lean_Syntax_SepArray_ofElems(v___x_2687_, v___y_2662_);
lean_dec_ref(v___y_2662_);
v___x_2689_ = l_Array_append___redArg(v___y_2663_, v___x_2688_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2690_, 0, v___y_2664_);
lean_ctor_set(v___x_2690_, 1, v___y_2666_);
lean_ctor_set(v___x_2690_, 2, v___x_2689_);
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___y_2664_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_Syntax_node3(v___y_2664_, v___y_2666_, v___x_2686_, v___x_2690_, v___x_2692_);
v___x_2694_ = l_Lean_Syntax_node5(v___y_2664_, v___y_2669_, v___y_2680_, v___y_2667_, v___y_2672_, v___x_2684_, v___x_2693_);
v___y_2630_ = v___y_2674_;
v___y_2631_ = v___y_2676_;
v___y_2632_ = v___y_2668_;
v___y_2633_ = v___y_2671_;
v_stxForSuggestion_2634_ = v___x_2694_;
v___y_2635_ = v___y_2679_;
v___y_2636_ = v___y_2681_;
v___y_2637_ = v___y_2678_;
v___y_2638_ = v___y_2665_;
v___y_2639_ = v___y_2670_;
v___y_2640_ = v___y_2673_;
v___y_2641_ = v___y_2675_;
v___y_2642_ = v___y_2677_;
goto v___jp_2629_;
}
v___jp_2695_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_inc_ref(v___y_2697_);
v___x_2717_ = l_Array_append___redArg(v___y_2697_, v___y_2716_);
lean_dec_ref(v___y_2716_);
lean_inc(v___y_2700_);
lean_inc(v___y_2698_);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___y_2698_);
lean_ctor_set(v___x_2718_, 1, v___y_2700_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
if (lean_obj_tag(v___y_2705_) == 1)
{
lean_object* v_val_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_val_2719_ = lean_ctor_get(v___y_2705_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v___y_2705_, 1);
v___x_2720_ = l_Lean_SourceInfo_fromRef(v_val_2719_, v___x_2499_);
lean_dec(v_val_2719_);
v___x_2721_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = l_Array_mkArray1___redArg(v___x_2722_);
v___y_2662_ = v___y_2696_;
v___y_2663_ = v___y_2697_;
v___y_2664_ = v___y_2698_;
v___y_2665_ = v___y_2699_;
v___y_2666_ = v___y_2700_;
v___y_2667_ = v___y_2701_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2706_;
v___y_2672_ = v___x_2718_;
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2708_;
v___y_2675_ = v___y_2709_;
v___y_2676_ = v___y_2710_;
v___y_2677_ = v___y_2712_;
v___y_2678_ = v___y_2711_;
v___y_2679_ = v___y_2713_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___y_2714_;
v___y_2682_ = v___x_2723_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2724_; 
lean_dec(v___y_2705_);
v___x_2724_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2662_ = v___y_2696_;
v___y_2663_ = v___y_2697_;
v___y_2664_ = v___y_2698_;
v___y_2665_ = v___y_2699_;
v___y_2666_ = v___y_2700_;
v___y_2667_ = v___y_2701_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2706_;
v___y_2672_ = v___x_2718_;
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2708_;
v___y_2675_ = v___y_2709_;
v___y_2676_ = v___y_2710_;
v___y_2677_ = v___y_2712_;
v___y_2678_ = v___y_2711_;
v___y_2679_ = v___y_2713_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___y_2714_;
v___y_2682_ = v___x_2724_;
goto v___jp_2661_;
}
}
v___jp_2725_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_inc_ref_n(v___y_2734_, 2);
v___x_2747_ = l_Array_append___redArg(v___y_2734_, v___y_2746_);
lean_dec_ref(v___y_2746_);
lean_inc_n(v___y_2727_, 3);
lean_inc_n(v___y_2736_, 5);
v___x_2748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___y_2736_);
lean_ctor_set(v___x_2748_, 1, v___y_2727_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2736_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2752_ = l_Lean_Syntax_SepArray_ofElems(v___x_2751_, v___y_2726_);
lean_dec_ref(v___y_2726_);
v___x_2753_ = l_Array_append___redArg(v___y_2734_, v___x_2752_);
lean_dec_ref(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2754_, 0, v___y_2736_);
lean_ctor_set(v___x_2754_, 1, v___y_2727_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___y_2736_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_Syntax_node3(v___y_2736_, v___y_2727_, v___x_2750_, v___x_2754_, v___x_2756_);
v___x_2758_ = l_Lean_Syntax_node5(v___y_2736_, v___y_2733_, v___y_2740_, v___y_2729_, v___y_2743_, v___x_2748_, v___x_2757_);
v___y_2630_ = v___y_2737_;
v___y_2631_ = v___y_2739_;
v___y_2632_ = v___y_2730_;
v___y_2633_ = v___y_2732_;
v_stxForSuggestion_2634_ = v___x_2758_;
v___y_2635_ = v___y_2744_;
v___y_2636_ = v___y_2745_;
v___y_2637_ = v___y_2742_;
v___y_2638_ = v___y_2728_;
v___y_2639_ = v___y_2731_;
v___y_2640_ = v___y_2735_;
v___y_2641_ = v___y_2738_;
v___y_2642_ = v___y_2741_;
goto v___jp_2629_;
}
v___jp_2759_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_inc_ref(v___y_2769_);
v___x_2781_ = l_Array_append___redArg(v___y_2769_, v___y_2780_);
lean_dec_ref(v___y_2780_);
lean_inc(v___y_2761_);
lean_inc(v___y_2771_);
v___x_2782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2782_, 0, v___y_2771_);
lean_ctor_set(v___x_2782_, 1, v___y_2761_);
lean_ctor_set(v___x_2782_, 2, v___x_2781_);
if (lean_obj_tag(v___y_2766_) == 1)
{
lean_object* v_val_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_val_2783_ = lean_ctor_get(v___y_2766_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v___y_2766_, 1);
v___x_2784_ = l_Lean_SourceInfo_fromRef(v_val_2783_, v___x_2499_);
lean_dec(v_val_2783_);
v___x_2785_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = l_Array_mkArray1___redArg(v___x_2786_);
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2767_;
v___y_2733_ = v___y_2768_;
v___y_2734_ = v___y_2769_;
v___y_2735_ = v___y_2770_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___y_2772_;
v___y_2738_ = v___y_2773_;
v___y_2739_ = v___y_2774_;
v___y_2740_ = v___y_2775_;
v___y_2741_ = v___y_2777_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___x_2782_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___x_2787_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2788_; 
lean_dec(v___y_2766_);
v___x_2788_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2767_;
v___y_2733_ = v___y_2768_;
v___y_2734_ = v___y_2769_;
v___y_2735_ = v___y_2770_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___y_2772_;
v___y_2738_ = v___y_2773_;
v___y_2739_ = v___y_2774_;
v___y_2740_ = v___y_2775_;
v___y_2741_ = v___y_2777_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___x_2782_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___x_2788_;
goto v___jp_2725_;
}
}
v___jp_2789_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_inc_ref_n(v___y_2804_, 2);
v___x_2810_ = l_Array_append___redArg(v___y_2804_, v___y_2809_);
lean_dec_ref(v___y_2809_);
lean_inc_n(v___y_2797_, 2);
lean_inc_n(v___y_2801_, 2);
v___x_2811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2811_, 0, v___y_2801_);
lean_ctor_set(v___x_2811_, 1, v___y_2797_);
lean_ctor_set(v___x_2811_, 2, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2812_, 0, v___y_2801_);
lean_ctor_set(v___x_2812_, 1, v___y_2797_);
lean_ctor_set(v___x_2812_, 2, v___y_2804_);
v___x_2813_ = l_Lean_Syntax_node5(v___y_2801_, v___y_2793_, v___y_2799_, v___y_2791_, v___y_2807_, v___x_2811_, v___x_2812_);
v___y_2630_ = v___y_2798_;
v___y_2631_ = v___y_2802_;
v___y_2632_ = v___y_2792_;
v___y_2633_ = v___y_2795_;
v_stxForSuggestion_2634_ = v___x_2813_;
v___y_2635_ = v___y_2806_;
v___y_2636_ = v___y_2808_;
v___y_2637_ = v___y_2805_;
v___y_2638_ = v___y_2790_;
v___y_2639_ = v___y_2794_;
v___y_2640_ = v___y_2796_;
v___y_2641_ = v___y_2800_;
v___y_2642_ = v___y_2803_;
goto v___jp_2629_;
}
v___jp_2814_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_inc_ref(v___y_2831_);
v___x_2835_ = l_Array_append___redArg(v___y_2831_, v___y_2834_);
lean_dec_ref(v___y_2834_);
lean_inc(v___y_2823_);
lean_inc(v___y_2827_);
v___x_2836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2836_, 0, v___y_2827_);
lean_ctor_set(v___x_2836_, 1, v___y_2823_);
lean_ctor_set(v___x_2836_, 2, v___x_2835_);
if (lean_obj_tag(v___y_2820_) == 1)
{
lean_object* v_val_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_val_2837_ = lean_ctor_get(v___y_2820_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v___y_2820_, 1);
v___x_2838_ = l_Lean_SourceInfo_fromRef(v_val_2837_, v___x_2499_);
lean_dec(v_val_2837_);
v___x_2839_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Array_mkArray1___redArg(v___x_2840_);
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2817_;
v___y_2793_ = v___y_2818_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2821_;
v___y_2796_ = v___y_2822_;
v___y_2797_ = v___y_2823_;
v___y_2798_ = v___y_2824_;
v___y_2799_ = v___y_2825_;
v___y_2800_ = v___y_2826_;
v___y_2801_ = v___y_2827_;
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2830_;
v___y_2804_ = v___y_2831_;
v___y_2805_ = v___y_2829_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___x_2836_;
v___y_2808_ = v___y_2833_;
v___y_2809_ = v___x_2841_;
goto v___jp_2789_;
}
else
{
lean_object* v___x_2842_; 
lean_dec(v___y_2820_);
v___x_2842_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2817_;
v___y_2793_ = v___y_2818_;
v___y_2794_ = v___y_2819_;
v___y_2795_ = v___y_2821_;
v___y_2796_ = v___y_2822_;
v___y_2797_ = v___y_2823_;
v___y_2798_ = v___y_2824_;
v___y_2799_ = v___y_2825_;
v___y_2800_ = v___y_2826_;
v___y_2801_ = v___y_2827_;
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2830_;
v___y_2804_ = v___y_2831_;
v___y_2805_ = v___y_2829_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___x_2836_;
v___y_2808_ = v___y_2833_;
v___y_2809_ = v___x_2842_;
goto v___jp_2789_;
}
}
v___jp_2843_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_inc_ref_n(v___y_2851_, 2);
v___x_2864_ = l_Array_append___redArg(v___y_2851_, v___y_2863_);
lean_dec_ref(v___y_2863_);
lean_inc_n(v___y_2858_, 2);
lean_inc_n(v___y_2846_, 2);
v___x_2865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2865_, 0, v___y_2846_);
lean_ctor_set(v___x_2865_, 1, v___y_2858_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2866_, 0, v___y_2846_);
lean_ctor_set(v___x_2866_, 1, v___y_2858_);
lean_ctor_set(v___x_2866_, 2, v___y_2851_);
v___x_2867_ = l_Lean_Syntax_node5(v___y_2846_, v___y_2852_, v___y_2859_, v___y_2845_, v___y_2861_, v___x_2865_, v___x_2866_);
v___y_2630_ = v___y_2853_;
v___y_2631_ = v___y_2855_;
v___y_2632_ = v___y_2847_;
v___y_2633_ = v___y_2849_;
v_stxForSuggestion_2634_ = v___x_2867_;
v___y_2635_ = v___y_2860_;
v___y_2636_ = v___y_2862_;
v___y_2637_ = v___y_2857_;
v___y_2638_ = v___y_2844_;
v___y_2639_ = v___y_2848_;
v___y_2640_ = v___y_2850_;
v___y_2641_ = v___y_2854_;
v___y_2642_ = v___y_2856_;
goto v___jp_2629_;
}
v___jp_2868_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_inc_ref(v___y_2877_);
v___x_2889_ = l_Array_append___redArg(v___y_2877_, v___y_2888_);
lean_dec_ref(v___y_2888_);
lean_inc(v___y_2886_);
lean_inc(v___y_2871_);
v___x_2890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___y_2871_);
lean_ctor_set(v___x_2890_, 1, v___y_2886_);
lean_ctor_set(v___x_2890_, 2, v___x_2889_);
if (lean_obj_tag(v___y_2874_) == 1)
{
lean_object* v_val_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_val_2891_ = lean_ctor_get(v___y_2874_, 0);
lean_inc(v_val_2891_);
lean_dec_ref_known(v___y_2874_, 1);
v___x_2892_ = l_Lean_SourceInfo_fromRef(v_val_2891_, v___x_2499_);
lean_dec(v_val_2891_);
v___x_2893_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = l_Array_mkArray1___redArg(v___x_2894_);
v___y_2844_ = v___y_2869_;
v___y_2845_ = v___y_2870_;
v___y_2846_ = v___y_2871_;
v___y_2847_ = v___y_2872_;
v___y_2848_ = v___y_2873_;
v___y_2849_ = v___y_2875_;
v___y_2850_ = v___y_2876_;
v___y_2851_ = v___y_2877_;
v___y_2852_ = v___y_2878_;
v___y_2853_ = v___y_2879_;
v___y_2854_ = v___y_2880_;
v___y_2855_ = v___y_2881_;
v___y_2856_ = v___y_2883_;
v___y_2857_ = v___y_2882_;
v___y_2858_ = v___y_2886_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2884_;
v___y_2861_ = v___x_2890_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___x_2895_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2896_; 
lean_dec(v___y_2874_);
v___x_2896_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2844_ = v___y_2869_;
v___y_2845_ = v___y_2870_;
v___y_2846_ = v___y_2871_;
v___y_2847_ = v___y_2872_;
v___y_2848_ = v___y_2873_;
v___y_2849_ = v___y_2875_;
v___y_2850_ = v___y_2876_;
v___y_2851_ = v___y_2877_;
v___y_2852_ = v___y_2878_;
v___y_2853_ = v___y_2879_;
v___y_2854_ = v___y_2880_;
v___y_2855_ = v___y_2881_;
v___y_2856_ = v___y_2883_;
v___y_2857_ = v___y_2882_;
v___y_2858_ = v___y_2886_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2884_;
v___y_2861_ = v___x_2890_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___x_2896_;
goto v___jp_2843_;
}
}
v___jp_2897_:
{
lean_object* v_ref_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_ref_2915_ = lean_ctor_get(v___y_2908_, 2);
v___x_2916_ = l_Lean_SourceInfo_fromRef(v_ref_2915_, v___y_2914_);
v___x_2917_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2918_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_2917_);
v___x_2919_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2923_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2906_) == 1)
{
lean_object* v_val_2924_; lean_object* v___x_2925_; 
v_val_2924_ = lean_ctor_get(v___y_2906_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v___y_2906_, 1);
v___x_2925_ = l_Array_mkArray1___redArg(v_val_2924_);
v___y_2696_ = v___y_2898_;
v___y_2697_ = v___x_2923_;
v___y_2698_ = v___x_2916_;
v___y_2699_ = v___y_2899_;
v___y_2700_ = v___x_2922_;
v___y_2701_ = v___y_2900_;
v___y_2702_ = v___y_2901_;
v___y_2703_ = v___x_2918_;
v___y_2704_ = v___y_2902_;
v___y_2705_ = v___y_2903_;
v___y_2706_ = v___y_2904_;
v___y_2707_ = v___y_2905_;
v___y_2708_ = v___y_2907_;
v___y_2709_ = v___y_2908_;
v___y_2710_ = v___y_2909_;
v___y_2711_ = v___y_2911_;
v___y_2712_ = v___y_2910_;
v___y_2713_ = v___y_2912_;
v___y_2714_ = v___y_2913_;
v___y_2715_ = v___x_2921_;
v___y_2716_ = v___x_2925_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2926_; 
lean_dec(v___y_2906_);
v___x_2926_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2696_ = v___y_2898_;
v___y_2697_ = v___x_2923_;
v___y_2698_ = v___x_2916_;
v___y_2699_ = v___y_2899_;
v___y_2700_ = v___x_2922_;
v___y_2701_ = v___y_2900_;
v___y_2702_ = v___y_2901_;
v___y_2703_ = v___x_2918_;
v___y_2704_ = v___y_2902_;
v___y_2705_ = v___y_2903_;
v___y_2706_ = v___y_2904_;
v___y_2707_ = v___y_2905_;
v___y_2708_ = v___y_2907_;
v___y_2709_ = v___y_2908_;
v___y_2710_ = v___y_2909_;
v___y_2711_ = v___y_2911_;
v___y_2712_ = v___y_2910_;
v___y_2713_ = v___y_2912_;
v___y_2714_ = v___y_2913_;
v___y_2715_ = v___x_2921_;
v___y_2716_ = v___x_2926_;
goto v___jp_2695_;
}
}
v___jp_2927_:
{
lean_object* v___x_2944_; lean_object* v_a_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2944_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2930_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = lean_array_get_size(v___y_2928_);
v___x_2947_ = lean_nat_dec_eq(v___x_2946_, v___x_2514_);
if (v___x_2947_ == 0)
{
if (lean_obj_tag(v___y_2931_) == 0)
{
v___y_2898_ = v___y_2928_;
v___y_2899_ = v___y_2939_;
v___y_2900_ = v_a_2945_;
v___y_2901_ = v___y_2933_;
v___y_2902_ = v___y_2940_;
v___y_2903_ = v___y_2934_;
v___y_2904_ = v_stxForExecution_2935_;
v___y_2905_ = v___y_2941_;
v___y_2906_ = v___y_2929_;
v___y_2907_ = v___y_2931_;
v___y_2908_ = v___y_2942_;
v___y_2909_ = v___y_2932_;
v___y_2910_ = v___y_2943_;
v___y_2911_ = v___y_2938_;
v___y_2912_ = v___y_2936_;
v___y_2913_ = v___y_2937_;
v___y_2914_ = v___x_2947_;
goto v___jp_2897_;
}
else
{
if (v___y_2933_ == 0)
{
v___y_2898_ = v___y_2928_;
v___y_2899_ = v___y_2939_;
v___y_2900_ = v_a_2945_;
v___y_2901_ = v___y_2933_;
v___y_2902_ = v___y_2940_;
v___y_2903_ = v___y_2934_;
v___y_2904_ = v_stxForExecution_2935_;
v___y_2905_ = v___y_2941_;
v___y_2906_ = v___y_2929_;
v___y_2907_ = v___y_2931_;
v___y_2908_ = v___y_2942_;
v___y_2909_ = v___y_2932_;
v___y_2910_ = v___y_2943_;
v___y_2911_ = v___y_2938_;
v___y_2912_ = v___y_2936_;
v___y_2913_ = v___y_2937_;
v___y_2914_ = v___y_2933_;
goto v___jp_2897_;
}
else
{
lean_object* v_ref_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_ref_2948_ = lean_ctor_get(v___y_2942_, 2);
v___x_2949_ = l_Lean_SourceInfo_fromRef(v_ref_2948_, v___x_2947_);
v___x_2950_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2951_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_2950_);
v___x_2952_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_2953_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2956_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2929_) == 1)
{
lean_object* v_val_2957_; lean_object* v___x_2958_; 
v_val_2957_ = lean_ctor_get(v___y_2929_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v___y_2929_, 1);
v___x_2958_ = l_Array_mkArray1___redArg(v_val_2957_);
v___y_2760_ = v___y_2928_;
v___y_2761_ = v___x_2955_;
v___y_2762_ = v___y_2939_;
v___y_2763_ = v_a_2945_;
v___y_2764_ = v___y_2933_;
v___y_2765_ = v___y_2940_;
v___y_2766_ = v___y_2934_;
v___y_2767_ = v_stxForExecution_2935_;
v___y_2768_ = v___x_2951_;
v___y_2769_ = v___x_2956_;
v___y_2770_ = v___y_2941_;
v___y_2771_ = v___x_2949_;
v___y_2772_ = v___y_2931_;
v___y_2773_ = v___y_2942_;
v___y_2774_ = v___y_2932_;
v___y_2775_ = v___x_2954_;
v___y_2776_ = v___y_2938_;
v___y_2777_ = v___y_2943_;
v___y_2778_ = v___y_2936_;
v___y_2779_ = v___y_2937_;
v___y_2780_ = v___x_2958_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2959_; 
lean_dec(v___y_2929_);
v___x_2959_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2760_ = v___y_2928_;
v___y_2761_ = v___x_2955_;
v___y_2762_ = v___y_2939_;
v___y_2763_ = v_a_2945_;
v___y_2764_ = v___y_2933_;
v___y_2765_ = v___y_2940_;
v___y_2766_ = v___y_2934_;
v___y_2767_ = v_stxForExecution_2935_;
v___y_2768_ = v___x_2951_;
v___y_2769_ = v___x_2956_;
v___y_2770_ = v___y_2941_;
v___y_2771_ = v___x_2949_;
v___y_2772_ = v___y_2931_;
v___y_2773_ = v___y_2942_;
v___y_2774_ = v___y_2932_;
v___y_2775_ = v___x_2954_;
v___y_2776_ = v___y_2938_;
v___y_2777_ = v___y_2943_;
v___y_2778_ = v___y_2936_;
v___y_2779_ = v___y_2937_;
v___y_2780_ = v___x_2959_;
goto v___jp_2759_;
}
}
}
}
else
{
lean_dec_ref(v___y_2928_);
if (lean_obj_tag(v___y_2931_) == 0)
{
lean_object* v_ref_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_ref_2960_ = lean_ctor_get(v___y_2942_, 2);
v___x_2961_ = 0;
v___x_2962_ = l_Lean_SourceInfo_fromRef(v_ref_2960_, v___x_2961_);
v___x_2963_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2964_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_2963_);
v___x_2965_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2969_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2929_) == 1)
{
lean_object* v_val_2970_; lean_object* v___x_2971_; 
v_val_2970_ = lean_ctor_get(v___y_2929_, 0);
lean_inc(v_val_2970_);
lean_dec_ref_known(v___y_2929_, 1);
v___x_2971_ = l_Array_mkArray1___redArg(v_val_2970_);
v___y_2815_ = v___y_2939_;
v___y_2816_ = v_a_2945_;
v___y_2817_ = v___y_2933_;
v___y_2818_ = v___x_2964_;
v___y_2819_ = v___y_2940_;
v___y_2820_ = v___y_2934_;
v___y_2821_ = v_stxForExecution_2935_;
v___y_2822_ = v___y_2941_;
v___y_2823_ = v___x_2968_;
v___y_2824_ = v___y_2931_;
v___y_2825_ = v___x_2967_;
v___y_2826_ = v___y_2942_;
v___y_2827_ = v___x_2962_;
v___y_2828_ = v___y_2932_;
v___y_2829_ = v___y_2938_;
v___y_2830_ = v___y_2943_;
v___y_2831_ = v___x_2969_;
v___y_2832_ = v___y_2936_;
v___y_2833_ = v___y_2937_;
v___y_2834_ = v___x_2971_;
goto v___jp_2814_;
}
else
{
lean_object* v___x_2972_; 
lean_dec(v___y_2929_);
v___x_2972_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2815_ = v___y_2939_;
v___y_2816_ = v_a_2945_;
v___y_2817_ = v___y_2933_;
v___y_2818_ = v___x_2964_;
v___y_2819_ = v___y_2940_;
v___y_2820_ = v___y_2934_;
v___y_2821_ = v_stxForExecution_2935_;
v___y_2822_ = v___y_2941_;
v___y_2823_ = v___x_2968_;
v___y_2824_ = v___y_2931_;
v___y_2825_ = v___x_2967_;
v___y_2826_ = v___y_2942_;
v___y_2827_ = v___x_2962_;
v___y_2828_ = v___y_2932_;
v___y_2829_ = v___y_2938_;
v___y_2830_ = v___y_2943_;
v___y_2831_ = v___x_2969_;
v___y_2832_ = v___y_2936_;
v___y_2833_ = v___y_2937_;
v___y_2834_ = v___x_2972_;
goto v___jp_2814_;
}
}
else
{
lean_object* v_ref_2973_; uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_ref_2973_ = lean_ctor_get(v___y_2942_, 2);
v___x_2974_ = 0;
v___x_2975_ = l_Lean_SourceInfo_fromRef(v_ref_2973_, v___x_2974_);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2977_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_2976_);
v___x_2978_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2982_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2929_) == 1)
{
lean_object* v_val_2983_; lean_object* v___x_2984_; 
v_val_2983_ = lean_ctor_get(v___y_2929_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v___y_2929_, 1);
v___x_2984_ = l_Array_mkArray1___redArg(v_val_2983_);
v___y_2869_ = v___y_2939_;
v___y_2870_ = v_a_2945_;
v___y_2871_ = v___x_2975_;
v___y_2872_ = v___y_2933_;
v___y_2873_ = v___y_2940_;
v___y_2874_ = v___y_2934_;
v___y_2875_ = v_stxForExecution_2935_;
v___y_2876_ = v___y_2941_;
v___y_2877_ = v___x_2982_;
v___y_2878_ = v___x_2977_;
v___y_2879_ = v___y_2931_;
v___y_2880_ = v___y_2942_;
v___y_2881_ = v___y_2932_;
v___y_2882_ = v___y_2938_;
v___y_2883_ = v___y_2943_;
v___y_2884_ = v___y_2936_;
v___y_2885_ = v___x_2980_;
v___y_2886_ = v___x_2981_;
v___y_2887_ = v___y_2937_;
v___y_2888_ = v___x_2984_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2985_; 
lean_dec(v___y_2929_);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2869_ = v___y_2939_;
v___y_2870_ = v_a_2945_;
v___y_2871_ = v___x_2975_;
v___y_2872_ = v___y_2933_;
v___y_2873_ = v___y_2940_;
v___y_2874_ = v___y_2934_;
v___y_2875_ = v_stxForExecution_2935_;
v___y_2876_ = v___y_2941_;
v___y_2877_ = v___x_2982_;
v___y_2878_ = v___x_2977_;
v___y_2879_ = v___y_2931_;
v___y_2880_ = v___y_2942_;
v___y_2881_ = v___y_2932_;
v___y_2882_ = v___y_2938_;
v___y_2883_ = v___y_2943_;
v___y_2884_ = v___y_2936_;
v___y_2885_ = v___x_2980_;
v___y_2886_ = v___x_2981_;
v___y_2887_ = v___y_2937_;
v___y_2888_ = v___x_2985_;
goto v___jp_2868_;
}
}
}
}
v___jp_2986_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_inc_ref_n(v___y_2996_, 2);
v___x_3009_ = l_Array_append___redArg(v___y_2996_, v___y_3008_);
lean_dec_ref(v___y_3008_);
lean_inc_n(v___y_2992_, 3);
lean_inc_n(v___y_2999_, 5);
v___x_3010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3010_, 0, v___y_2999_);
lean_ctor_set(v___x_3010_, 1, v___y_2992_);
lean_ctor_set(v___x_3010_, 2, v___x_3009_);
v___x_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___y_2999_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3014_ = l_Lean_Syntax_SepArray_ofElems(v___x_3013_, v___y_2987_);
v___x_3015_ = l_Array_append___redArg(v___y_2996_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3016_, 0, v___y_2999_);
lean_ctor_set(v___x_3016_, 1, v___y_2992_);
lean_ctor_set(v___x_3016_, 2, v___x_3015_);
v___x_3017_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___y_2999_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_Syntax_node3(v___y_2999_, v___y_2992_, v___x_3012_, v___x_3016_, v___x_3018_);
lean_inc(v___y_2991_);
v___x_3020_ = l_Lean_Syntax_node5(v___y_2999_, v___y_3006_, v___y_3002_, v___y_2991_, v___y_3004_, v___x_3010_, v___x_3019_);
v___y_2928_ = v___y_2987_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___y_2991_;
v___y_2931_ = v___y_3001_;
v___y_2932_ = v___y_3003_;
v___y_2933_ = v___y_2993_;
v___y_2934_ = v___y_2998_;
v_stxForExecution_2935_ = v___x_3020_;
v___y_2936_ = v___y_3005_;
v___y_2937_ = v___y_2988_;
v___y_2938_ = v___y_2994_;
v___y_2939_ = v___y_3007_;
v___y_2940_ = v___y_2990_;
v___y_2941_ = v___y_2997_;
v___y_2942_ = v___y_2989_;
v___y_2943_ = v___y_2995_;
goto v___jp_2927_;
}
v___jp_3021_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_inc_ref(v___y_3031_);
v___x_3043_ = l_Array_append___redArg(v___y_3031_, v___y_3042_);
lean_dec_ref(v___y_3042_);
lean_inc(v___y_3027_);
lean_inc(v___y_3034_);
v___x_3044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3044_, 0, v___y_3034_);
lean_ctor_set(v___x_3044_, 1, v___y_3027_);
lean_ctor_set(v___x_3044_, 2, v___x_3043_);
if (lean_obj_tag(v___y_3033_) == 1)
{
lean_object* v_val_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v_val_3045_ = lean_ctor_get(v___y_3033_, 0);
v___x_3046_ = l_Lean_SourceInfo_fromRef(v_val_3045_, v___x_2499_);
v___x_3047_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = l_Array_mkArray1___redArg(v___x_3048_);
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3025_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3032_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3036_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3039_;
v___y_3004_ = v___x_3044_;
v___y_3005_ = v___y_3038_;
v___y_3006_ = v___y_3040_;
v___y_3007_ = v___y_3041_;
v___y_3008_ = v___x_3049_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3050_; 
v___x_3050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2987_ = v___y_3022_;
v___y_2988_ = v___y_3023_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3025_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3027_;
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3032_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3036_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3039_;
v___y_3004_ = v___x_3044_;
v___y_3005_ = v___y_3038_;
v___y_3006_ = v___y_3040_;
v___y_3007_ = v___y_3041_;
v___y_3008_ = v___x_3050_;
goto v___jp_2986_;
}
}
v___jp_3051_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_inc_ref_n(v___y_3058_, 2);
v___x_3074_ = l_Array_append___redArg(v___y_3058_, v___y_3073_);
lean_dec_ref(v___y_3073_);
lean_inc_n(v___y_3071_, 3);
lean_inc_n(v___y_3065_, 5);
v___x_3075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3075_, 0, v___y_3065_);
lean_ctor_set(v___x_3075_, 1, v___y_3071_);
lean_ctor_set(v___x_3075_, 2, v___x_3074_);
v___x_3076_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___y_3065_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3079_ = l_Lean_Syntax_SepArray_ofElems(v___x_3078_, v___y_3053_);
v___x_3080_ = l_Array_append___redArg(v___y_3058_, v___x_3079_);
lean_dec_ref(v___x_3079_);
v___x_3081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3065_);
lean_ctor_set(v___x_3081_, 1, v___y_3071_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
v___x_3082_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3065_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_Syntax_node3(v___y_3065_, v___y_3071_, v___x_3077_, v___x_3081_, v___x_3083_);
lean_inc(v___y_3057_);
v___x_3085_ = l_Lean_Syntax_node5(v___y_3065_, v___y_3066_, v___y_3060_, v___y_3057_, v___y_3052_, v___x_3075_, v___x_3084_);
v___y_2928_ = v___y_3053_;
v___y_2929_ = v___y_3067_;
v___y_2930_ = v___y_3057_;
v___y_2931_ = v___y_3068_;
v___y_2932_ = v___y_3069_;
v___y_2933_ = v___y_3059_;
v___y_2934_ = v___y_3064_;
v_stxForExecution_2935_ = v___x_3085_;
v___y_2936_ = v___y_3070_;
v___y_2937_ = v___y_3054_;
v___y_2938_ = v___y_3061_;
v___y_2939_ = v___y_3072_;
v___y_2940_ = v___y_3056_;
v___y_2941_ = v___y_3063_;
v___y_2942_ = v___y_3055_;
v___y_2943_ = v___y_3062_;
goto v___jp_2927_;
}
v___jp_3086_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_inc_ref(v___y_3092_);
v___x_3108_ = l_Array_append___redArg(v___y_3092_, v___y_3107_);
lean_dec_ref(v___y_3107_);
lean_inc(v___y_3106_);
lean_inc(v___y_3099_);
v___x_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3099_);
lean_ctor_set(v___x_3109_, 1, v___y_3106_);
lean_ctor_set(v___x_3109_, 2, v___x_3108_);
if (lean_obj_tag(v___y_3098_) == 1)
{
lean_object* v_val_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_val_3110_ = lean_ctor_get(v___y_3098_, 0);
v___x_3111_ = l_Lean_SourceInfo_fromRef(v_val_3110_, v___x_2499_);
v___x_3112_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Array_mkArray1___redArg(v___x_3113_);
v___y_3052_ = v___x_3109_;
v___y_3053_ = v___y_3087_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3092_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3098_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___y_3104_;
v___y_3070_ = v___y_3103_;
v___y_3071_ = v___y_3106_;
v___y_3072_ = v___y_3105_;
v___y_3073_ = v___x_3114_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3052_ = v___x_3109_;
v___y_3053_ = v___y_3087_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v___y_3090_;
v___y_3057_ = v___y_3091_;
v___y_3058_ = v___y_3092_;
v___y_3059_ = v___y_3093_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3098_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___y_3104_;
v___y_3070_ = v___y_3103_;
v___y_3071_ = v___y_3106_;
v___y_3072_ = v___y_3105_;
v___y_3073_ = v___x_3115_;
goto v___jp_3051_;
}
}
v___jp_3116_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_inc_ref_n(v___y_3119_, 2);
v___x_3139_ = l_Array_append___redArg(v___y_3119_, v___y_3138_);
lean_dec_ref(v___y_3138_);
lean_inc_n(v___y_3137_, 2);
lean_inc_n(v___y_3135_, 2);
v___x_3140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3140_, 0, v___y_3135_);
lean_ctor_set(v___x_3140_, 1, v___y_3137_);
lean_ctor_set(v___x_3140_, 2, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3141_, 0, v___y_3135_);
lean_ctor_set(v___x_3141_, 1, v___y_3137_);
lean_ctor_set(v___x_3141_, 2, v___y_3119_);
lean_inc(v___y_3123_);
v___x_3142_ = l_Lean_Syntax_node5(v___y_3135_, v___y_3129_, v___y_3117_, v___y_3123_, v___y_3131_, v___x_3140_, v___x_3141_);
v___y_2928_ = v___y_3118_;
v___y_2929_ = v___y_3130_;
v___y_2930_ = v___y_3123_;
v___y_2931_ = v___y_3132_;
v___y_2932_ = v___y_3133_;
v___y_2933_ = v___y_3124_;
v___y_2934_ = v___y_3128_;
v_stxForExecution_2935_ = v___x_3142_;
v___y_2936_ = v___y_3134_;
v___y_2937_ = v___y_3120_;
v___y_2938_ = v___y_3125_;
v___y_2939_ = v___y_3136_;
v___y_2940_ = v___y_3122_;
v___y_2941_ = v___y_3127_;
v___y_2942_ = v___y_3121_;
v___y_2943_ = v___y_3126_;
goto v___jp_2927_;
}
v___jp_3143_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_inc_ref(v___y_3146_);
v___x_3165_ = l_Array_append___redArg(v___y_3146_, v___y_3164_);
lean_dec_ref(v___y_3164_);
lean_inc(v___y_3163_);
lean_inc(v___y_3161_);
v___x_3166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3161_);
lean_ctor_set(v___x_3166_, 1, v___y_3163_);
lean_ctor_set(v___x_3166_, 2, v___x_3165_);
if (lean_obj_tag(v___y_3155_) == 1)
{
lean_object* v_val_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_val_3167_ = lean_ctor_get(v___y_3155_, 0);
v___x_3168_ = l_Lean_SourceInfo_fromRef(v_val_3167_, v___x_2499_);
v___x_3169_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Array_mkArray1___redArg(v___x_3170_);
v___y_3117_ = v___y_3144_;
v___y_3118_ = v___y_3145_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3148_;
v___y_3122_ = v___y_3149_;
v___y_3123_ = v___y_3150_;
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v___x_3166_;
v___y_3132_ = v___y_3158_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3159_;
v___y_3135_ = v___y_3161_;
v___y_3136_ = v___y_3162_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___x_3171_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3172_; 
v___x_3172_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3117_ = v___y_3144_;
v___y_3118_ = v___y_3145_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3148_;
v___y_3122_ = v___y_3149_;
v___y_3123_ = v___y_3150_;
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v___x_3166_;
v___y_3132_ = v___y_3158_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3159_;
v___y_3135_ = v___y_3161_;
v___y_3136_ = v___y_3162_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___x_3172_;
goto v___jp_3116_;
}
}
v___jp_3173_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_inc_ref_n(v___y_3181_, 2);
v___x_3196_ = l_Array_append___redArg(v___y_3181_, v___y_3195_);
lean_dec_ref(v___y_3195_);
lean_inc_n(v___y_3187_, 2);
lean_inc_n(v___y_3193_, 2);
v___x_3197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3197_, 0, v___y_3193_);
lean_ctor_set(v___x_3197_, 1, v___y_3187_);
lean_ctor_set(v___x_3197_, 2, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3198_, 0, v___y_3193_);
lean_ctor_set(v___x_3198_, 1, v___y_3187_);
lean_ctor_set(v___x_3198_, 2, v___y_3181_);
lean_inc(v___y_3178_);
v___x_3199_ = l_Lean_Syntax_node5(v___y_3193_, v___y_3184_, v___y_3179_, v___y_3178_, v___y_3189_, v___x_3197_, v___x_3198_);
v___y_2928_ = v___y_3174_;
v___y_2929_ = v___y_3188_;
v___y_2930_ = v___y_3178_;
v___y_2931_ = v___y_3190_;
v___y_2932_ = v___y_3191_;
v___y_2933_ = v___y_3180_;
v___y_2934_ = v___y_3186_;
v_stxForExecution_2935_ = v___x_3199_;
v___y_2936_ = v___y_3192_;
v___y_2937_ = v___y_3175_;
v___y_2938_ = v___y_3182_;
v___y_2939_ = v___y_3194_;
v___y_2940_ = v___y_3177_;
v___y_2941_ = v___y_3185_;
v___y_2942_ = v___y_3176_;
v___y_2943_ = v___y_3183_;
goto v___jp_2927_;
}
v___jp_3200_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_inc_ref(v___y_3207_);
v___x_3222_ = l_Array_append___redArg(v___y_3207_, v___y_3221_);
lean_dec_ref(v___y_3221_);
lean_inc(v___y_3214_);
lean_inc(v___y_3219_);
v___x_3223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3223_, 0, v___y_3219_);
lean_ctor_set(v___x_3223_, 1, v___y_3214_);
lean_ctor_set(v___x_3223_, 2, v___x_3222_);
if (lean_obj_tag(v___y_3213_) == 1)
{
lean_object* v_val_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_val_3224_ = lean_ctor_get(v___y_3213_, 0);
v___x_3225_ = l_Lean_SourceInfo_fromRef(v_val_3224_, v___x_2499_);
v___x_3226_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3225_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = l_Array_mkArray1___redArg(v___x_3227_);
v___y_3174_ = v___y_3201_;
v___y_3175_ = v___y_3202_;
v___y_3176_ = v___y_3203_;
v___y_3177_ = v___y_3204_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3212_;
v___y_3185_ = v___y_3211_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___x_3223_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3218_;
v___y_3192_ = v___y_3217_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3220_;
v___y_3195_ = v___x_3228_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3229_; 
v___x_3229_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3174_ = v___y_3201_;
v___y_3175_ = v___y_3202_;
v___y_3176_ = v___y_3203_;
v___y_3177_ = v___y_3204_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3212_;
v___y_3185_ = v___y_3211_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___x_3223_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3218_;
v___y_3192_ = v___y_3217_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3220_;
v___y_3195_ = v___x_3229_;
goto v___jp_3173_;
}
}
v___jp_3230_:
{
lean_object* v_ref_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_ref_3247_ = lean_ctor_get(v___y_3233_, 2);
v___x_3248_ = l_Lean_SourceInfo_fromRef(v_ref_3247_, v___y_3246_);
v___x_3249_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3250_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3249_);
v___x_3251_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_3252_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3255_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3241_) == 1)
{
lean_object* v_val_3256_; lean_object* v___x_3257_; 
v_val_3256_ = lean_ctor_get(v___y_3241_, 0);
lean_inc(v_val_3256_);
v___x_3257_ = l_Array_mkArray1___redArg(v_val_3256_);
v___y_3022_ = v___y_3231_;
v___y_3023_ = v___y_3232_;
v___y_3024_ = v___y_3233_;
v___y_3025_ = v___y_3234_;
v___y_3026_ = v___y_3235_;
v___y_3027_ = v___x_3254_;
v___y_3028_ = v___y_3236_;
v___y_3029_ = v___y_3237_;
v___y_3030_ = v___y_3238_;
v___y_3031_ = v___x_3255_;
v___y_3032_ = v___y_3239_;
v___y_3033_ = v___y_3240_;
v___y_3034_ = v___x_3248_;
v___y_3035_ = v___y_3241_;
v___y_3036_ = v___y_3242_;
v___y_3037_ = v___x_3253_;
v___y_3038_ = v___y_3244_;
v___y_3039_ = v___y_3243_;
v___y_3040_ = v___x_3250_;
v___y_3041_ = v___y_3245_;
v___y_3042_ = v___x_3257_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3022_ = v___y_3231_;
v___y_3023_ = v___y_3232_;
v___y_3024_ = v___y_3233_;
v___y_3025_ = v___y_3234_;
v___y_3026_ = v___y_3235_;
v___y_3027_ = v___x_3254_;
v___y_3028_ = v___y_3236_;
v___y_3029_ = v___y_3237_;
v___y_3030_ = v___y_3238_;
v___y_3031_ = v___x_3255_;
v___y_3032_ = v___y_3239_;
v___y_3033_ = v___y_3240_;
v___y_3034_ = v___x_3248_;
v___y_3035_ = v___y_3241_;
v___y_3036_ = v___y_3242_;
v___y_3037_ = v___x_3253_;
v___y_3038_ = v___y_3244_;
v___y_3039_ = v___y_3243_;
v___y_3040_ = v___x_3250_;
v___y_3041_ = v___y_3245_;
v___y_3042_ = v___x_3258_;
goto v___jp_3021_;
}
}
v___jp_3259_:
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = lean_array_get_size(v_argsArray_3266_);
v___x_3276_ = lean_nat_dec_eq(v___x_3275_, v___x_2514_);
if (v___x_3276_ == 0)
{
if (lean_obj_tag(v___y_3261_) == 0)
{
v___y_3231_ = v_argsArray_3266_;
v___y_3232_ = v___y_3268_;
v___y_3233_ = v___y_3273_;
v___y_3234_ = v___y_3271_;
v___y_3235_ = v___y_3262_;
v___y_3236_ = v___y_3264_;
v___y_3237_ = v___y_3269_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3272_;
v___y_3240_ = v___y_3265_;
v___y_3241_ = v___y_3260_;
v___y_3242_ = v___y_3261_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3267_;
v___y_3245_ = v___y_3270_;
v___y_3246_ = v___x_3276_;
goto v___jp_3230_;
}
else
{
if (v___y_3264_ == 0)
{
v___y_3231_ = v_argsArray_3266_;
v___y_3232_ = v___y_3268_;
v___y_3233_ = v___y_3273_;
v___y_3234_ = v___y_3271_;
v___y_3235_ = v___y_3262_;
v___y_3236_ = v___y_3264_;
v___y_3237_ = v___y_3269_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3272_;
v___y_3240_ = v___y_3265_;
v___y_3241_ = v___y_3260_;
v___y_3242_ = v___y_3261_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3267_;
v___y_3245_ = v___y_3270_;
v___y_3246_ = v___y_3264_;
goto v___jp_3230_;
}
else
{
lean_object* v_ref_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_ref_3277_ = lean_ctor_get(v___y_3273_, 2);
v___x_3278_ = l_Lean_SourceInfo_fromRef(v_ref_3277_, v___x_3276_);
v___x_3279_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3280_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3279_);
v___x_3281_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3285_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3260_) == 1)
{
lean_object* v_val_3286_; lean_object* v___x_3287_; 
v_val_3286_ = lean_ctor_get(v___y_3260_, 0);
lean_inc(v_val_3286_);
v___x_3287_ = l_Array_mkArray1___redArg(v_val_3286_);
v___y_3087_ = v_argsArray_3266_;
v___y_3088_ = v___y_3268_;
v___y_3089_ = v___y_3273_;
v___y_3090_ = v___y_3271_;
v___y_3091_ = v___y_3262_;
v___y_3092_ = v___x_3285_;
v___y_3093_ = v___y_3264_;
v___y_3094_ = v___x_3283_;
v___y_3095_ = v___y_3269_;
v___y_3096_ = v___y_3274_;
v___y_3097_ = v___y_3272_;
v___y_3098_ = v___y_3265_;
v___y_3099_ = v___x_3278_;
v___y_3100_ = v___x_3280_;
v___y_3101_ = v___y_3260_;
v___y_3102_ = v___y_3261_;
v___y_3103_ = v___y_3267_;
v___y_3104_ = v___y_3263_;
v___y_3105_ = v___y_3270_;
v___y_3106_ = v___x_3284_;
v___y_3107_ = v___x_3287_;
goto v___jp_3086_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3087_ = v_argsArray_3266_;
v___y_3088_ = v___y_3268_;
v___y_3089_ = v___y_3273_;
v___y_3090_ = v___y_3271_;
v___y_3091_ = v___y_3262_;
v___y_3092_ = v___x_3285_;
v___y_3093_ = v___y_3264_;
v___y_3094_ = v___x_3283_;
v___y_3095_ = v___y_3269_;
v___y_3096_ = v___y_3274_;
v___y_3097_ = v___y_3272_;
v___y_3098_ = v___y_3265_;
v___y_3099_ = v___x_3278_;
v___y_3100_ = v___x_3280_;
v___y_3101_ = v___y_3260_;
v___y_3102_ = v___y_3261_;
v___y_3103_ = v___y_3267_;
v___y_3104_ = v___y_3263_;
v___y_3105_ = v___y_3270_;
v___y_3106_ = v___x_3284_;
v___y_3107_ = v___x_3288_;
goto v___jp_3086_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3261_) == 0)
{
lean_object* v_ref_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_ref_3289_ = lean_ctor_get(v___y_3273_, 2);
v___x_3290_ = 0;
v___x_3291_ = l_Lean_SourceInfo_fromRef(v_ref_3289_, v___x_3290_);
v___x_3292_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3293_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3292_);
v___x_3294_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_3295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3298_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3260_) == 1)
{
lean_object* v_val_3299_; lean_object* v___x_3300_; 
v_val_3299_ = lean_ctor_get(v___y_3260_, 0);
lean_inc(v_val_3299_);
v___x_3300_ = l_Array_mkArray1___redArg(v_val_3299_);
v___y_3144_ = v___x_3296_;
v___y_3145_ = v_argsArray_3266_;
v___y_3146_ = v___x_3298_;
v___y_3147_ = v___y_3268_;
v___y_3148_ = v___y_3273_;
v___y_3149_ = v___y_3271_;
v___y_3150_ = v___y_3262_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3269_;
v___y_3153_ = v___y_3274_;
v___y_3154_ = v___y_3272_;
v___y_3155_ = v___y_3265_;
v___y_3156_ = v___x_3293_;
v___y_3157_ = v___y_3260_;
v___y_3158_ = v___y_3261_;
v___y_3159_ = v___y_3267_;
v___y_3160_ = v___y_3263_;
v___y_3161_ = v___x_3291_;
v___y_3162_ = v___y_3270_;
v___y_3163_ = v___x_3297_;
v___y_3164_ = v___x_3300_;
goto v___jp_3143_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3144_ = v___x_3296_;
v___y_3145_ = v_argsArray_3266_;
v___y_3146_ = v___x_3298_;
v___y_3147_ = v___y_3268_;
v___y_3148_ = v___y_3273_;
v___y_3149_ = v___y_3271_;
v___y_3150_ = v___y_3262_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3269_;
v___y_3153_ = v___y_3274_;
v___y_3154_ = v___y_3272_;
v___y_3155_ = v___y_3265_;
v___y_3156_ = v___x_3293_;
v___y_3157_ = v___y_3260_;
v___y_3158_ = v___y_3261_;
v___y_3159_ = v___y_3267_;
v___y_3160_ = v___y_3263_;
v___y_3161_ = v___x_3291_;
v___y_3162_ = v___y_3270_;
v___y_3163_ = v___x_3297_;
v___y_3164_ = v___x_3301_;
goto v___jp_3143_;
}
}
else
{
lean_object* v_ref_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_ref_3302_ = lean_ctor_get(v___y_3273_, 2);
v___x_3303_ = 0;
v___x_3304_ = l_Lean_SourceInfo_fromRef(v_ref_3302_, v___x_3303_);
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3306_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3305_);
v___x_3307_ = l_Lean_SourceInfo_fromRef(v_tk_2515_, v___x_2499_);
v___x_3308_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3311_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3260_) == 1)
{
lean_object* v_val_3312_; lean_object* v___x_3313_; 
v_val_3312_ = lean_ctor_get(v___y_3260_, 0);
lean_inc(v_val_3312_);
v___x_3313_ = l_Array_mkArray1___redArg(v_val_3312_);
v___y_3201_ = v_argsArray_3266_;
v___y_3202_ = v___y_3268_;
v___y_3203_ = v___y_3273_;
v___y_3204_ = v___y_3271_;
v___y_3205_ = v___y_3262_;
v___y_3206_ = v___x_3309_;
v___y_3207_ = v___x_3311_;
v___y_3208_ = v___y_3264_;
v___y_3209_ = v___y_3269_;
v___y_3210_ = v___y_3274_;
v___y_3211_ = v___y_3272_;
v___y_3212_ = v___x_3306_;
v___y_3213_ = v___y_3265_;
v___y_3214_ = v___x_3310_;
v___y_3215_ = v___y_3260_;
v___y_3216_ = v___y_3261_;
v___y_3217_ = v___y_3267_;
v___y_3218_ = v___y_3263_;
v___y_3219_ = v___x_3304_;
v___y_3220_ = v___y_3270_;
v___y_3221_ = v___x_3313_;
goto v___jp_3200_;
}
else
{
lean_object* v___x_3314_; 
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3201_ = v_argsArray_3266_;
v___y_3202_ = v___y_3268_;
v___y_3203_ = v___y_3273_;
v___y_3204_ = v___y_3271_;
v___y_3205_ = v___y_3262_;
v___y_3206_ = v___x_3309_;
v___y_3207_ = v___x_3311_;
v___y_3208_ = v___y_3264_;
v___y_3209_ = v___y_3269_;
v___y_3210_ = v___y_3274_;
v___y_3211_ = v___y_3272_;
v___y_3212_ = v___x_3306_;
v___y_3213_ = v___y_3265_;
v___y_3214_ = v___x_3310_;
v___y_3215_ = v___y_3260_;
v___y_3216_ = v___y_3261_;
v___y_3217_ = v___y_3267_;
v___y_3218_ = v___y_3263_;
v___y_3219_ = v___x_3304_;
v___y_3220_ = v___y_3270_;
v___y_3221_ = v___x_3314_;
goto v___jp_3200_;
}
}
}
}
v___jp_3315_:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3330_, v___y_3320_, v___y_3323_, v___y_3317_, v___y_3325_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___x_3334_ = l_Lean_LibrarySuggestions_select(v_a_3333_, v___y_3331_, v___y_3320_, v___y_3323_, v___y_3317_, v___y_3325_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; size_t v_sz_3336_; size_t v___x_3337_; lean_object* v___x_3338_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v_sz_3336_ = lean_array_size(v_a_3335_);
v___x_3337_ = ((size_t)0ULL);
v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3335_, v_sz_3336_, v___x_3337_, v___y_3319_, v___y_3328_, v___y_3330_, v___y_3322_, v___y_3329_, v___y_3320_, v___y_3323_, v___y_3317_, v___y_3325_);
lean_dec(v_a_3335_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___y_3260_ = v___y_3324_;
v___y_3261_ = v___y_3326_;
v___y_3262_ = v___y_3316_;
v___y_3263_ = v___y_3327_;
v___y_3264_ = v___y_3318_;
v___y_3265_ = v___y_3321_;
v_argsArray_3266_ = v_a_3339_;
v___y_3267_ = v___y_3328_;
v___y_3268_ = v___y_3330_;
v___y_3269_ = v___y_3322_;
v___y_3270_ = v___y_3329_;
v___y_3271_ = v___y_3320_;
v___y_3272_ = v___y_3323_;
v___y_3273_ = v___y_3317_;
v___y_3274_ = v___y_3325_;
goto v___jp_3259_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v___y_3326_);
lean_dec(v___y_3324_);
lean_dec(v___y_3321_);
lean_dec(v___y_3316_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v_a_3340_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3338_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3338_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec(v___y_3326_);
lean_dec(v___y_3324_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3316_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v_a_3348_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3334_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3334_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3326_);
lean_dec(v___y_3324_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3316_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v_a_3356_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3332_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3332_);
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
lean_object* v_config_3381_; uint8_t v_suggestions_3382_; 
v_config_3381_ = lean_ctor_get(v___y_3365_, 0);
lean_inc_ref(v_config_3381_);
lean_dec_ref(v___y_3365_);
v_suggestions_3382_ = lean_ctor_get_uint8(v_config_3381_, sizeof(void*)*3 + 26);
if (v_suggestions_3382_ == 0)
{
lean_dec_ref(v_config_3381_);
lean_dec_ref(v___f_2503_);
v___y_3260_ = v___y_3373_;
v___y_3261_ = v___y_3375_;
v___y_3262_ = v___y_3366_;
v___y_3263_ = v___y_3376_;
v___y_3264_ = v___y_3368_;
v___y_3265_ = v___y_3370_;
v_argsArray_3266_ = v___y_3380_;
v___y_3267_ = v___y_3377_;
v___y_3268_ = v___y_3379_;
v___y_3269_ = v___y_3371_;
v___y_3270_ = v___y_3378_;
v___y_3271_ = v___y_3369_;
v___y_3272_ = v___y_3372_;
v___y_3273_ = v___y_3367_;
v___y_3274_ = v___y_3374_;
goto v___jp_3259_;
}
else
{
lean_object* v_maxSuggestions_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_maxSuggestions_3383_ = lean_ctor_get(v_config_3381_, 2);
lean_inc(v_maxSuggestions_3383_);
lean_dec_ref(v_config_3381_);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3385_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3383_) == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_unsigned_to_nat(100u);
v___x_3387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___x_3384_);
lean_ctor_set(v___x_3387_, 2, v___f_2503_);
lean_ctor_set(v___x_3387_, 3, v___x_3385_);
v___y_3316_ = v___y_3366_;
v___y_3317_ = v___y_3367_;
v___y_3318_ = v___y_3368_;
v___y_3319_ = v___y_3380_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___y_3371_;
v___y_3323_ = v___y_3372_;
v___y_3324_ = v___y_3373_;
v___y_3325_ = v___y_3374_;
v___y_3326_ = v___y_3375_;
v___y_3327_ = v___y_3376_;
v___y_3328_ = v___y_3377_;
v___y_3329_ = v___y_3378_;
v___y_3330_ = v___y_3379_;
v___y_3331_ = v___x_3387_;
goto v___jp_3315_;
}
else
{
lean_object* v_val_3388_; lean_object* v___x_3389_; 
v_val_3388_ = lean_ctor_get(v_maxSuggestions_3383_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v_maxSuggestions_3383_, 1);
v___x_3389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3389_, 0, v_val_3388_);
lean_ctor_set(v___x_3389_, 1, v___x_3384_);
lean_ctor_set(v___x_3389_, 2, v___f_2503_);
lean_ctor_set(v___x_3389_, 3, v___x_3385_);
v___y_3316_ = v___y_3366_;
v___y_3317_ = v___y_3367_;
v___y_3318_ = v___y_3368_;
v___y_3319_ = v___y_3380_;
v___y_3320_ = v___y_3369_;
v___y_3321_ = v___y_3370_;
v___y_3322_ = v___y_3371_;
v___y_3323_ = v___y_3372_;
v___y_3324_ = v___y_3373_;
v___y_3325_ = v___y_3374_;
v___y_3326_ = v___y_3375_;
v___y_3327_ = v___y_3376_;
v___y_3328_ = v___y_3377_;
v___y_3329_ = v___y_3378_;
v___y_3330_ = v___y_3379_;
v___y_3331_ = v___x_3389_;
goto v___jp_3315_;
}
}
}
v___jp_3390_:
{
uint8_t v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = 1;
lean_inc(v___y_3391_);
v___x_3406_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3391_, v___x_3405_, v___y_3400_, v___y_3392_, v___y_3398_);
if (lean_obj_tag(v___x_3406_) == 0)
{
if (lean_obj_tag(v___y_3403_) == 1)
{
lean_object* v_a_3407_; lean_object* v_val_3408_; lean_object* v___x_3409_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v_val_3408_ = lean_ctor_get(v___y_3403_, 0);
lean_inc(v_val_3408_);
lean_dec_ref_known(v___y_3403_, 1);
v___x_3409_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3408_);
lean_dec(v_val_3408_);
v___y_3365_ = v_a_3407_;
v___y_3366_ = v___y_3391_;
v___y_3367_ = v___y_3392_;
v___y_3368_ = v___y_3393_;
v___y_3369_ = v___y_3394_;
v___y_3370_ = v___y_3395_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3397_;
v___y_3373_ = v___y_3404_;
v___y_3374_ = v___y_3398_;
v___y_3375_ = v___y_3399_;
v___y_3376_ = v___x_3405_;
v___y_3377_ = v___y_3400_;
v___y_3378_ = v___y_3401_;
v___y_3379_ = v___y_3402_;
v___y_3380_ = v___x_3409_;
goto v___jp_3364_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
lean_dec(v___y_3403_);
v_a_3410_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3411_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3365_ = v_a_3410_;
v___y_3366_ = v___y_3391_;
v___y_3367_ = v___y_3392_;
v___y_3368_ = v___y_3393_;
v___y_3369_ = v___y_3394_;
v___y_3370_ = v___y_3395_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3397_;
v___y_3373_ = v___y_3404_;
v___y_3374_ = v___y_3398_;
v___y_3375_ = v___y_3399_;
v___y_3376_ = v___x_3405_;
v___y_3377_ = v___y_3400_;
v___y_3378_ = v___y_3401_;
v___y_3379_ = v___y_3402_;
v___y_3380_ = v___x_3411_;
goto v___jp_3364_;
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___y_3399_);
lean_dec(v___y_3395_);
lean_dec(v___y_3391_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v_a_3412_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3406_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3406_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
v___jp_3420_:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Syntax_getOptional_x3f(v___y_3423_);
lean_dec(v___y_3423_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3436_; 
v___x_3436_ = lean_box(0);
v___y_3391_ = v___y_3422_;
v___y_3392_ = v___y_3433_;
v___y_3393_ = v___y_3424_;
v___y_3394_ = v___y_3431_;
v___y_3395_ = v___y_3425_;
v___y_3396_ = v___y_3429_;
v___y_3397_ = v___y_3432_;
v___y_3398_ = v___y_3434_;
v___y_3399_ = v___y_3421_;
v___y_3400_ = v___y_3427_;
v___y_3401_ = v___y_3430_;
v___y_3402_ = v___y_3428_;
v___y_3403_ = v_args_3426_;
v___y_3404_ = v___x_3436_;
goto v___jp_3390_;
}
else
{
lean_object* v_val_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v_val_3437_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3435_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_val_3437_);
lean_dec(v___x_3435_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_val_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v___y_3391_ = v___y_3422_;
v___y_3392_ = v___y_3433_;
v___y_3393_ = v___y_3424_;
v___y_3394_ = v___y_3431_;
v___y_3395_ = v___y_3425_;
v___y_3396_ = v___y_3429_;
v___y_3397_ = v___y_3432_;
v___y_3398_ = v___y_3434_;
v___y_3399_ = v___y_3421_;
v___y_3400_ = v___y_3427_;
v___y_3401_ = v___y_3430_;
v___y_3402_ = v___y_3428_;
v___y_3403_ = v_args_3426_;
v___y_3404_ = v___x_3442_;
goto v___jp_3390_;
}
}
}
}
v___jp_3446_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3461_ = lean_unsigned_to_nat(3u);
v___x_3462_ = l_Lean_Syntax_getArg(v___y_3451_, v___x_3461_);
lean_dec(v___y_3451_);
v___x_3463_ = l_Lean_Syntax_isNone(v___x_3462_);
if (v___x_3463_ == 0)
{
uint8_t v___x_3464_; 
lean_inc(v___x_3462_);
v___x_3464_ = l_Lean_Syntax_matchesNull(v___x_3462_, v___x_3445_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; 
lean_dec(v___x_3462_);
lean_dec(v_o_3452_);
lean_dec(v___y_3450_);
lean_dec(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_3465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3465_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3466_ = l_Lean_Syntax_getArg(v___x_3462_, v___x_2514_);
lean_dec(v___x_3462_);
v___x_3467_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3468_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3467_);
lean_inc(v___x_3466_);
v___x_3469_ = l_Lean_Syntax_isOfKind(v___x_3466_, v___x_3468_);
lean_dec(v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
lean_dec(v___x_3466_);
lean_dec(v_o_3452_);
lean_dec(v___y_3450_);
lean_dec(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_3470_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v_args_3472_; lean_object* v___x_3473_; 
v___x_3471_ = l_Lean_Syntax_getArg(v___x_3466_, v___x_3445_);
lean_dec(v___x_3466_);
v_args_3472_ = l_Lean_Syntax_getArgs(v___x_3471_);
lean_dec(v___x_3471_);
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_args_3472_);
v___y_3421_ = v___y_3448_;
v___y_3422_ = v___y_3447_;
v___y_3423_ = v___y_3450_;
v___y_3424_ = v___y_3449_;
v___y_3425_ = v_o_3452_;
v_args_3426_ = v___x_3473_;
v___y_3427_ = v___y_3453_;
v___y_3428_ = v___y_3454_;
v___y_3429_ = v___y_3455_;
v___y_3430_ = v___y_3456_;
v___y_3431_ = v___y_3457_;
v___y_3432_ = v___y_3458_;
v___y_3433_ = v___y_3459_;
v___y_3434_ = v___y_3460_;
goto v___jp_3420_;
}
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v___x_3462_);
v___x_3474_ = lean_box(0);
v___y_3421_ = v___y_3448_;
v___y_3422_ = v___y_3447_;
v___y_3423_ = v___y_3450_;
v___y_3424_ = v___y_3449_;
v___y_3425_ = v_o_3452_;
v_args_3426_ = v___x_3474_;
v___y_3427_ = v___y_3453_;
v___y_3428_ = v___y_3454_;
v___y_3429_ = v___y_3455_;
v___y_3430_ = v___y_3456_;
v___y_3431_ = v___y_3457_;
v___y_3432_ = v___y_3458_;
v___y_3433_ = v___y_3459_;
v___y_3434_ = v___y_3460_;
goto v___jp_3420_;
}
}
v___jp_3475_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3485_ = lean_unsigned_to_nat(2u);
v___x_3486_ = l_Lean_Syntax_getArg(v_stx_2498_, v___x_3485_);
v___x_3487_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3488_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3487_);
lean_inc(v___x_3486_);
v___x_3489_ = l_Lean_Syntax_isOfKind(v___x_3486_, v___x_3488_);
lean_dec(v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
lean_dec(v___x_3486_);
lean_dec(v_bang_3476_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_3490_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3490_;
}
else
{
lean_object* v_cfg_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_cfg_3491_ = l_Lean_Syntax_getArg(v___x_3486_, v___x_2514_);
v___x_3492_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2502_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v___x_2500_);
v___x_3493_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_3492_);
lean_inc(v_cfg_3491_);
v___x_3494_ = l_Lean_Syntax_isOfKind(v_cfg_3491_, v___x_3493_);
lean_dec(v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
lean_dec(v_cfg_3491_);
lean_dec(v___x_3486_);
lean_dec(v_bang_3476_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_3495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3495_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = l_Lean_Syntax_getArg(v___x_3486_, v___x_3445_);
v___x_3497_ = l_Lean_Syntax_getArg(v___x_3486_, v___x_3485_);
v___x_3498_ = l_Lean_Syntax_isNone(v___x_3497_);
if (v___x_3498_ == 0)
{
uint8_t v___x_3499_; 
lean_inc(v___x_3497_);
v___x_3499_ = l_Lean_Syntax_matchesNull(v___x_3497_, v___x_3445_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v___x_3497_);
lean_dec(v___x_3496_);
lean_dec(v_cfg_3491_);
lean_dec(v___x_3486_);
lean_dec(v_bang_3476_);
lean_dec(v_tk_2515_);
lean_dec_ref(v___f_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2500_);
v___x_3500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3500_;
}
else
{
lean_object* v_o_3501_; lean_object* v___x_3502_; 
v_o_3501_ = l_Lean_Syntax_getArg(v___x_3497_, v___x_2514_);
lean_dec(v___x_3497_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_o_3501_);
v___y_3447_ = v_cfg_3491_;
v___y_3448_ = v_bang_3476_;
v___y_3449_ = v___x_3489_;
v___y_3450_ = v___x_3496_;
v___y_3451_ = v___x_3486_;
v_o_3452_ = v___x_3502_;
v___y_3453_ = v___y_3477_;
v___y_3454_ = v___y_3478_;
v___y_3455_ = v___y_3479_;
v___y_3456_ = v___y_3480_;
v___y_3457_ = v___y_3481_;
v___y_3458_ = v___y_3482_;
v___y_3459_ = v___y_3483_;
v___y_3460_ = v___y_3484_;
goto v___jp_3446_;
}
}
else
{
lean_object* v___x_3503_; 
lean_dec(v___x_3497_);
v___x_3503_ = lean_box(0);
v___y_3447_ = v_cfg_3491_;
v___y_3448_ = v_bang_3476_;
v___y_3449_ = v___x_3489_;
v___y_3450_ = v___x_3496_;
v___y_3451_ = v___x_3486_;
v_o_3452_ = v___x_3503_;
v___y_3453_ = v___y_3477_;
v___y_3454_ = v___y_3478_;
v___y_3455_ = v___y_3479_;
v___y_3456_ = v___y_3480_;
v___y_3457_ = v___y_3481_;
v___y_3458_ = v___y_3482_;
v___y_3459_ = v___y_3483_;
v___y_3460_ = v___y_3484_;
goto v___jp_3446_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3511_, lean_object* v_stx_3512_, lean_object* v___x_3513_, lean_object* v___x_3514_, lean_object* v___x_3515_, lean_object* v___x_3516_, lean_object* v___f_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v___x_30974__boxed_3527_; uint8_t v___x_30975__boxed_3528_; lean_object* v_res_3529_; 
v___x_30974__boxed_3527_ = lean_unbox(v___x_3511_);
v___x_30975__boxed_3528_ = lean_unbox(v___x_3513_);
v_res_3529_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_30974__boxed_3527_, v_stx_3512_, v___x_30975__boxed_3528_, v___x_3514_, v___x_3515_, v___x_3516_, v___f_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v_stx_3512_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; uint8_t v___x_3551_; lean_object* v___f_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___y_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3549_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3536_);
v___x_3550_ = l_Lean_Syntax_isOfKind(v_stx_3536_, v___x_3549_);
v___x_3551_ = 1;
v___f_3552_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3553_ = lean_box(v___x_3550_);
v___x_3554_ = lean_box(v___x_3551_);
v___y_3555_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3555_, 0, v___x_3553_);
lean_closure_set(v___y_3555_, 1, v_stx_3536_);
lean_closure_set(v___y_3555_, 2, v___x_3554_);
lean_closure_set(v___y_3555_, 3, v___x_3546_);
lean_closure_set(v___y_3555_, 4, v___x_3547_);
lean_closure_set(v___y_3555_, 5, v___x_3548_);
lean_closure_set(v___y_3555_, 6, v___f_3552_);
v___x_3556_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3556_, 0, v___y_3555_);
v___x_3557_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3556_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3569_, lean_object* v_as_3570_, lean_object* v_as_x27_3571_, lean_object* v_b_3572_, lean_object* v_a_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3569_, v_as_x27_3571_, v_b_3572_, v___y_3580_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3584_, lean_object* v_as_3585_, lean_object* v_as_x27_3586_, lean_object* v_b_3587_, lean_object* v_a_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3584_, v_as_3585_, v_as_x27_3586_, v_b_3587_, v_a_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v_as_x27_3586_);
lean_dec(v_as_3585_);
lean_dec(v___x_3584_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3606_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3607_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3609_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3610_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3606_, v___x_3607_, v___x_3608_, v___x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3640_ = l_Lean_addBuiltinDeclarationRanges(v___x_3638_, v___x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3643_, lean_object* v_simprocs_3644_, lean_object* v_fvarIdsToSimp_3645_, uint8_t v_simplifyTarget_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = lean_unsigned_to_nat(32u);
v___x_3656_ = lean_mk_empty_array_with_capacity(v___x_3655_);
lean_dec_ref(v___x_3656_);
v___x_3657_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3658_ = l_Lean_Meta_dsimpGoal(v_a_3654_, v_ctx_3643_, v_simprocs_3644_, v_simplifyTarget_3646_, v_fvarIdsToSimp_3645_, v___x_3657_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v_fst_3660_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v_fst_3660_ = lean_ctor_get(v_a_3659_, 0);
if (lean_obj_tag(v_fst_3660_) == 0)
{
lean_object* v_snd_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_snd_3661_ = lean_ctor_get(v_a_3659_, 1);
lean_inc(v_snd_3661_);
lean_dec(v_a_3659_);
v___x_3662_ = lean_box(0);
v___x_3663_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3662_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v___x_3663_, 0);
lean_dec(v_unused_3671_);
v___x_3665_ = v___x_3663_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v___x_3663_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v_snd_3661_);
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_snd_3661_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_snd_3661_);
v_a_3672_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3663_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3663_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_snd_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3706_; 
lean_inc_ref(v_fst_3660_);
v_snd_3680_ = lean_ctor_get(v_a_3659_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_a_3659_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; 
v_unused_3707_ = lean_ctor_get(v_a_3659_, 0);
lean_dec(v_unused_3707_);
v___x_3682_ = v_a_3659_;
v_isShared_3683_ = v_isSharedCheck_3706_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_snd_3680_);
lean_dec(v_a_3659_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3706_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v_val_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v_val_3684_ = lean_ctor_get(v_fst_3660_, 0);
lean_inc(v_val_3684_);
lean_dec_ref_known(v_fst_3660_, 1);
v___x_3685_ = lean_box(0);
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 1);
lean_ctor_set(v___x_3682_, 1, v___x_3685_);
lean_ctor_set(v___x_3682_, 0, v_val_3684_);
v___x_3687_ = v___x_3682_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_val_3684_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3687_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; 
v_unused_3696_ = lean_ctor_get(v___x_3688_, 0);
lean_dec(v_unused_3696_);
v___x_3690_ = v___x_3688_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v___x_3688_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v_snd_3680_);
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_snd_3680_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v_snd_3680_);
v_a_3697_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3688_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3688_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
v_a_3708_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3658_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3658_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec_ref(v_fvarIdsToSimp_3645_);
lean_dec_ref(v_simprocs_3644_);
lean_dec_ref(v_ctx_3643_);
v_a_3716_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3653_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3653_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3724_, lean_object* v_simprocs_3725_, lean_object* v_fvarIdsToSimp_3726_, lean_object* v_simplifyTarget_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_){
_start:
{
uint8_t v_simplifyTarget_boxed_3734_; lean_object* v_res_3735_; 
v_simplifyTarget_boxed_3734_ = lean_unbox(v_simplifyTarget_3727_);
v_res_3735_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3724_, v_simprocs_3725_, v_fvarIdsToSimp_3726_, v_simplifyTarget_boxed_3734_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
lean_dec(v_a_3728_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3736_, lean_object* v_simprocs_3737_, lean_object* v_fvarIdsToSimp_3738_, uint8_t v_simplifyTarget_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3736_, v_simprocs_3737_, v_fvarIdsToSimp_3738_, v_simplifyTarget_3739_, v_a_3741_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3750_, lean_object* v_simprocs_3751_, lean_object* v_fvarIdsToSimp_3752_, lean_object* v_simplifyTarget_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
uint8_t v_simplifyTarget_boxed_3763_; lean_object* v_res_3764_; 
v_simplifyTarget_boxed_3763_ = lean_unbox(v_simplifyTarget_3753_);
v_res_3764_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3750_, v_simprocs_3751_, v_fvarIdsToSimp_3752_, v_simplifyTarget_boxed_3763_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3754_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3765_, lean_object* v_simprocs_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3768_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3778_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v___x_3778_ = l_Lean_MVarId_getNondepPropHyps(v_a_3777_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; uint8_t v___x_3780_; lean_object* v___x_3781_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
v___x_3780_ = 1;
v___x_3781_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3765_, v_simprocs_3766_, v_a_3779_, v___x_3780_, v___y_3768_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
return v___x_3781_;
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec_ref(v_simprocs_3766_);
lean_dec_ref(v_ctx_3765_);
v_a_3782_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3778_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3778_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec_ref(v_simprocs_3766_);
lean_dec_ref(v_ctx_3765_);
v_a_3790_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3776_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3776_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3798_, lean_object* v_simprocs_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3798_, v_simprocs_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3810_, lean_object* v_ctx_3811_, lean_object* v_simprocs_3812_, uint8_t v_type_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3810_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3825_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v___x_3825_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3811_, v_simprocs_3812_, v_a_3824_, v_type_3813_, v___y_3815_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_simprocs_3812_);
lean_dec_ref(v_ctx_3811_);
v_a_3826_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3823_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3823_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3834_, lean_object* v_ctx_3835_, lean_object* v_simprocs_3836_, lean_object* v_type_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
uint8_t v_type_633__boxed_3847_; lean_object* v_res_3848_; 
v_type_633__boxed_3847_ = lean_unbox(v_type_3837_);
v_res_3848_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3834_, v_ctx_3835_, v_simprocs_3836_, v_type_633__boxed_3847_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3849_, lean_object* v_simprocs_3850_, lean_object* v_loc_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
if (lean_obj_tag(v_loc_3851_) == 0)
{
lean_object* v___f_3861_; lean_object* v___x_3862_; 
v___f_3861_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3861_, 0, v_ctx_3849_);
lean_closure_set(v___f_3861_, 1, v_simprocs_3850_);
v___x_3862_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3861_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
return v___x_3862_;
}
else
{
lean_object* v_hypotheses_3863_; uint8_t v_type_3864_; lean_object* v___x_3865_; lean_object* v___f_3866_; lean_object* v___x_3867_; 
v_hypotheses_3863_ = lean_ctor_get(v_loc_3851_, 0);
lean_inc_ref(v_hypotheses_3863_);
v_type_3864_ = lean_ctor_get_uint8(v_loc_3851_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3851_, 1);
v___x_3865_ = lean_box(v_type_3864_);
v___f_3866_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3866_, 0, v_hypotheses_3863_);
lean_closure_set(v___f_3866_, 1, v_ctx_3849_);
lean_closure_set(v___f_3866_, 2, v_simprocs_3850_);
lean_closure_set(v___f_3866_, 3, v___x_3865_);
v___x_3867_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3866_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3868_, lean_object* v_simprocs_3869_, lean_object* v_loc_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3868_, v_simprocs_3869_, v_loc_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3885_, lean_object* v_stx_3886_, uint8_t v___x_3887_, lean_object* v___x_3888_, lean_object* v___x_3889_, lean_object* v___x_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
if (v___x_3885_ == 0)
{
lean_object* v___x_3900_; 
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_3900_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3900_;
}
else
{
lean_object* v___x_3901_; lean_object* v_tk_3902_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; uint8_t v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v_stx_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; uint8_t v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; uint8_t v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; uint8_t v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; uint8_t v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; uint8_t v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; uint8_t v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; uint8_t v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; uint8_t v___y_4207_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; uint8_t v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; uint8_t v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v_args_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___x_4283_; uint8_t v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v_o_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v_bang_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_3901_ = lean_unsigned_to_nat(0u);
v_tk_3902_ = l_Lean_Syntax_getArg(v_stx_3886_, v___x_3901_);
v___x_4283_ = lean_unsigned_to_nat(1u);
v___x_4340_ = l_Lean_Syntax_getArg(v_stx_3886_, v___x_4283_);
v___x_4341_ = l_Lean_Syntax_isNone(v___x_4340_);
if (v___x_4341_ == 0)
{
uint8_t v___x_4342_; 
lean_inc(v___x_4340_);
v___x_4342_ = l_Lean_Syntax_matchesNull(v___x_4340_, v___x_4283_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; 
lean_dec(v___x_4340_);
lean_dec(v_tk_3902_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_4343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4343_;
}
else
{
lean_object* v_bang_4344_; lean_object* v___x_4345_; 
v_bang_4344_ = l_Lean_Syntax_getArg(v___x_4340_, v___x_3901_);
lean_dec(v___x_4340_);
v___x_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4345_, 0, v_bang_4344_);
v_bang_4313_ = v___x_4345_;
v___y_4314_ = v___y_3891_;
v___y_4315_ = v___y_3892_;
v___y_4316_ = v___y_3893_;
v___y_4317_ = v___y_3894_;
v___y_4318_ = v___y_3895_;
v___y_4319_ = v___y_3896_;
v___y_4320_ = v___y_3897_;
v___y_4321_ = v___y_3898_;
goto v___jp_4312_;
}
}
else
{
lean_object* v___x_4346_; 
lean_dec(v___x_4340_);
v___x_4346_ = lean_box(0);
v_bang_4313_ = v___x_4346_;
v___y_4314_ = v___y_3891_;
v___y_4315_ = v___y_3892_;
v___y_4316_ = v___y_3893_;
v___y_4317_ = v___y_3894_;
v___y_4318_ = v___y_3895_;
v___y_4319_ = v___y_3896_;
v___y_4320_ = v___y_3897_;
v___y_4321_ = v___y_3898_;
goto v___jp_4312_;
}
v___jp_3903_:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3912_, v___y_3906_, v___y_3915_, v___y_3905_, v___y_3911_, v___y_3910_, v___y_3914_, v___y_3904_, v___y_3909_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v_usedTheorems_3918_; lean_object* v_diag_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3961_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v_usedTheorems_3918_ = lean_ctor_get(v_a_3917_, 0);
v_diag_3919_ = lean_ctor_get(v_a_3917_, 1);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_a_3917_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3921_ = v_a_3917_;
v_isShared_3922_ = v_isSharedCheck_3961_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_diag_3919_);
lean_inc(v_usedTheorems_3918_);
lean_dec(v_a_3917_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3961_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3913_, v_usedTheorems_3918_, v___y_3904_, v___y_3909_, v___y_3907_, v___y_3908_);
lean_dec_ref(v_usedTheorems_3918_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v_ref_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v_ref_3925_ = lean_ctor_get(v___y_3907_, 2);
v___x_3926_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v_a_3924_);
lean_ctor_set(v___x_3921_, 0, v___x_3926_);
v___x_3928_ = v___x_3921_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_a_3924_);
v___x_3928_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
lean_ctor_set(v___x_3930_, 2, v___x_3929_);
lean_ctor_set(v___x_3930_, 3, v___x_3929_);
lean_ctor_set(v___x_3930_, 4, v___x_3929_);
lean_ctor_set(v___x_3930_, 5, v___x_3929_);
lean_inc(v_ref_3925_);
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v_ref_3925_);
v___x_3932_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3933_ = 4;
v___x_3934_ = l_Lean_MessageData_nil;
v___x_3935_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3902_, v___x_3930_, v___x_3931_, v___x_3932_, v___x_3929_, v___x_3933_, v___x_3934_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; 
v_unused_3943_ = lean_ctor_get(v___x_3935_, 0);
lean_dec(v_unused_3943_);
v___x_3937_ = v___x_3935_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v___x_3935_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v_diag_3919_);
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_diag_3919_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec_ref(v_diag_3919_);
v_a_3944_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3935_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3935_);
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
lean_del_object(v___x_3921_);
lean_dec_ref(v_diag_3919_);
lean_dec(v_tk_3902_);
v_a_3953_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3923_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3923_);
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
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v___y_3913_);
lean_dec(v_tk_3902_);
v_a_3962_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3916_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3916_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
v___jp_3970_:
{
if (lean_obj_tag(v___y_3980_) == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3984_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
lean_ctor_set_uint8(v___x_3984_, sizeof(void*)*1, v___x_3887_);
v___y_3904_ = v___y_3973_;
v___y_3905_ = v___y_3972_;
v___y_3906_ = v___y_3971_;
v___y_3907_ = v___y_3974_;
v___y_3908_ = v___y_3976_;
v___y_3909_ = v___y_3975_;
v___y_3910_ = v___y_3977_;
v___y_3911_ = v___y_3978_;
v___y_3912_ = v___y_3982_;
v___y_3913_ = v___y_3979_;
v___y_3914_ = v___y_3981_;
v___y_3915_ = v___x_3984_;
goto v___jp_3903_;
}
else
{
lean_object* v_val_3985_; lean_object* v___x_3986_; 
v_val_3985_ = lean_ctor_get(v___y_3980_, 0);
lean_inc(v_val_3985_);
lean_dec_ref_known(v___y_3980_, 1);
v___x_3986_ = l_Lean_Elab_Tactic_expandLocation(v_val_3985_);
lean_dec(v_val_3985_);
v___y_3904_ = v___y_3973_;
v___y_3905_ = v___y_3972_;
v___y_3906_ = v___y_3971_;
v___y_3907_ = v___y_3974_;
v___y_3908_ = v___y_3976_;
v___y_3909_ = v___y_3975_;
v___y_3910_ = v___y_3977_;
v___y_3911_ = v___y_3978_;
v___y_3912_ = v___y_3982_;
v___y_3913_ = v___y_3979_;
v___y_3914_ = v___y_3981_;
v___y_3915_ = v___x_3986_;
goto v___jp_3903_;
}
}
v___jp_3987_:
{
uint8_t v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4000_ = 0;
v___x_4001_ = 2;
v___x_4002_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4003_ = lean_box(v___x_4000_);
v___x_4004_ = lean_box(v___x_4001_);
v___x_4005_ = lean_box(v___x_4000_);
lean_inc(v_stx_3991_);
v___x_4006_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4006_, 0, v_stx_3991_);
lean_closure_set(v___x_4006_, 1, v___x_4003_);
lean_closure_set(v___x_4006_, 2, v___x_4004_);
lean_closure_set(v___x_4006_, 3, v___x_4005_);
lean_closure_set(v___x_4006_, 4, v___x_4002_);
v___x_4007_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4006_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
if (lean_obj_tag(v___y_3990_) == 0)
{
lean_object* v_ctx_4009_; lean_object* v_simprocs_4010_; 
v_ctx_4009_ = lean_ctor_get(v_a_4008_, 0);
lean_inc_ref(v_ctx_4009_);
v_simprocs_4010_ = lean_ctor_get(v_a_4008_, 1);
lean_inc_ref(v_simprocs_4010_);
lean_dec(v_a_4008_);
v___y_3971_ = v_simprocs_4010_;
v___y_3972_ = v___y_3992_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3997_;
v___y_3976_ = v___y_3999_;
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___y_3993_;
v___y_3979_ = v_stx_3991_;
v___y_3980_ = v___y_3989_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v_ctx_4009_;
goto v___jp_3970_;
}
else
{
lean_dec_ref_known(v___y_3990_, 1);
if (v___y_3988_ == 0)
{
lean_object* v_ctx_4011_; lean_object* v_simprocs_4012_; 
v_ctx_4011_ = lean_ctor_get(v_a_4008_, 0);
lean_inc_ref(v_ctx_4011_);
v_simprocs_4012_ = lean_ctor_get(v_a_4008_, 1);
lean_inc_ref(v_simprocs_4012_);
lean_dec(v_a_4008_);
v___y_3971_ = v_simprocs_4012_;
v___y_3972_ = v___y_3992_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3997_;
v___y_3976_ = v___y_3999_;
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___y_3993_;
v___y_3979_ = v_stx_3991_;
v___y_3980_ = v___y_3989_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v_ctx_4011_;
goto v___jp_3970_;
}
else
{
lean_object* v_ctx_4013_; lean_object* v_simprocs_4014_; lean_object* v___x_4015_; 
v_ctx_4013_ = lean_ctor_get(v_a_4008_, 0);
lean_inc_ref(v_ctx_4013_);
v_simprocs_4014_ = lean_ctor_get(v_a_4008_, 1);
lean_inc_ref(v_simprocs_4014_);
lean_dec(v_a_4008_);
v___x_4015_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4013_);
v___y_3971_ = v_simprocs_4014_;
v___y_3972_ = v___y_3992_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3997_;
v___y_3976_ = v___y_3999_;
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___y_3993_;
v___y_3979_ = v_stx_3991_;
v___y_3980_ = v___y_3989_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v___x_4015_;
goto v___jp_3970_;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_stx_3991_);
lean_dec(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec(v_tk_3902_);
v_a_4016_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4007_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4007_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
v___jp_4024_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_inc_ref(v___y_4044_);
v___x_4046_ = l_Array_append___redArg(v___y_4044_, v___y_4045_);
lean_dec_ref(v___y_4045_);
lean_inc(v___y_4032_);
lean_inc(v___y_4037_);
v___x_4047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4047_, 0, v___y_4037_);
lean_ctor_set(v___x_4047_, 1, v___y_4032_);
lean_ctor_set(v___x_4047_, 2, v___x_4046_);
v___x_4048_ = l_Lean_Syntax_node6(v___y_4037_, v___y_4029_, v___y_4043_, v___y_4038_, v___y_4025_, v___y_4026_, v___y_4042_, v___x_4047_);
v___y_3988_ = v___y_4034_;
v___y_3989_ = v___y_4041_;
v___y_3990_ = v___y_4031_;
v_stx_3991_ = v___x_4048_;
v___y_3992_ = v___y_4028_;
v___y_3993_ = v___y_4039_;
v___y_3994_ = v___y_4035_;
v___y_3995_ = v___y_4036_;
v___y_3996_ = v___y_4040_;
v___y_3997_ = v___y_4033_;
v___y_3998_ = v___y_4030_;
v___y_3999_ = v___y_4027_;
goto v___jp_3987_;
}
v___jp_4049_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_inc_ref(v___y_4068_);
v___x_4070_ = l_Array_append___redArg(v___y_4068_, v___y_4069_);
lean_dec_ref(v___y_4069_);
lean_inc(v___y_4056_);
lean_inc(v___y_4062_);
v___x_4071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4071_, 0, v___y_4062_);
lean_ctor_set(v___x_4071_, 1, v___y_4056_);
lean_ctor_set(v___x_4071_, 2, v___x_4070_);
if (lean_obj_tag(v___y_4066_) == 0)
{
lean_object* v___x_4072_; 
v___x_4072_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4025_ = v___y_4050_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4052_;
v___y_4028_ = v___y_4053_;
v___y_4029_ = v___y_4054_;
v___y_4030_ = v___y_4055_;
v___y_4031_ = v___y_4057_;
v___y_4032_ = v___y_4056_;
v___y_4033_ = v___y_4058_;
v___y_4034_ = v___y_4061_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4059_;
v___y_4037_ = v___y_4062_;
v___y_4038_ = v___y_4063_;
v___y_4039_ = v___y_4064_;
v___y_4040_ = v___y_4065_;
v___y_4041_ = v___y_4066_;
v___y_4042_ = v___x_4071_;
v___y_4043_ = v___y_4067_;
v___y_4044_ = v___y_4068_;
v___y_4045_ = v___x_4072_;
goto v___jp_4024_;
}
else
{
lean_object* v_val_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_val_4073_ = lean_ctor_get(v___y_4066_, 0);
v___x_4074_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4073_);
v___x_4075_ = lean_array_push(v___x_4074_, v_val_4073_);
v___y_4025_ = v___y_4050_;
v___y_4026_ = v___y_4051_;
v___y_4027_ = v___y_4052_;
v___y_4028_ = v___y_4053_;
v___y_4029_ = v___y_4054_;
v___y_4030_ = v___y_4055_;
v___y_4031_ = v___y_4057_;
v___y_4032_ = v___y_4056_;
v___y_4033_ = v___y_4058_;
v___y_4034_ = v___y_4061_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4059_;
v___y_4037_ = v___y_4062_;
v___y_4038_ = v___y_4063_;
v___y_4039_ = v___y_4064_;
v___y_4040_ = v___y_4065_;
v___y_4041_ = v___y_4066_;
v___y_4042_ = v___x_4071_;
v___y_4043_ = v___y_4067_;
v___y_4044_ = v___y_4068_;
v___y_4045_ = v___x_4075_;
goto v___jp_4024_;
}
}
v___jp_4076_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_inc_ref(v___y_4095_);
v___x_4097_ = l_Array_append___redArg(v___y_4095_, v___y_4096_);
lean_dec_ref(v___y_4096_);
lean_inc(v___y_4082_);
lean_inc(v___y_4088_);
v___x_4098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4098_, 0, v___y_4088_);
lean_ctor_set(v___x_4098_, 1, v___y_4082_);
lean_ctor_set(v___x_4098_, 2, v___x_4097_);
if (lean_obj_tag(v___y_4094_) == 1)
{
lean_object* v_val_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v_val_4099_ = lean_ctor_get(v___y_4094_, 0);
lean_inc(v_val_4099_);
lean_dec_ref_known(v___y_4094_, 1);
v___x_4100_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4088_, 3);
v___x_4101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___y_4088_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
lean_inc_ref(v___y_4095_);
v___x_4102_ = l_Array_append___redArg(v___y_4095_, v_val_4099_);
lean_dec(v_val_4099_);
lean_inc(v___y_4082_);
v___x_4103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4103_, 0, v___y_4088_);
lean_ctor_set(v___x_4103_, 1, v___y_4082_);
lean_ctor_set(v___x_4103_, 2, v___x_4102_);
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___y_4088_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = l_Array_mkArray3___redArg(v___x_4101_, v___x_4103_, v___x_4105_);
v___y_4050_ = v___y_4077_;
v___y_4051_ = v___x_4098_;
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4082_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4086_;
v___y_4060_ = v___y_4087_;
v___y_4061_ = v___y_4085_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___y_4089_;
v___y_4064_ = v___y_4090_;
v___y_4065_ = v___y_4091_;
v___y_4066_ = v___y_4092_;
v___y_4067_ = v___y_4093_;
v___y_4068_ = v___y_4095_;
v___y_4069_ = v___x_4106_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4107_; 
lean_dec(v___y_4094_);
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4050_ = v___y_4077_;
v___y_4051_ = v___x_4098_;
v___y_4052_ = v___y_4078_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4080_;
v___y_4055_ = v___y_4081_;
v___y_4056_ = v___y_4082_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4086_;
v___y_4060_ = v___y_4087_;
v___y_4061_ = v___y_4085_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___y_4089_;
v___y_4064_ = v___y_4090_;
v___y_4065_ = v___y_4091_;
v___y_4066_ = v___y_4092_;
v___y_4067_ = v___y_4093_;
v___y_4068_ = v___y_4095_;
v___y_4069_ = v___x_4107_;
goto v___jp_4049_;
}
}
v___jp_4108_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_inc_ref(v___y_4120_);
v___x_4130_ = l_Array_append___redArg(v___y_4120_, v___y_4129_);
lean_dec_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc(v___y_4113_);
v___x_4131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4131_, 0, v___y_4113_);
lean_ctor_set(v___x_4131_, 1, v___y_4128_);
lean_ctor_set(v___x_4131_, 2, v___x_4130_);
v___x_4132_ = l_Lean_Syntax_node6(v___y_4113_, v___y_4123_, v___y_4111_, v___y_4121_, v___y_4112_, v___y_4127_, v___y_4122_, v___x_4131_);
v___y_3988_ = v___y_4117_;
v___y_3989_ = v___y_4126_;
v___y_3990_ = v___y_4115_;
v_stx_3991_ = v___x_4132_;
v___y_3992_ = v___y_4110_;
v___y_3993_ = v___y_4124_;
v___y_3994_ = v___y_4118_;
v___y_3995_ = v___y_4119_;
v___y_3996_ = v___y_4125_;
v___y_3997_ = v___y_4116_;
v___y_3998_ = v___y_4114_;
v___y_3999_ = v___y_4109_;
goto v___jp_3987_;
}
v___jp_4133_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_inc_ref(v___y_4145_);
v___x_4154_ = l_Array_append___redArg(v___y_4145_, v___y_4153_);
lean_dec_ref(v___y_4153_);
lean_inc(v___y_4152_);
lean_inc(v___y_4138_);
v___x_4155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4155_, 0, v___y_4138_);
lean_ctor_set(v___x_4155_, 1, v___y_4152_);
lean_ctor_set(v___x_4155_, 2, v___x_4154_);
if (lean_obj_tag(v___y_4150_) == 0)
{
lean_object* v___x_4156_; 
v___x_4156_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4137_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4144_;
v___y_4119_ = v___y_4142_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___x_4155_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___y_4147_;
v___y_4125_ = v___y_4149_;
v___y_4126_ = v___y_4150_;
v___y_4127_ = v___y_4151_;
v___y_4128_ = v___y_4152_;
v___y_4129_ = v___x_4156_;
goto v___jp_4108_;
}
else
{
lean_object* v_val_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_val_4157_ = lean_ctor_get(v___y_4150_, 0);
v___x_4158_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4157_);
v___x_4159_ = lean_array_push(v___x_4158_, v_val_4157_);
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4137_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___y_4140_;
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4144_;
v___y_4119_ = v___y_4142_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___x_4155_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___y_4147_;
v___y_4125_ = v___y_4149_;
v___y_4126_ = v___y_4150_;
v___y_4127_ = v___y_4151_;
v___y_4128_ = v___y_4152_;
v___y_4129_ = v___x_4159_;
goto v___jp_4108_;
}
}
v___jp_4160_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_inc_ref(v___y_4172_);
v___x_4181_ = l_Array_append___redArg(v___y_4172_, v___y_4180_);
lean_dec_ref(v___y_4180_);
lean_inc(v___y_4178_);
lean_inc(v___y_4165_);
v___x_4182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4182_, 0, v___y_4165_);
lean_ctor_set(v___x_4182_, 1, v___y_4178_);
lean_ctor_set(v___x_4182_, 2, v___x_4181_);
if (lean_obj_tag(v___y_4179_) == 1)
{
lean_object* v_val_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_val_4183_ = lean_ctor_get(v___y_4179_, 0);
lean_inc(v_val_4183_);
lean_dec_ref_known(v___y_4179_, 1);
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4165_, 3);
v___x_4185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___y_4165_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
lean_inc_ref(v___y_4172_);
v___x_4186_ = l_Array_append___redArg(v___y_4172_, v_val_4183_);
lean_dec(v_val_4183_);
lean_inc(v___y_4178_);
v___x_4187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4187_, 0, v___y_4165_);
lean_ctor_set(v___x_4187_, 1, v___y_4178_);
lean_ctor_set(v___x_4187_, 2, v___x_4186_);
v___x_4188_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___y_4165_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = l_Array_mkArray3___redArg(v___x_4185_, v___x_4187_, v___x_4189_);
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
v___y_4136_ = v___y_4163_;
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4165_;
v___y_4139_ = v___y_4166_;
v___y_4140_ = v___y_4167_;
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4170_;
v___y_4143_ = v___y_4171_;
v___y_4144_ = v___y_4169_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___y_4175_;
v___y_4148_ = v___y_4174_;
v___y_4149_ = v___y_4176_;
v___y_4150_ = v___y_4177_;
v___y_4151_ = v___x_4182_;
v___y_4152_ = v___y_4178_;
v___y_4153_ = v___x_4190_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4191_; 
lean_dec(v___y_4179_);
v___x_4191_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4134_ = v___y_4161_;
v___y_4135_ = v___y_4162_;
v___y_4136_ = v___y_4163_;
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4165_;
v___y_4139_ = v___y_4166_;
v___y_4140_ = v___y_4167_;
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4170_;
v___y_4143_ = v___y_4171_;
v___y_4144_ = v___y_4169_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___y_4175_;
v___y_4148_ = v___y_4174_;
v___y_4149_ = v___y_4176_;
v___y_4150_ = v___y_4177_;
v___y_4151_ = v___x_4182_;
v___y_4152_ = v___y_4178_;
v___y_4153_ = v___x_4191_;
goto v___jp_4133_;
}
}
v___jp_4192_:
{
lean_object* v_ref_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v_ref_4208_ = lean_ctor_get(v___y_4196_, 2);
v___x_4209_ = l_Lean_SourceInfo_fromRef(v_ref_4208_, v___y_4207_);
v___x_4210_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4211_ = l_Lean_Name_mkStr4(v___x_3888_, v___x_3889_, v___x_3890_, v___x_4210_);
v___x_4212_ = l_Lean_SourceInfo_fromRef(v_tk_3902_, v___x_3887_);
v___x_4213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
lean_ctor_set(v___x_4213_, 1, v___x_4210_);
v___x_4214_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4215_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4209_);
v___x_4216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4209_);
lean_ctor_set(v___x_4216_, 1, v___x_4214_);
lean_ctor_set(v___x_4216_, 2, v___x_4215_);
if (lean_obj_tag(v___y_4193_) == 1)
{
lean_object* v_val_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_val_4217_ = lean_ctor_get(v___y_4193_, 0);
lean_inc(v_val_4217_);
lean_dec_ref_known(v___y_4193_, 1);
v___x_4218_ = l_Lean_SourceInfo_fromRef(v_val_4217_, v___x_3887_);
lean_dec(v_val_4217_);
v___x_4219_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4218_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
v___x_4221_ = l_Array_mkArray1___redArg(v___x_4220_);
v___y_4077_ = v___x_4216_;
v___y_4078_ = v___y_4194_;
v___y_4079_ = v___y_4195_;
v___y_4080_ = v___x_4211_;
v___y_4081_ = v___y_4196_;
v___y_4082_ = v___x_4214_;
v___y_4083_ = v___y_4197_;
v___y_4084_ = v___y_4198_;
v___y_4085_ = v___y_4199_;
v___y_4086_ = v___y_4200_;
v___y_4087_ = v___y_4201_;
v___y_4088_ = v___x_4209_;
v___y_4089_ = v___y_4202_;
v___y_4090_ = v___y_4203_;
v___y_4091_ = v___y_4204_;
v___y_4092_ = v___y_4205_;
v___y_4093_ = v___x_4213_;
v___y_4094_ = v___y_4206_;
v___y_4095_ = v___x_4215_;
v___y_4096_ = v___x_4221_;
goto v___jp_4076_;
}
else
{
lean_object* v___x_4222_; 
lean_dec(v___y_4193_);
v___x_4222_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4077_ = v___x_4216_;
v___y_4078_ = v___y_4194_;
v___y_4079_ = v___y_4195_;
v___y_4080_ = v___x_4211_;
v___y_4081_ = v___y_4196_;
v___y_4082_ = v___x_4214_;
v___y_4083_ = v___y_4197_;
v___y_4084_ = v___y_4198_;
v___y_4085_ = v___y_4199_;
v___y_4086_ = v___y_4200_;
v___y_4087_ = v___y_4201_;
v___y_4088_ = v___x_4209_;
v___y_4089_ = v___y_4202_;
v___y_4090_ = v___y_4203_;
v___y_4091_ = v___y_4204_;
v___y_4092_ = v___y_4205_;
v___y_4093_ = v___x_4213_;
v___y_4094_ = v___y_4206_;
v___y_4095_ = v___x_4215_;
v___y_4096_ = v___x_4222_;
goto v___jp_4076_;
}
}
v___jp_4223_:
{
if (lean_obj_tag(v___y_4228_) == 0)
{
uint8_t v___x_4238_; 
v___x_4238_ = 0;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4226_;
v___y_4196_ = v___y_4227_;
v___y_4197_ = v___y_4228_;
v___y_4198_ = v___y_4229_;
v___y_4199_ = v___y_4230_;
v___y_4200_ = v___y_4231_;
v___y_4201_ = v___y_4232_;
v___y_4202_ = v___y_4233_;
v___y_4203_ = v___y_4234_;
v___y_4204_ = v___y_4235_;
v___y_4205_ = v___y_4237_;
v___y_4206_ = v___y_4236_;
v___y_4207_ = v___x_4238_;
goto v___jp_4192_;
}
else
{
if (v___y_4230_ == 0)
{
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4226_;
v___y_4196_ = v___y_4227_;
v___y_4197_ = v___y_4228_;
v___y_4198_ = v___y_4229_;
v___y_4199_ = v___y_4230_;
v___y_4200_ = v___y_4231_;
v___y_4201_ = v___y_4232_;
v___y_4202_ = v___y_4233_;
v___y_4203_ = v___y_4234_;
v___y_4204_ = v___y_4235_;
v___y_4205_ = v___y_4237_;
v___y_4206_ = v___y_4236_;
v___y_4207_ = v___y_4230_;
goto v___jp_4192_;
}
else
{
lean_object* v_ref_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_ref_4239_ = lean_ctor_get(v___y_4227_, 2);
v___x_4240_ = 0;
v___x_4241_ = l_Lean_SourceInfo_fromRef(v_ref_4239_, v___x_4240_);
v___x_4242_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4243_ = l_Lean_Name_mkStr4(v___x_3888_, v___x_3889_, v___x_3890_, v___x_4242_);
v___x_4244_ = l_Lean_SourceInfo_fromRef(v_tk_3902_, v___x_3887_);
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4248_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4241_);
v___x_4249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4241_);
lean_ctor_set(v___x_4249_, 1, v___x_4247_);
lean_ctor_set(v___x_4249_, 2, v___x_4248_);
if (lean_obj_tag(v___y_4224_) == 1)
{
lean_object* v_val_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v_val_4250_ = lean_ctor_get(v___y_4224_, 0);
lean_inc(v_val_4250_);
lean_dec_ref_known(v___y_4224_, 1);
v___x_4251_ = l_Lean_SourceInfo_fromRef(v_val_4250_, v___x_3887_);
lean_dec(v_val_4250_);
v___x_4252_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4251_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = l_Array_mkArray1___redArg(v___x_4253_);
v___y_4161_ = v___y_4225_;
v___y_4162_ = v___y_4226_;
v___y_4163_ = v___x_4246_;
v___y_4164_ = v___x_4249_;
v___y_4165_ = v___x_4241_;
v___y_4166_ = v___y_4227_;
v___y_4167_ = v___y_4228_;
v___y_4168_ = v___y_4229_;
v___y_4169_ = v___y_4232_;
v___y_4170_ = v___y_4231_;
v___y_4171_ = v___y_4230_;
v___y_4172_ = v___x_4248_;
v___y_4173_ = v___y_4233_;
v___y_4174_ = v___x_4243_;
v___y_4175_ = v___y_4234_;
v___y_4176_ = v___y_4235_;
v___y_4177_ = v___y_4237_;
v___y_4178_ = v___x_4247_;
v___y_4179_ = v___y_4236_;
v___y_4180_ = v___x_4254_;
goto v___jp_4160_;
}
else
{
lean_object* v___x_4255_; 
lean_dec(v___y_4224_);
v___x_4255_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4161_ = v___y_4225_;
v___y_4162_ = v___y_4226_;
v___y_4163_ = v___x_4246_;
v___y_4164_ = v___x_4249_;
v___y_4165_ = v___x_4241_;
v___y_4166_ = v___y_4227_;
v___y_4167_ = v___y_4228_;
v___y_4168_ = v___y_4229_;
v___y_4169_ = v___y_4232_;
v___y_4170_ = v___y_4231_;
v___y_4171_ = v___y_4230_;
v___y_4172_ = v___x_4248_;
v___y_4173_ = v___y_4233_;
v___y_4174_ = v___x_4243_;
v___y_4175_ = v___y_4234_;
v___y_4176_ = v___y_4235_;
v___y_4177_ = v___y_4237_;
v___y_4178_ = v___x_4247_;
v___y_4179_ = v___y_4236_;
v___y_4180_ = v___x_4255_;
goto v___jp_4160_;
}
}
}
}
v___jp_4256_:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = lean_unsigned_to_nat(3u);
v___x_4272_ = l_Lean_Syntax_getArg(v___y_4260_, v___x_4271_);
lean_dec(v___y_4260_);
v___x_4273_ = l_Lean_Syntax_getOptional_x3f(v___x_4272_);
lean_dec(v___x_4272_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v___x_4274_; 
v___x_4274_ = lean_box(0);
v___y_4224_ = v___y_4258_;
v___y_4225_ = v___y_4270_;
v___y_4226_ = v___y_4263_;
v___y_4227_ = v___y_4269_;
v___y_4228_ = v___y_4261_;
v___y_4229_ = v___y_4268_;
v___y_4230_ = v___y_4257_;
v___y_4231_ = v___y_4266_;
v___y_4232_ = v___y_4265_;
v___y_4233_ = v___y_4259_;
v___y_4234_ = v___y_4264_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v_args_4262_;
v___y_4237_ = v___x_4274_;
goto v___jp_4223_;
}
else
{
lean_object* v_val_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
v_val_4275_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4273_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_val_4275_);
lean_dec(v___x_4273_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_val_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
v___y_4224_ = v___y_4258_;
v___y_4225_ = v___y_4270_;
v___y_4226_ = v___y_4263_;
v___y_4227_ = v___y_4269_;
v___y_4228_ = v___y_4261_;
v___y_4229_ = v___y_4268_;
v___y_4230_ = v___y_4257_;
v___y_4231_ = v___y_4266_;
v___y_4232_ = v___y_4265_;
v___y_4233_ = v___y_4259_;
v___y_4234_ = v___y_4264_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v_args_4262_;
v___y_4237_ = v___x_4280_;
goto v___jp_4223_;
}
}
}
}
v___jp_4284_:
{
lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4299_ = l_Lean_Syntax_getArg(v___y_4288_, v___y_4286_);
v___x_4300_ = l_Lean_Syntax_isNone(v___x_4299_);
if (v___x_4300_ == 0)
{
uint8_t v___x_4301_; 
lean_inc(v___x_4299_);
v___x_4301_ = l_Lean_Syntax_matchesNull(v___x_4299_, v___x_4283_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; 
lean_dec(v___x_4299_);
lean_dec(v_o_4290_);
lean_dec(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec(v_tk_3902_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_4302_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4302_;
}
else
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4303_ = l_Lean_Syntax_getArg(v___x_4299_, v___x_3901_);
lean_dec(v___x_4299_);
v___x_4304_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3890_);
lean_inc_ref(v___x_3889_);
lean_inc_ref(v___x_3888_);
v___x_4305_ = l_Lean_Name_mkStr4(v___x_3888_, v___x_3889_, v___x_3890_, v___x_4304_);
lean_inc(v___x_4303_);
v___x_4306_ = l_Lean_Syntax_isOfKind(v___x_4303_, v___x_4305_);
lean_dec(v___x_4305_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
lean_dec(v___x_4303_);
lean_dec(v_o_4290_);
lean_dec(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec(v_tk_3902_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_4307_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4307_;
}
else
{
lean_object* v___x_4308_; lean_object* v_args_4309_; lean_object* v___x_4310_; 
v___x_4308_ = l_Lean_Syntax_getArg(v___x_4303_, v___x_4283_);
lean_dec(v___x_4303_);
v_args_4309_ = l_Lean_Syntax_getArgs(v___x_4308_);
lean_dec(v___x_4308_);
v___x_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4310_, 0, v_args_4309_);
v___y_4257_ = v___y_4285_;
v___y_4258_ = v_o_4290_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
v_args_4262_ = v___x_4310_;
v___y_4263_ = v___y_4291_;
v___y_4264_ = v___y_4292_;
v___y_4265_ = v___y_4293_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v___y_4268_ = v___y_4296_;
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4298_;
goto v___jp_4256_;
}
}
}
else
{
lean_object* v___x_4311_; 
lean_dec(v___x_4299_);
v___x_4311_ = lean_box(0);
v___y_4257_ = v___y_4285_;
v___y_4258_ = v_o_4290_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4288_;
v___y_4261_ = v___y_4289_;
v_args_4262_ = v___x_4311_;
v___y_4263_ = v___y_4291_;
v___y_4264_ = v___y_4292_;
v___y_4265_ = v___y_4293_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v___y_4268_ = v___y_4296_;
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4298_;
goto v___jp_4256_;
}
}
v___jp_4312_:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4322_ = lean_unsigned_to_nat(2u);
v___x_4323_ = l_Lean_Syntax_getArg(v_stx_3886_, v___x_4322_);
v___x_4324_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3890_);
lean_inc_ref(v___x_3889_);
lean_inc_ref(v___x_3888_);
v___x_4325_ = l_Lean_Name_mkStr4(v___x_3888_, v___x_3889_, v___x_3890_, v___x_4324_);
lean_inc(v___x_4323_);
v___x_4326_ = l_Lean_Syntax_isOfKind(v___x_4323_, v___x_4325_);
lean_dec(v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; 
lean_dec(v___x_4323_);
lean_dec(v_bang_4313_);
lean_dec(v_tk_3902_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_4327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4327_;
}
else
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4328_ = l_Lean_Syntax_getArg(v___x_4323_, v___x_3901_);
v___x_4329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3890_);
lean_inc_ref(v___x_3889_);
lean_inc_ref(v___x_3888_);
v___x_4330_ = l_Lean_Name_mkStr4(v___x_3888_, v___x_3889_, v___x_3890_, v___x_4329_);
lean_inc(v___x_4328_);
v___x_4331_ = l_Lean_Syntax_isOfKind(v___x_4328_, v___x_4330_);
lean_dec(v___x_4330_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; 
lean_dec(v___x_4328_);
lean_dec(v___x_4323_);
lean_dec(v_bang_4313_);
lean_dec(v_tk_3902_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_4332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4332_;
}
else
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = l_Lean_Syntax_getArg(v___x_4323_, v___x_4283_);
v___x_4334_ = l_Lean_Syntax_isNone(v___x_4333_);
if (v___x_4334_ == 0)
{
uint8_t v___x_4335_; 
lean_inc(v___x_4333_);
v___x_4335_ = l_Lean_Syntax_matchesNull(v___x_4333_, v___x_4283_);
if (v___x_4335_ == 0)
{
lean_object* v___x_4336_; 
lean_dec(v___x_4333_);
lean_dec(v___x_4328_);
lean_dec(v___x_4323_);
lean_dec(v_bang_4313_);
lean_dec(v_tk_3902_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
v___x_4336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4336_;
}
else
{
lean_object* v_o_4337_; lean_object* v___x_4338_; 
v_o_4337_ = l_Lean_Syntax_getArg(v___x_4333_, v___x_3901_);
lean_dec(v___x_4333_);
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v_o_4337_);
v___y_4285_ = v___x_4326_;
v___y_4286_ = v___x_4322_;
v___y_4287_ = v___x_4328_;
v___y_4288_ = v___x_4323_;
v___y_4289_ = v_bang_4313_;
v_o_4290_ = v___x_4338_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4315_;
v___y_4293_ = v___y_4316_;
v___y_4294_ = v___y_4317_;
v___y_4295_ = v___y_4318_;
v___y_4296_ = v___y_4319_;
v___y_4297_ = v___y_4320_;
v___y_4298_ = v___y_4321_;
goto v___jp_4284_;
}
}
else
{
lean_object* v___x_4339_; 
lean_dec(v___x_4333_);
v___x_4339_ = lean_box(0);
v___y_4285_ = v___x_4326_;
v___y_4286_ = v___x_4322_;
v___y_4287_ = v___x_4328_;
v___y_4288_ = v___x_4323_;
v___y_4289_ = v_bang_4313_;
v_o_4290_ = v___x_4339_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4315_;
v___y_4293_ = v___y_4316_;
v___y_4294_ = v___y_4317_;
v___y_4295_ = v___y_4318_;
v___y_4296_ = v___y_4319_;
v___y_4297_ = v___y_4320_;
v___y_4298_ = v___y_4321_;
goto v___jp_4284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4347_, lean_object* v_stx_4348_, lean_object* v___x_4349_, lean_object* v___x_4350_, lean_object* v___x_4351_, lean_object* v___x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v___x_8002__boxed_4362_; uint8_t v___x_8003__boxed_4363_; lean_object* v_res_4364_; 
v___x_8002__boxed_4362_ = lean_unbox(v___x_4347_);
v___x_8003__boxed_4363_ = lean_unbox(v___x_4349_);
v_res_4364_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8002__boxed_4362_, v_stx_4348_, v___x_8003__boxed_4363_, v___x_4350_, v___x_4351_, v___x_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v_stx_4348_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___y_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4371_);
v___x_4385_ = l_Lean_Syntax_isOfKind(v_stx_4371_, v___x_4384_);
v___x_4386_ = 1;
v___x_4387_ = lean_box(v___x_4385_);
v___x_4388_ = lean_box(v___x_4386_);
v___y_4389_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4389_, 0, v___x_4387_);
lean_closure_set(v___y_4389_, 1, v_stx_4371_);
lean_closure_set(v___y_4389_, 2, v___x_4388_);
lean_closure_set(v___y_4389_, 3, v___x_4381_);
lean_closure_set(v___y_4389_, 4, v___x_4382_);
lean_closure_set(v___y_4389_, 5, v___x_4383_);
v___x_4390_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4390_, 0, v___y_4389_);
v___x_4391_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4390_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4410_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4411_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4410_, v___x_4411_, v___x_4412_, v___x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4445_ = l_Lean_addBuiltinDeclarationRanges(v___x_4443_, v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4447_;
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
