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
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__7(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
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
lean_dec_ref(v___x_25_);
v_str_31_ = lean_ctor_get(v_pre_26_, 1);
lean_inc_ref(v_str_31_);
lean_dec_ref(v_pre_26_);
v_str_32_ = lean_ctor_get(v_pre_27_, 1);
lean_inc_ref(v_str_32_);
lean_dec_ref(v_pre_27_);
v_str_33_ = lean_ctor_get(v_pre_28_, 1);
lean_inc_ref(v_str_33_);
lean_dec_ref(v_pre_28_);
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
lean_dec_ref(v___x_48_);
v_str_54_ = lean_ctor_get(v_pre_49_, 1);
lean_inc_ref(v_str_54_);
lean_dec_ref(v_pre_49_);
v_str_55_ = lean_ctor_get(v_pre_50_, 1);
lean_inc_ref(v_str_55_);
lean_dec_ref(v_pre_50_);
v_str_56_ = lean_ctor_get(v_pre_51_, 1);
lean_inc_ref(v_str_56_);
lean_dec_ref(v_pre_51_);
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
v_id_67_ = lean_erase_macro_scopes(v___x_66_);
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
lean_dec_ref(v_pre_51_);
lean_dec_ref(v_pre_50_);
lean_dec_ref(v_pre_49_);
lean_dec_ref(v___x_48_);
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
lean_dec(v_pre_51_);
lean_dec_ref(v_pre_50_);
lean_dec_ref(v_pre_49_);
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v_pre_49_);
lean_dec(v_pre_50_);
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v___x_48_);
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
lean_dec_ref(v_pre_28_);
lean_dec_ref(v_pre_27_);
lean_dec_ref(v_pre_26_);
lean_dec_ref(v___x_25_);
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
lean_dec_ref(v_pre_27_);
lean_dec(v_pre_28_);
lean_dec_ref(v_pre_26_);
lean_dec_ref(v___x_25_);
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
lean_dec_ref(v_pre_26_);
lean_dec(v_pre_27_);
lean_dec_ref(v___x_25_);
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
lean_dec_ref(v___x_25_);
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
uint8_t v___x_38714__boxed_208_; lean_object* v_res_209_; 
v___x_38714__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_38714__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_38741__boxed_246_; lean_object* v_res_247_; 
v___x_38741__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_38741__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
lean_inc(v_head_264_);
v_tail_265_ = lean_ctor_get(v_as_x27_259_, 1);
lean_inc(v_tail_265_);
lean_dec_ref(v_as_x27_259_);
v_ref_266_ = lean_ctor_get(v___y_261_, 5);
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
lean_dec(v___x_278_);
return v_res_283_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(lean_object* v_opts_284_, lean_object* v_opt_285_){
_start:
{
lean_object* v_name_286_; lean_object* v_defValue_287_; lean_object* v_map_288_; lean_object* v___x_289_; 
v_name_286_ = lean_ctor_get(v_opt_285_, 0);
v_defValue_287_ = lean_ctor_get(v_opt_285_, 1);
v_map_288_ = lean_ctor_get(v_opts_284_, 0);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_288_, v_name_286_);
if (lean_obj_tag(v___x_289_) == 0)
{
uint8_t v___x_290_; 
v___x_290_ = lean_unbox(v_defValue_287_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_291_);
lean_dec_ref(v___x_289_);
if (lean_obj_tag(v_val_291_) == 1)
{
uint8_t v_v_292_; 
v_v_292_ = lean_ctor_get_uint8(v_val_291_, 0);
lean_dec_ref(v_val_291_);
return v_v_292_;
}
else
{
uint8_t v___x_293_; 
lean_dec(v_val_291_);
v___x_293_ = lean_unbox(v_defValue_287_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11___boxed(lean_object* v_opts_294_, lean_object* v_opt_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(v_opts_294_, v_opt_295_);
lean_dec_ref(v_opt_295_);
lean_dec_ref(v_opts_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_opt_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_options_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_options_301_ = lean_ctor_get(v___y_299_, 2);
v___x_302_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(v_options_301_, v_opt_298_);
v___x_303_ = lean_box(v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_opt_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(v_opt_305_, v___y_306_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_opt_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v_mctx_318_; lean_object* v_lctx_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_315_ = lean_st_ref_get(v___y_313_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_env_316_);
lean_dec(v___x_315_);
v___x_317_ = lean_st_ref_get(v___y_311_);
v_mctx_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_mctx_318_);
lean_dec(v___x_317_);
v_lctx_319_ = lean_ctor_get(v___y_310_, 2);
v_options_320_ = lean_ctor_get(v___y_312_, 2);
lean_inc_ref(v_options_320_);
lean_inc_ref(v_lctx_319_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_316_);
lean_ctor_set(v___x_321_, 1, v_mctx_318_);
lean_ctor_set(v___x_321_, 2, v_lctx_319_);
lean_ctor_set(v___x_321_, 3, v_options_320_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_309_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0(uint8_t v___y_338_, uint8_t v_suppressElabErrors_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 1)
{
lean_object* v_pre_341_; 
v_pre_341_ = lean_ctor_get(v_x_340_, 0);
switch(lean_obj_tag(v_pre_341_))
{
case 1:
{
lean_object* v_pre_342_; 
v_pre_342_ = lean_ctor_get(v_pre_341_, 0);
switch(lean_obj_tag(v_pre_342_))
{
case 0:
{
lean_object* v_str_343_; lean_object* v_str_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_str_343_ = lean_ctor_get(v_x_340_, 1);
v_str_344_ = lean_ctor_get(v_pre_341_, 1);
v___x_345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__0));
v___x_346_ = lean_string_dec_eq(v_str_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_348_ = lean_string_dec_eq(v_str_344_, v___x_347_);
if (v___x_348_ == 0)
{
return v___y_338_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__1));
v___x_350_ = lean_string_dec_eq(v_str_343_, v___x_349_);
if (v___x_350_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
}
else
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__2));
v___x_352_ = lean_string_dec_eq(v_str_343_, v___x_351_);
if (v___x_352_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
}
case 1:
{
lean_object* v_pre_353_; 
v_pre_353_ = lean_ctor_get(v_pre_342_, 0);
if (lean_obj_tag(v_pre_353_) == 0)
{
lean_object* v_str_354_; lean_object* v_str_355_; lean_object* v_str_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_str_354_ = lean_ctor_get(v_x_340_, 1);
v_str_355_ = lean_ctor_get(v_pre_341_, 1);
v_str_356_ = lean_ctor_get(v_pre_342_, 1);
v___x_357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__3));
v___x_358_ = lean_string_dec_eq(v_str_356_, v___x_357_);
if (v___x_358_ == 0)
{
return v___y_338_;
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__4));
v___x_360_ = lean_string_dec_eq(v_str_355_, v___x_359_);
if (v___x_360_ == 0)
{
return v___y_338_;
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__5));
v___x_362_ = lean_string_dec_eq(v_str_354_, v___x_361_);
if (v___x_362_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
}
}
else
{
return v___y_338_;
}
}
default: 
{
return v___y_338_;
}
}
}
case 0:
{
lean_object* v_str_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_str_363_ = lean_ctor_get(v_x_340_, 1);
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___closed__6));
v___x_365_ = lean_string_dec_eq(v_str_363_, v___x_364_);
if (v___x_365_ == 0)
{
return v___y_338_;
}
else
{
return v_suppressElabErrors_339_;
}
}
default: 
{
return v___y_338_;
}
}
}
else
{
return v___y_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___boxed(lean_object* v___y_366_, lean_object* v_suppressElabErrors_367_, lean_object* v_x_368_){
_start:
{
uint8_t v___y_38925__boxed_369_; uint8_t v_suppressElabErrors_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v___y_38925__boxed_369_ = lean_unbox(v___y_366_);
v_suppressElabErrors_boxed_370_ = lean_unbox(v_suppressElabErrors_367_);
v_res_371_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0(v___y_38925__boxed_369_, v_suppressElabErrors_boxed_370_, v_x_368_);
lean_dec(v_x_368_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(lean_object* v_ref_374_, lean_object* v_msgData_375_, uint8_t v_severity_376_, uint8_t v_isSilent_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___y_384_; lean_object* v___y_385_; uint8_t v___y_386_; uint8_t v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_422_; uint8_t v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; uint8_t v___y_426_; lean_object* v___y_427_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_447_; uint8_t v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; uint8_t v___y_451_; lean_object* v___y_452_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; uint8_t v___y_462_; uint8_t v___x_467_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; uint8_t v___y_474_; uint8_t v___y_475_; uint8_t v___y_477_; uint8_t v___x_492_; 
v___x_467_ = 2;
v___x_492_ = l_Lean_instBEqMessageSeverity_beq(v_severity_376_, v___x_467_);
if (v___x_492_ == 0)
{
v___y_477_ = v___x_492_;
goto v___jp_476_;
}
else
{
uint8_t v___x_493_; 
lean_inc_ref(v_msgData_375_);
v___x_493_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_375_);
v___y_477_ = v___x_493_;
goto v___jp_476_;
}
v___jp_383_:
{
lean_object* v___x_393_; lean_object* v_currNamespace_394_; lean_object* v_openDecls_395_; lean_object* v_env_396_; lean_object* v_nextMacroScope_397_; lean_object* v_ngen_398_; lean_object* v_auxDeclNGen_399_; lean_object* v_traceState_400_; lean_object* v_cache_401_; lean_object* v_messages_402_; lean_object* v_infoState_403_; lean_object* v_snapshotTasks_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_418_; 
v___x_393_ = lean_st_ref_take(v___y_392_);
v_currNamespace_394_ = lean_ctor_get(v___y_391_, 6);
v_openDecls_395_ = lean_ctor_get(v___y_391_, 7);
v_env_396_ = lean_ctor_get(v___x_393_, 0);
v_nextMacroScope_397_ = lean_ctor_get(v___x_393_, 1);
v_ngen_398_ = lean_ctor_get(v___x_393_, 2);
v_auxDeclNGen_399_ = lean_ctor_get(v___x_393_, 3);
v_traceState_400_ = lean_ctor_get(v___x_393_, 4);
v_cache_401_ = lean_ctor_get(v___x_393_, 5);
v_messages_402_ = lean_ctor_get(v___x_393_, 6);
v_infoState_403_ = lean_ctor_get(v___x_393_, 7);
v_snapshotTasks_404_ = lean_ctor_get(v___x_393_, 8);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_418_ == 0)
{
v___x_406_ = v___x_393_;
v_isShared_407_ = v_isSharedCheck_418_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snapshotTasks_404_);
lean_inc(v_infoState_403_);
lean_inc(v_messages_402_);
lean_inc(v_cache_401_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_399_);
lean_inc(v_ngen_398_);
lean_inc(v_nextMacroScope_397_);
lean_inc(v_env_396_);
lean_dec(v___x_393_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_418_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_openDecls_395_);
lean_inc(v_currNamespace_394_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_currNamespace_394_);
lean_ctor_set(v___x_408_, 1, v_openDecls_395_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___y_385_);
lean_inc_ref(v___y_389_);
lean_inc_ref(v___y_388_);
v___x_410_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_410_, 0, v___y_388_);
lean_ctor_set(v___x_410_, 1, v___y_384_);
lean_ctor_set(v___x_410_, 2, v___y_390_);
lean_ctor_set(v___x_410_, 3, v___y_389_);
lean_ctor_set(v___x_410_, 4, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5, v___y_387_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 1, v___y_386_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*5 + 2, v_isSilent_377_);
v___x_411_ = l_Lean_MessageLog_add(v___x_410_, v_messages_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 6, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_env_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_nextMacroScope_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_ngen_398_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_auxDeclNGen_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_traceState_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_cache_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_infoState_403_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_snapshotTasks_404_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_st_ref_set(v___y_392_, v___x_413_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
v___jp_419_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_443_; 
v___x_428_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_375_);
v___x_429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(v___x_428_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_443_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc_ref_n(v___y_425_, 2);
v___x_434_ = l_Lean_FileMap_toPosition(v___y_425_, v___y_421_);
lean_dec(v___y_421_);
v___x_435_ = l_Lean_FileMap_toPosition(v___y_425_, v___y_427_);
lean_dec(v___y_427_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___closed__0));
if (v___y_426_ == 0)
{
lean_del_object(v___x_432_);
lean_dec_ref(v___y_420_);
v___y_384_ = v___x_434_;
v___y_385_ = v_a_430_;
v___y_386_ = v___y_422_;
v___y_387_ = v___y_423_;
v___y_388_ = v___y_424_;
v___y_389_ = v___x_437_;
v___y_390_ = v___x_436_;
v___y_391_ = v___y_380_;
v___y_392_ = v___y_381_;
goto v___jp_383_;
}
else
{
uint8_t v___x_438_; 
lean_inc(v_a_430_);
v___x_438_ = l_Lean_MessageData_hasTag(v___y_420_, v_a_430_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_dec_ref(v___x_436_);
lean_dec_ref(v___x_434_);
lean_dec(v_a_430_);
v___x_439_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_439_);
v___x_441_ = v___x_432_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_del_object(v___x_432_);
v___y_384_ = v___x_434_;
v___y_385_ = v_a_430_;
v___y_386_ = v___y_422_;
v___y_387_ = v___y_423_;
v___y_388_ = v___y_424_;
v___y_389_ = v___x_437_;
v___y_390_ = v___x_436_;
v___y_391_ = v___y_380_;
v___y_392_ = v___y_381_;
goto v___jp_383_;
}
}
}
}
v___jp_444_:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Syntax_getTailPos_x3f(v___y_447_, v___y_448_);
lean_dec(v___y_447_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_inc(v___y_452_);
v___y_420_ = v___y_445_;
v___y_421_ = v___y_452_;
v___y_422_ = v___y_446_;
v___y_423_ = v___y_448_;
v___y_424_ = v___y_449_;
v___y_425_ = v___y_450_;
v___y_426_ = v___y_451_;
v___y_427_ = v___y_452_;
goto v___jp_419_;
}
else
{
lean_object* v_val_454_; 
v_val_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_val_454_);
lean_dec_ref(v___x_453_);
v___y_420_ = v___y_445_;
v___y_421_ = v___y_452_;
v___y_422_ = v___y_446_;
v___y_423_ = v___y_448_;
v___y_424_ = v___y_449_;
v___y_425_ = v___y_450_;
v___y_426_ = v___y_451_;
v___y_427_ = v_val_454_;
goto v___jp_419_;
}
}
v___jp_455_:
{
lean_object* v_ref_463_; lean_object* v___x_464_; 
v_ref_463_ = l_Lean_replaceRef(v_ref_374_, v___y_459_);
v___x_464_ = l_Lean_Syntax_getPos_x3f(v_ref_463_, v___y_457_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___y_445_ = v___y_456_;
v___y_446_ = v___y_462_;
v___y_447_ = v_ref_463_;
v___y_448_ = v___y_457_;
v___y_449_ = v___y_458_;
v___y_450_ = v___y_460_;
v___y_451_ = v___y_461_;
v___y_452_ = v___x_465_;
goto v___jp_444_;
}
else
{
lean_object* v_val_466_; 
v_val_466_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_466_);
lean_dec_ref(v___x_464_);
v___y_445_ = v___y_456_;
v___y_446_ = v___y_462_;
v___y_447_ = v_ref_463_;
v___y_448_ = v___y_457_;
v___y_449_ = v___y_458_;
v___y_450_ = v___y_460_;
v___y_451_ = v___y_461_;
v___y_452_ = v_val_466_;
goto v___jp_444_;
}
}
v___jp_468_:
{
if (v___y_475_ == 0)
{
v___y_456_ = v___y_472_;
v___y_457_ = v___y_474_;
v___y_458_ = v___y_470_;
v___y_459_ = v___y_469_;
v___y_460_ = v___y_471_;
v___y_461_ = v___y_473_;
v___y_462_ = v_severity_376_;
goto v___jp_455_;
}
else
{
v___y_456_ = v___y_472_;
v___y_457_ = v___y_474_;
v___y_458_ = v___y_470_;
v___y_459_ = v___y_469_;
v___y_460_ = v___y_471_;
v___y_461_ = v___y_473_;
v___y_462_ = v___x_467_;
goto v___jp_455_;
}
}
v___jp_476_:
{
if (v___y_477_ == 0)
{
lean_object* v_fileName_478_; lean_object* v_fileMap_479_; lean_object* v_options_480_; lean_object* v_ref_481_; uint8_t v_suppressElabErrors_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___f_485_; uint8_t v___x_486_; uint8_t v___x_487_; 
v_fileName_478_ = lean_ctor_get(v___y_380_, 0);
v_fileMap_479_ = lean_ctor_get(v___y_380_, 1);
v_options_480_ = lean_ctor_get(v___y_380_, 2);
v_ref_481_ = lean_ctor_get(v___y_380_, 5);
v_suppressElabErrors_482_ = lean_ctor_get_uint8(v___y_380_, sizeof(void*)*14 + 1);
v___x_483_ = lean_box(v___y_477_);
v___x_484_ = lean_box(v_suppressElabErrors_482_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_485_, 0, v___x_483_);
lean_closure_set(v___f_485_, 1, v___x_484_);
v___x_486_ = 1;
v___x_487_ = l_Lean_instBEqMessageSeverity_beq(v_severity_376_, v___x_486_);
if (v___x_487_ == 0)
{
v___y_469_ = v_ref_481_;
v___y_470_ = v_fileName_478_;
v___y_471_ = v_fileMap_479_;
v___y_472_ = v___f_485_;
v___y_473_ = v_suppressElabErrors_482_;
v___y_474_ = v___y_477_;
v___y_475_ = v___x_487_;
goto v___jp_468_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = l_Lean_warningAsError;
v___x_489_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7_spec__11(v_options_480_, v___x_488_);
v___y_469_ = v_ref_481_;
v___y_470_ = v_fileName_478_;
v___y_471_ = v_fileMap_479_;
v___y_472_ = v___f_485_;
v___y_473_ = v_suppressElabErrors_482_;
v___y_474_ = v___y_477_;
v___y_475_ = v___x_489_;
goto v___jp_468_;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v_msgData_375_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg___boxed(lean_object* v_ref_494_, lean_object* v_msgData_495_, lean_object* v_severity_496_, lean_object* v_isSilent_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v_severity_boxed_503_; uint8_t v_isSilent_boxed_504_; lean_object* v_res_505_; 
v_severity_boxed_503_ = lean_unbox(v_severity_496_);
v_isSilent_boxed_504_ = lean_unbox(v_isSilent_497_);
v_res_505_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(v_ref_494_, v_msgData_495_, v_severity_boxed_503_, v_isSilent_boxed_504_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v_ref_494_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(lean_object* v_msgData_506_, uint8_t v_severity_507_, uint8_t v_isSilent_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_ref_518_; lean_object* v___x_519_; 
v_ref_518_ = lean_ctor_get(v___y_515_, 5);
v___x_519_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(v_ref_518_, v_msgData_506_, v_severity_507_, v_isSilent_508_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13___boxed(lean_object* v_msgData_520_, lean_object* v_severity_521_, lean_object* v_isSilent_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v_severity_boxed_532_; uint8_t v_isSilent_boxed_533_; lean_object* v_res_534_; 
v_severity_boxed_532_ = lean_unbox(v_severity_521_);
v_isSilent_boxed_533_ = lean_unbox(v_isSilent_522_);
v_res_534_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(v_msgData_520_, v_severity_boxed_532_, v_isSilent_boxed_533_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
uint8_t v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; 
v___x_545_ = 1;
v___x_546_ = 0;
v___x_547_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13(v_msgData_535_, v___x_545_, v___x_546_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(v_msgData_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__0));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(lean_object* v_id_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_env_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_598_; 
v___x_575_ = lean_st_ref_get(v___y_573_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_578_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(v___x_577_, v___y_572_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_598_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint8_t v_isExporting_588_; 
v_isExporting_588_ = lean_ctor_get_uint8(v_env_576_, sizeof(void*)*8);
lean_dec_ref(v_env_576_);
if (v_isExporting_588_ == 0)
{
lean_dec(v_a_579_);
lean_dec(v_id_565_);
goto v___jp_583_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = l_Lean_isPrivateName(v_id_565_);
if (v___x_589_ == 0)
{
lean_dec(v_a_579_);
lean_dec(v_id_565_);
goto v___jp_583_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v_a_579_);
lean_dec(v_a_579_);
if (v___x_590_ == 0)
{
lean_dec(v_id_565_);
goto v___jp_583_;
}
else
{
lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_581_);
v___x_591_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__1);
v___x_592_ = 0;
v___x_593_ = l_Lean_MessageData_ofConstName(v_id_565_, v___x_592_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___closed__3);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8(v___x_596_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_597_;
}
}
}
v___jp_583_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_box(0);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_id_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_id_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_609_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0(lean_object* v_x_610_){
_start:
{
lean_object* v_fst_611_; uint8_t v___x_612_; 
v_fst_611_ = lean_ctor_get(v_x_610_, 0);
v___x_612_ = l_Lean_isPrivateName(v_fst_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___lam__0(v_x_613_);
lean_dec_ref(v_x_613_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_617_, uint8_t v_enableLog_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_env_629_; lean_object* v_options_630_; lean_object* v_currNamespace_631_; lean_object* v_openDecls_632_; lean_object* v___x_633_; lean_object* v_env_634_; lean_object* v_res_635_; 
v___x_628_ = lean_st_ref_get(v___y_626_);
v_env_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_628_);
v_options_630_ = lean_ctor_get(v___y_625_, 2);
v_currNamespace_631_ = lean_ctor_get(v___y_625_, 6);
v_openDecls_632_ = lean_ctor_get(v___y_625_, 7);
v___x_633_ = lean_st_ref_get(v___y_626_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
lean_inc(v_openDecls_632_);
lean_inc(v_currNamespace_631_);
v_res_635_ = l_Lean_ResolveName_resolveGlobalName(v_env_629_, v_options_630_, v_currNamespace_631_, v_openDecls_632_, v_id_617_);
if (v_enableLog_618_ == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v_env_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_res_635_);
return v___x_636_;
}
else
{
uint8_t v_isExporting_637_; 
v_isExporting_637_ = lean_ctor_get_uint8(v_env_634_, sizeof(void*)*8);
lean_dec_ref(v_env_634_);
if (v_isExporting_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_res_635_);
return v___x_638_;
}
else
{
lean_object* v___f_639_; lean_object* v___x_640_; 
v___f_639_ = ((lean_object*)(l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___closed__0));
lean_inc(v_res_635_);
v___x_640_ = l_List_find_x3f___redArg(v___f_639_, v_res_635_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v_fst_642_; lean_object* v___x_643_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref(v___x_640_);
v_fst_642_ = lean_ctor_get(v_val_641_, 0);
lean_inc(v_fst_642_);
lean_dec(v_val_641_);
v___x_643_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_fst_642_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v___x_643_, 0);
lean_dec(v_unused_651_);
v___x_645_ = v___x_643_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_dec(v___x_643_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_res_635_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_res_635_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_res_635_);
v_a_652_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_643_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_643_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v___x_640_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_res_635_);
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_661_, lean_object* v_enableLog_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v_enableLog_boxed_672_; lean_object* v_res_673_; 
v_enableLog_boxed_672_ = lean_unbox(v_enableLog_662_);
v_res_673_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_661_, v_enableLog_boxed_672_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
if (lean_obj_tag(v_a_674_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_List_reverse___redArg(v_a_675_);
return v___x_676_;
}
else
{
lean_object* v_head_677_; lean_object* v_tail_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
v_head_677_ = lean_ctor_get(v_a_674_, 0);
v_tail_678_ = lean_ctor_get(v_a_674_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_687_ == 0)
{
v___x_680_ = v_a_674_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_tail_678_);
lean_inc(v_head_677_);
lean_dec(v_a_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v___x_684_; 
v_fst_682_ = lean_ctor_get(v_head_677_, 0);
lean_inc(v_fst_682_);
lean_dec(v_head_677_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_a_675_);
lean_ctor_set(v___x_680_, 0, v_fst_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_675_);
v___x_684_ = v_reuseFailAlloc_686_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v_a_674_ = v_tail_678_;
v_a_675_ = v___x_684_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_ref_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_ref_694_ = lean_ctor_get(v___y_691_, 5);
v___x_695_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13_spec__17(v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_inc(v_ref_694_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_ref_694_);
lean_ctor_set(v___x_700_, 1, v_a_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(v_msg_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_fileName_723_; lean_object* v_fileMap_724_; lean_object* v_options_725_; lean_object* v_currRecDepth_726_; lean_object* v_maxRecDepth_727_; lean_object* v_ref_728_; lean_object* v_currNamespace_729_; lean_object* v_openDecls_730_; lean_object* v_initHeartbeats_731_; lean_object* v_maxHeartbeats_732_; lean_object* v_quotContext_733_; lean_object* v_currMacroScope_734_; uint8_t v_diag_735_; lean_object* v_cancelTk_x3f_736_; uint8_t v_suppressElabErrors_737_; lean_object* v_inheritedTraceOptions_738_; lean_object* v_ref_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_fileName_723_ = lean_ctor_get(v___y_720_, 0);
v_fileMap_724_ = lean_ctor_get(v___y_720_, 1);
v_options_725_ = lean_ctor_get(v___y_720_, 2);
v_currRecDepth_726_ = lean_ctor_get(v___y_720_, 3);
v_maxRecDepth_727_ = lean_ctor_get(v___y_720_, 4);
v_ref_728_ = lean_ctor_get(v___y_720_, 5);
v_currNamespace_729_ = lean_ctor_get(v___y_720_, 6);
v_openDecls_730_ = lean_ctor_get(v___y_720_, 7);
v_initHeartbeats_731_ = lean_ctor_get(v___y_720_, 8);
v_maxHeartbeats_732_ = lean_ctor_get(v___y_720_, 9);
v_quotContext_733_ = lean_ctor_get(v___y_720_, 10);
v_currMacroScope_734_ = lean_ctor_get(v___y_720_, 11);
v_diag_735_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*14);
v_cancelTk_x3f_736_ = lean_ctor_get(v___y_720_, 12);
v_suppressElabErrors_737_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_738_ = lean_ctor_get(v___y_720_, 13);
v_ref_739_ = l_Lean_replaceRef(v_ref_712_, v_ref_728_);
lean_inc_ref(v_inheritedTraceOptions_738_);
lean_inc(v_cancelTk_x3f_736_);
lean_inc(v_currMacroScope_734_);
lean_inc(v_quotContext_733_);
lean_inc(v_maxHeartbeats_732_);
lean_inc(v_initHeartbeats_731_);
lean_inc(v_openDecls_730_);
lean_inc(v_currNamespace_729_);
lean_inc(v_maxRecDepth_727_);
lean_inc(v_currRecDepth_726_);
lean_inc_ref(v_options_725_);
lean_inc_ref(v_fileMap_724_);
lean_inc_ref(v_fileName_723_);
v___x_740_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_740_, 0, v_fileName_723_);
lean_ctor_set(v___x_740_, 1, v_fileMap_724_);
lean_ctor_set(v___x_740_, 2, v_options_725_);
lean_ctor_set(v___x_740_, 3, v_currRecDepth_726_);
lean_ctor_set(v___x_740_, 4, v_maxRecDepth_727_);
lean_ctor_set(v___x_740_, 5, v_ref_739_);
lean_ctor_set(v___x_740_, 6, v_currNamespace_729_);
lean_ctor_set(v___x_740_, 7, v_openDecls_730_);
lean_ctor_set(v___x_740_, 8, v_initHeartbeats_731_);
lean_ctor_set(v___x_740_, 9, v_maxHeartbeats_732_);
lean_ctor_set(v___x_740_, 10, v_quotContext_733_);
lean_ctor_set(v___x_740_, 11, v_currMacroScope_734_);
lean_ctor_set(v___x_740_, 12, v_cancelTk_x3f_736_);
lean_ctor_set(v___x_740_, 13, v_inheritedTraceOptions_738_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*14, v_diag_735_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*14 + 1, v_suppressElabErrors_737_);
v___x_741_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(v_msg_713_, v___y_718_, v___y_719_, v___x_740_, v___y_721_);
lean_dec_ref(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_742_, lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_742_, v_msg_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v_ref_742_);
return v_res_753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_754_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__0);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_ctor_set(v___x_759_, 3, v___x_758_);
lean_ctor_set(v___x_759_, 4, v___x_757_);
lean_ctor_set(v___x_759_, 5, v___x_757_);
lean_ctor_set(v___x_759_, 6, v___x_757_);
lean_ctor_set(v___x_759_, 7, v___x_757_);
lean_ctor_set(v___x_759_, 8, v___x_757_);
lean_ctor_set(v___x_759_, 9, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(32u);
v___x_761_ = lean_mk_empty_array_with_capacity(v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4(void){
_start:
{
size_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_763_ = ((size_t)5ULL);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_unsigned_to_nat(32u);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
v___x_767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__3);
v___x_768_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
lean_ctor_set(v___x_768_, 2, v___x_764_);
lean_ctor_set(v___x_768_, 3, v___x_764_);
lean_ctor_set_usize(v___x_768_, 4, v___x_763_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_769_ = lean_box(1);
v___x_770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__4);
v___x_771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__1);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_770_);
lean_ctor_set(v___x_772_, 2, v___x_769_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__6));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__8));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__10));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__12));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__14));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__16));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__18));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(lean_object* v_msg_794_, lean_object* v_declHint_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; lean_object* v_env_799_; uint8_t v___x_800_; 
v___x_798_ = lean_st_ref_get(v___y_796_);
v_env_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc_ref(v_env_799_);
lean_dec(v___x_798_);
v___x_800_ = l_Lean_Name_isAnonymous(v_declHint_795_);
if (v___x_800_ == 0)
{
uint8_t v_isExporting_801_; 
v_isExporting_801_ = lean_ctor_get_uint8(v_env_799_, sizeof(void*)*8);
if (v_isExporting_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v_env_799_);
lean_dec(v_declHint_795_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v_msg_794_);
return v___x_802_;
}
else
{
lean_object* v___x_803_; uint8_t v___x_804_; 
lean_inc_ref(v_env_799_);
v___x_803_ = l_Lean_Environment_setExporting(v_env_799_, v___x_800_);
lean_inc(v_declHint_795_);
lean_inc_ref(v___x_803_);
v___x_804_ = l_Lean_Environment_contains(v___x_803_, v_declHint_795_, v_isExporting_801_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v___x_803_);
lean_dec_ref(v_env_799_);
lean_dec(v_declHint_795_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_msg_794_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_c_811_; lean_object* v___x_812_; 
v___x_806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__2);
v___x_807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__5);
v___x_808_ = l_Lean_Options_empty;
v___x_809_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_809_, 0, v___x_803_);
lean_ctor_set(v___x_809_, 1, v___x_806_);
lean_ctor_set(v___x_809_, 2, v___x_807_);
lean_ctor_set(v___x_809_, 3, v___x_808_);
lean_inc(v_declHint_795_);
v___x_810_ = l_Lean_MessageData_ofConstName(v_declHint_795_, v___x_800_);
v_c_811_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_811_, 0, v___x_809_);
lean_ctor_set(v_c_811_, 1, v___x_810_);
v___x_812_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_799_, v_declHint_795_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_env_799_);
lean_dec(v_declHint_795_);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_c_811_);
v___x_815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__9);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_MessageData_note(v___x_816_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v_msg_794_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_855_; 
v_val_820_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_855_ == 0)
{
v___x_822_ = v___x_812_;
v_isShared_823_ = v_isSharedCheck_855_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v___x_812_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_855_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_mod_827_; uint8_t v___x_828_; 
v___x_824_ = lean_box(0);
v___x_825_ = l_Lean_Environment_header(v_env_799_);
lean_dec_ref(v_env_799_);
v___x_826_ = l_Lean_EnvironmentHeader_moduleNames(v___x_825_);
v_mod_827_ = lean_array_get(v___x_824_, v___x_826_, v_val_820_);
lean_dec(v_val_820_);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Lean_isPrivateName(v_declHint_795_);
lean_dec(v_declHint_795_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__11);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_c_811_);
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__13);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_MessageData_ofName(v_mod_827_);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__15);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Lean_MessageData_note(v___x_836_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v_msg_794_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_838_);
v___x_840_ = v___x_822_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__7);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_c_811_);
v___x_844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__17);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_MessageData_ofName(v_mod_827_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___closed__19);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_MessageData_note(v___x_849_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v_msg_794_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_851_);
v___x_853_ = v___x_822_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_856_; 
lean_dec_ref(v_env_799_);
lean_dec(v_declHint_795_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_msg_794_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg___boxed(lean_object* v_msg_857_, lean_object* v_declHint_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(v_msg_857_, v_declHint_858_, v___y_859_);
lean_dec(v___y_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(lean_object* v_msg_862_, lean_object* v_declHint_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_883_; 
v___x_873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(v_msg_862_, v_declHint_863_, v___y_871_);
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_883_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_883_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_883_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_878_ = l_Lean_unknownIdentifierMessageTag;
v___x_879_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_a_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_879_);
v___x_881_ = v___x_876_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18___boxed(lean_object* v_msg_884_, lean_object* v_declHint_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(v_msg_884_, v_declHint_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_ref_896_, lean_object* v_msg_897_, lean_object* v_declHint_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_910_; 
v___x_908_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18(v_msg_897_, v_declHint_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
v___x_910_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_896_, v_a_909_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_ref_911_, lean_object* v_msg_912_, lean_object* v_declHint_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(v_ref_911_, v_msg_912_, v_declHint_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v_ref_911_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__0));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__2));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(lean_object* v_ref_930_, lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_941_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__1);
v___x_942_ = 0;
lean_inc(v_constName_931_);
v___x_943_ = l_Lean_MessageData_ofConstName(v_constName_931_, v___x_942_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_941_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___closed__3);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(v_ref_930_, v___x_946_, v_constName_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_ref_948_, lean_object* v_constName_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(v_ref_948_, v_constName_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_ref_948_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__7(lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
if (lean_obj_tag(v_a_960_) == 0)
{
lean_object* v___x_962_; 
v___x_962_ = l_List_reverse___redArg(v_a_961_);
return v___x_962_;
}
else
{
lean_object* v_head_963_; lean_object* v_tail_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_975_; 
v_head_963_ = lean_ctor_get(v_a_960_, 0);
v_tail_964_ = lean_ctor_get(v_a_960_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_960_);
if (v_isSharedCheck_975_ == 0)
{
v___x_966_ = v_a_960_;
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_tail_964_);
lean_inc(v_head_963_);
lean_dec(v_a_960_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_snd_968_; uint8_t v___x_969_; 
v_snd_968_ = lean_ctor_get(v_head_963_, 1);
v___x_969_ = l_List_isEmpty___redArg(v_snd_968_);
if (v___x_969_ == 0)
{
lean_del_object(v___x_966_);
lean_dec(v_head_963_);
v_a_960_ = v_tail_964_;
goto _start;
}
else
{
lean_object* v___x_972_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_a_961_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_head_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_a_961_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v_a_960_ = v_tail_964_;
v_a_961_ = v___x_972_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_976_, lean_object* v_cs_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_cs_988_; uint8_t v___x_992_; 
v___x_987_ = lean_box(0);
v_cs_988_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__7(v_cs_977_, v___x_987_);
v___x_992_ = l_List_isEmpty___redArg(v_cs_988_);
if (v___x_992_ == 0)
{
lean_dec(v_n_976_);
goto v___jp_989_;
}
else
{
lean_object* v_ref_993_; lean_object* v___x_994_; lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_cs_988_);
v_ref_993_ = lean_ctor_get(v___y_984_, 5);
v___x_994_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(v_ref_993_, v_n_976_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
v___jp_989_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_988_, v___x_987_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1003_, lean_object* v_cs_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1003_, v_cs_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = 1;
lean_inc(v_n_1015_);
v___x_1026_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1015_, v___x_1025_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1015_, v_a_1027_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1028_;
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_n_1015_);
v_a_1029_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1026_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
if (lean_obj_tag(v_a_1048_) == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_array_to_list(v_a_1049_);
return v___x_1050_;
}
else
{
lean_object* v_head_1051_; 
v_head_1051_ = lean_ctor_get(v_a_1048_, 0);
if (lean_obj_tag(v_head_1051_) == 1)
{
lean_object* v_fields_1052_; 
v_fields_1052_ = lean_ctor_get(v_head_1051_, 1);
if (lean_obj_tag(v_fields_1052_) == 0)
{
lean_object* v_tail_1053_; lean_object* v_n_1054_; lean_object* v___x_1055_; 
lean_inc_ref(v_head_1051_);
v_tail_1053_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_tail_1053_);
lean_dec_ref(v_a_1048_);
v_n_1054_ = lean_ctor_get(v_head_1051_, 0);
lean_inc(v_n_1054_);
lean_dec_ref(v_head_1051_);
v___x_1055_ = lean_array_push(v_a_1049_, v_n_1054_);
v_a_1048_ = v_tail_1053_;
v_a_1049_ = v___x_1055_;
goto _start;
}
else
{
lean_object* v_tail_1057_; 
v_tail_1057_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_tail_1057_);
lean_dec_ref(v_a_1048_);
v_a_1048_ = v_tail_1057_;
goto _start;
}
}
else
{
lean_object* v_tail_1059_; 
v_tail_1059_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_tail_1059_);
lean_dec_ref(v_a_1048_);
v_a_1048_ = v_tail_1059_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1067_ = l_Lean_MessageData_ofFormat(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1068_, lean_object* v_k_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
if (lean_obj_tag(v_stx_1068_) == 3)
{
lean_object* v_val_1079_; lean_object* v_preresolved_1080_; lean_object* v___x_1081_; lean_object* v_pre_1082_; uint8_t v___x_1083_; 
v_val_1079_ = lean_ctor_get(v_stx_1068_, 2);
lean_inc(v_val_1079_);
v_preresolved_1080_ = lean_ctor_get(v_stx_1068_, 3);
v___x_1081_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1080_);
v_pre_1082_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1080_, v___x_1081_);
v___x_1083_ = l_List_isEmpty___redArg(v_pre_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref(v_stx_1068_);
lean_dec(v_val_1079_);
lean_dec_ref(v_k_1069_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_pre_1082_);
return v___x_1084_;
}
else
{
lean_object* v_fileName_1085_; lean_object* v_fileMap_1086_; lean_object* v_options_1087_; lean_object* v_currRecDepth_1088_; lean_object* v_maxRecDepth_1089_; lean_object* v_ref_1090_; lean_object* v_currNamespace_1091_; lean_object* v_openDecls_1092_; lean_object* v_initHeartbeats_1093_; lean_object* v_maxHeartbeats_1094_; lean_object* v_quotContext_1095_; lean_object* v_currMacroScope_1096_; uint8_t v_diag_1097_; lean_object* v_cancelTk_x3f_1098_; uint8_t v_suppressElabErrors_1099_; lean_object* v_inheritedTraceOptions_1100_; lean_object* v_ref_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_pre_1082_);
v_fileName_1085_ = lean_ctor_get(v___y_1076_, 0);
v_fileMap_1086_ = lean_ctor_get(v___y_1076_, 1);
v_options_1087_ = lean_ctor_get(v___y_1076_, 2);
v_currRecDepth_1088_ = lean_ctor_get(v___y_1076_, 3);
v_maxRecDepth_1089_ = lean_ctor_get(v___y_1076_, 4);
v_ref_1090_ = lean_ctor_get(v___y_1076_, 5);
v_currNamespace_1091_ = lean_ctor_get(v___y_1076_, 6);
v_openDecls_1092_ = lean_ctor_get(v___y_1076_, 7);
v_initHeartbeats_1093_ = lean_ctor_get(v___y_1076_, 8);
v_maxHeartbeats_1094_ = lean_ctor_get(v___y_1076_, 9);
v_quotContext_1095_ = lean_ctor_get(v___y_1076_, 10);
v_currMacroScope_1096_ = lean_ctor_get(v___y_1076_, 11);
v_diag_1097_ = lean_ctor_get_uint8(v___y_1076_, sizeof(void*)*14);
v_cancelTk_x3f_1098_ = lean_ctor_get(v___y_1076_, 12);
v_suppressElabErrors_1099_ = lean_ctor_get_uint8(v___y_1076_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1100_ = lean_ctor_get(v___y_1076_, 13);
v_ref_1101_ = l_Lean_replaceRef(v_stx_1068_, v_ref_1090_);
lean_dec_ref(v_stx_1068_);
lean_inc_ref(v_inheritedTraceOptions_1100_);
lean_inc(v_cancelTk_x3f_1098_);
lean_inc(v_currMacroScope_1096_);
lean_inc(v_quotContext_1095_);
lean_inc(v_maxHeartbeats_1094_);
lean_inc(v_initHeartbeats_1093_);
lean_inc(v_openDecls_1092_);
lean_inc(v_currNamespace_1091_);
lean_inc(v_maxRecDepth_1089_);
lean_inc(v_currRecDepth_1088_);
lean_inc_ref(v_options_1087_);
lean_inc_ref(v_fileMap_1086_);
lean_inc_ref(v_fileName_1085_);
v___x_1102_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1102_, 0, v_fileName_1085_);
lean_ctor_set(v___x_1102_, 1, v_fileMap_1086_);
lean_ctor_set(v___x_1102_, 2, v_options_1087_);
lean_ctor_set(v___x_1102_, 3, v_currRecDepth_1088_);
lean_ctor_set(v___x_1102_, 4, v_maxRecDepth_1089_);
lean_ctor_set(v___x_1102_, 5, v_ref_1101_);
lean_ctor_set(v___x_1102_, 6, v_currNamespace_1091_);
lean_ctor_set(v___x_1102_, 7, v_openDecls_1092_);
lean_ctor_set(v___x_1102_, 8, v_initHeartbeats_1093_);
lean_ctor_set(v___x_1102_, 9, v_maxHeartbeats_1094_);
lean_ctor_set(v___x_1102_, 10, v_quotContext_1095_);
lean_ctor_set(v___x_1102_, 11, v_currMacroScope_1096_);
lean_ctor_set(v___x_1102_, 12, v_cancelTk_x3f_1098_);
lean_ctor_set(v___x_1102_, 13, v_inheritedTraceOptions_1100_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*14, v_diag_1097_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*14 + 1, v_suppressElabErrors_1099_);
lean_inc(v___y_1077_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
v___x_1103_ = lean_apply_10(v_k_1069_, v_val_1079_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___x_1102_, v___y_1077_, lean_box(0));
return v___x_1103_;
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_k_1069_);
v___x_1104_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1105_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1068_, v___x_1104_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v_stx_1068_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1106_, lean_object* v_k_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1106_, v_k_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1130_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1119_, v___x_1129_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1142_, size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1145_);
return v___x_1156_;
}
else
{
lean_object* v_a_1157_; lean_object* v_name_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_a_1157_ = lean_array_uget_borrowed(v_as_1142_, v_i_1144_);
v_name_1158_ = lean_ctor_get(v_a_1157_, 0);
lean_inc(v_name_1158_);
v___x_1159_ = lean_mk_syntax_ident(v_name_1158_);
lean_inc(v___x_1159_);
v___x_1160_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1159_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1159_, v_a_1161_, v_b_1145_, v___y_1152_);
lean_dec(v___x_1159_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; size_t v___x_1164_; size_t v___x_1165_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1144_, v___x_1164_);
v_i_1144_ = v___x_1165_;
v_b_1145_ = v_a_1163_;
goto _start;
}
else
{
return v___x_1162_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v___x_1159_);
lean_dec_ref(v_b_1145_);
v_a_1167_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1160_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1160_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1175_, lean_object* v_sz_1176_, lean_object* v_i_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
size_t v_sz_boxed_1188_; size_t v_i_boxed_1189_; lean_object* v_res_1190_; 
v_sz_boxed_1188_ = lean_unbox_usize(v_sz_1176_);
lean_dec(v_sz_1176_);
v_i_boxed_1189_ = lean_unbox_usize(v_i_1177_);
lean_dec(v_i_1177_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1175_, v_sz_boxed_1188_, v_i_boxed_1189_, v_b_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_as_1175_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1210_, lean_object* v_stx_1211_, uint8_t v___x_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v___f_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
if (v___x_1210_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_1226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v_tk_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1299_; lean_object* v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; lean_object* v_stxForSuggestion_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; uint8_t v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; uint8_t v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; uint8_t v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; uint8_t v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; uint8_t v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; uint8_t v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1561_; lean_object* v___y_1562_; uint8_t v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v_stxForExecution_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; uint8_t v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; uint8_t v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; uint8_t v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; uint8_t v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; uint8_t v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; uint8_t v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; uint8_t v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; uint8_t v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; uint8_t v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; uint8_t v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v_argsArray_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; uint8_t v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; uint8_t v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; uint8_t v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v_args_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___x_2024_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; uint8_t v___y_2029_; lean_object* v___y_2030_; lean_object* v_o_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v_bang_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v_tk_1228_ = l_Lean_Syntax_getArg(v_stx_1211_, v___x_1227_);
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2083_ = l_Lean_Syntax_getArg(v_stx_1211_, v___x_2024_);
v___x_2084_ = l_Lean_Syntax_isNone(v___x_2083_);
if (v___x_2084_ == 0)
{
uint8_t v___x_2085_; 
lean_inc(v___x_2083_);
v___x_2085_ = l_Lean_Syntax_matchesNull(v___x_2083_, v___x_2024_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec(v___x_2083_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_2086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2086_;
}
else
{
lean_object* v_bang_2087_; lean_object* v___x_2088_; 
v_bang_2087_ = l_Lean_Syntax_getArg(v___x_2083_, v___x_1227_);
lean_dec(v___x_2083_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_bang_2087_);
v_bang_2055_ = v___x_2088_;
v___y_2056_ = v___y_1217_;
v___y_2057_ = v___y_1218_;
v___y_2058_ = v___y_1219_;
v___y_2059_ = v___y_1220_;
v___y_2060_ = v___y_1221_;
v___y_2061_ = v___y_1222_;
v___y_2062_ = v___y_1223_;
v___y_2063_ = v___y_1224_;
goto v___jp_2054_;
}
}
else
{
lean_object* v___x_2089_; 
lean_dec(v___x_2083_);
v___x_2089_ = lean_box(0);
v_bang_2055_ = v___x_2089_;
v___y_2056_ = v___y_1217_;
v___y_2057_ = v___y_1218_;
v___y_2058_ = v___y_1219_;
v___y_2059_ = v___y_1220_;
v___y_2060_ = v___y_1221_;
v___y_2061_ = v___y_1222_;
v___y_2062_ = v___y_1223_;
v___y_2063_ = v___y_1224_;
goto v___jp_2054_;
}
v___jp_1229_:
{
lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_box(v___x_1212_);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1244_, 0, v___y_1231_);
lean_closure_set(v___f_1244_, 1, v___x_1227_);
lean_closure_set(v___f_1244_, 2, v___x_1243_);
lean_closure_set(v___f_1244_, 3, v___y_1242_);
lean_closure_set(v___f_1244_, 4, v___y_1232_);
v___x_1245_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1230_, v___f_1244_, v___y_1234_, v___y_1240_, v___y_1238_, v___y_1237_, v___y_1236_, v___y_1233_, v___y_1235_, v___y_1239_);
lean_dec(v___y_1230_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_usedTheorems_1247_; lean_object* v_diag_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1289_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v_usedTheorems_1247_ = lean_ctor_get(v_a_1246_, 0);
v_diag_1248_ = lean_ctor_get(v_a_1246_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1250_ = v_a_1246_;
v_isShared_1251_ = v_isSharedCheck_1289_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_diag_1248_);
lean_inc(v_usedTheorems_1247_);
lean_dec(v_a_1246_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1289_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1241_, v_usedTheorems_1247_, v___y_1236_, v___y_1233_, v___y_1235_, v___y_1239_);
lean_dec_ref(v_usedTheorems_1247_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_ref_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1252_);
v_ref_1254_ = lean_ctor_get(v___y_1235_, 5);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_a_1253_);
lean_ctor_set(v___x_1250_, 0, v___x_1255_);
v___x_1257_ = v___x_1250_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_a_1253_);
v___x_1257_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
lean_ctor_set(v___x_1259_, 4, v___x_1258_);
lean_ctor_set(v___x_1259_, 5, v___x_1258_);
lean_inc(v_ref_1254_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_ref_1254_);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1262_ = 4;
v___x_1263_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1228_, v___x_1259_, v___x_1260_, v___x_1261_, v___x_1258_, v___x_1262_, v___y_1235_, v___y_1239_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1263_, 0);
lean_dec(v_unused_1271_);
v___x_1265_ = v___x_1263_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_dec(v___x_1263_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_diag_1248_);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_diag_1248_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_diag_1248_);
v_a_1272_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1263_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1263_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1250_);
lean_dec_ref(v_diag_1248_);
lean_dec(v_tk_1228_);
v_a_1281_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1252_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1252_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___y_1241_);
lean_dec(v_tk_1228_);
v_a_1290_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1245_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1245_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
v___jp_1298_:
{
uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = 0;
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1315_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1300_, v___x_1313_, v___y_1301_, v___x_1313_, v___x_1314_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1300_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1315_);
if (lean_obj_tag(v___y_1302_) == 0)
{
lean_object* v_ctx_1317_; lean_object* v_simprocs_1318_; lean_object* v_dischargeWrapper_1319_; 
v_ctx_1317_ = lean_ctor_get(v_a_1316_, 0);
lean_inc_ref(v_ctx_1317_);
v_simprocs_1318_ = lean_ctor_get(v_a_1316_, 1);
lean_inc_ref(v_simprocs_1318_);
v_dischargeWrapper_1319_ = lean_ctor_get(v_a_1316_, 2);
lean_inc(v_dischargeWrapper_1319_);
lean_dec(v_a_1316_);
v___y_1230_ = v_dischargeWrapper_1319_;
v___y_1231_ = v___y_1299_;
v___y_1232_ = v_simprocs_1318_;
v___y_1233_ = v___y_1310_;
v___y_1234_ = v___y_1305_;
v___y_1235_ = v___y_1311_;
v___y_1236_ = v___y_1309_;
v___y_1237_ = v___y_1308_;
v___y_1238_ = v___y_1307_;
v___y_1239_ = v___y_1312_;
v___y_1240_ = v___y_1306_;
v___y_1241_ = v_stxForSuggestion_1304_;
v___y_1242_ = v_ctx_1317_;
goto v___jp_1229_;
}
else
{
lean_dec_ref(v___y_1302_);
if (v___y_1303_ == 0)
{
lean_object* v_ctx_1320_; lean_object* v_simprocs_1321_; lean_object* v_dischargeWrapper_1322_; 
v_ctx_1320_ = lean_ctor_get(v_a_1316_, 0);
lean_inc_ref(v_ctx_1320_);
v_simprocs_1321_ = lean_ctor_get(v_a_1316_, 1);
lean_inc_ref(v_simprocs_1321_);
v_dischargeWrapper_1322_ = lean_ctor_get(v_a_1316_, 2);
lean_inc(v_dischargeWrapper_1322_);
lean_dec(v_a_1316_);
v___y_1230_ = v_dischargeWrapper_1322_;
v___y_1231_ = v___y_1299_;
v___y_1232_ = v_simprocs_1321_;
v___y_1233_ = v___y_1310_;
v___y_1234_ = v___y_1305_;
v___y_1235_ = v___y_1311_;
v___y_1236_ = v___y_1309_;
v___y_1237_ = v___y_1308_;
v___y_1238_ = v___y_1307_;
v___y_1239_ = v___y_1312_;
v___y_1240_ = v___y_1306_;
v___y_1241_ = v_stxForSuggestion_1304_;
v___y_1242_ = v_ctx_1320_;
goto v___jp_1229_;
}
else
{
lean_object* v_ctx_1323_; lean_object* v_simprocs_1324_; lean_object* v_dischargeWrapper_1325_; lean_object* v___x_1326_; 
v_ctx_1323_ = lean_ctor_get(v_a_1316_, 0);
lean_inc_ref(v_ctx_1323_);
v_simprocs_1324_ = lean_ctor_get(v_a_1316_, 1);
lean_inc_ref(v_simprocs_1324_);
v_dischargeWrapper_1325_ = lean_ctor_get(v_a_1316_, 2);
lean_inc(v_dischargeWrapper_1325_);
lean_dec(v_a_1316_);
v___x_1326_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1323_);
v___y_1230_ = v_dischargeWrapper_1325_;
v___y_1231_ = v___y_1299_;
v___y_1232_ = v_simprocs_1324_;
v___y_1233_ = v___y_1310_;
v___y_1234_ = v___y_1305_;
v___y_1235_ = v___y_1311_;
v___y_1236_ = v___y_1309_;
v___y_1237_ = v___y_1308_;
v___y_1238_ = v___y_1307_;
v___y_1239_ = v___y_1312_;
v___y_1240_ = v___y_1306_;
v___y_1241_ = v_stxForSuggestion_1304_;
v___y_1242_ = v___x_1326_;
goto v___jp_1229_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_stxForSuggestion_1304_);
lean_dec(v___y_1302_);
lean_dec(v___y_1299_);
lean_dec(v_tk_1228_);
v_a_1327_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1315_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1315_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
v___jp_1335_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_inc_ref(v___y_1338_);
v___x_1359_ = l_Array_append___redArg(v___y_1338_, v___y_1358_);
lean_dec_ref(v___y_1358_);
lean_inc(v___y_1341_);
lean_inc(v___y_1353_);
v___x_1360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1360_, 0, v___y_1353_);
lean_ctor_set(v___x_1360_, 1, v___y_1341_);
lean_ctor_set(v___x_1360_, 2, v___x_1359_);
v___x_1361_ = l_Lean_Syntax_node6(v___y_1353_, v___y_1357_, v___y_1342_, v___y_1337_, v___y_1348_, v___y_1345_, v___y_1349_, v___x_1360_);
v___y_1299_ = v___y_1336_;
v___y_1300_ = v___y_1340_;
v___y_1301_ = v___y_1351_;
v___y_1302_ = v___y_1354_;
v___y_1303_ = v___y_1347_;
v_stxForSuggestion_1304_ = v___x_1361_;
v___y_1305_ = v___y_1356_;
v___y_1306_ = v___y_1339_;
v___y_1307_ = v___y_1346_;
v___y_1308_ = v___y_1350_;
v___y_1309_ = v___y_1344_;
v___y_1310_ = v___y_1343_;
v___y_1311_ = v___y_1352_;
v___y_1312_ = v___y_1355_;
goto v___jp_1298_;
}
v___jp_1362_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_inc_ref_n(v___y_1365_, 2);
v___x_1386_ = l_Array_append___redArg(v___y_1365_, v___y_1385_);
lean_dec_ref(v___y_1385_);
lean_inc_n(v___y_1367_, 3);
lean_inc_n(v___y_1379_, 5);
v___x_1387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1379_);
lean_ctor_set(v___x_1387_, 1, v___y_1367_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1379_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1391_ = l_Lean_Syntax_SepArray_ofElems(v___x_1390_, v___y_1383_);
lean_dec_ref(v___y_1383_);
v___x_1392_ = l_Array_append___redArg(v___y_1365_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1379_);
lean_ctor_set(v___x_1393_, 1, v___y_1367_);
lean_ctor_set(v___x_1393_, 2, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___y_1379_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = l_Lean_Syntax_node3(v___y_1379_, v___y_1367_, v___x_1389_, v___x_1393_, v___x_1395_);
if (lean_obj_tag(v___y_1373_) == 1)
{
lean_object* v_val_1397_; lean_object* v___x_1398_; 
v_val_1397_ = lean_ctor_get(v___y_1373_, 0);
lean_inc(v_val_1397_);
lean_dec_ref(v___y_1373_);
v___x_1398_ = l_Array_mkArray1___redArg(v_val_1397_);
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1364_;
v___y_1338_ = v___y_1365_;
v___y_1339_ = v___y_1366_;
v___y_1340_ = v___y_1368_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___y_1371_;
v___y_1345_ = v___x_1387_;
v___y_1346_ = v___y_1372_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___x_1396_;
v___y_1350_ = v___y_1376_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1377_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1380_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___x_1398_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1399_; 
lean_dec(v___y_1373_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1364_;
v___y_1338_ = v___y_1365_;
v___y_1339_ = v___y_1366_;
v___y_1340_ = v___y_1368_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___y_1371_;
v___y_1345_ = v___x_1387_;
v___y_1346_ = v___y_1372_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___x_1396_;
v___y_1350_ = v___y_1376_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1377_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1380_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___x_1399_;
goto v___jp_1335_;
}
}
v___jp_1400_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_inc_ref(v___y_1403_);
v___x_1424_ = l_Array_append___redArg(v___y_1403_, v___y_1423_);
lean_dec_ref(v___y_1423_);
lean_inc(v___y_1405_);
lean_inc(v___y_1417_);
v___x_1425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1425_, 0, v___y_1417_);
lean_ctor_set(v___x_1425_, 1, v___y_1405_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
if (lean_obj_tag(v___y_1413_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_val_1426_ = lean_ctor_get(v___y_1413_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___y_1413_);
v___x_1427_ = l_Lean_SourceInfo_fromRef(v_val_1426_, v___x_1212_);
lean_dec(v_val_1426_);
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Array_mkArray1___redArg(v___x_1429_);
v___y_1363_ = v___y_1401_;
v___y_1364_ = v___y_1402_;
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1409_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___x_1425_;
v___y_1376_ = v___y_1414_;
v___y_1377_ = v___y_1416_;
v___y_1378_ = v___y_1415_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1419_;
v___y_1381_ = v___y_1418_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___x_1430_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1431_; 
lean_dec(v___y_1413_);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1363_ = v___y_1401_;
v___y_1364_ = v___y_1402_;
v___y_1365_ = v___y_1403_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1409_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___x_1425_;
v___y_1376_ = v___y_1414_;
v___y_1377_ = v___y_1416_;
v___y_1378_ = v___y_1415_;
v___y_1379_ = v___y_1417_;
v___y_1380_ = v___y_1419_;
v___y_1381_ = v___y_1418_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___x_1431_;
goto v___jp_1362_;
}
}
v___jp_1432_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_inc_ref(v___y_1445_);
v___x_1456_ = l_Array_append___redArg(v___y_1445_, v___y_1455_);
lean_dec_ref(v___y_1455_);
lean_inc(v___y_1435_);
lean_inc(v___y_1444_);
v___x_1457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1444_);
lean_ctor_set(v___x_1457_, 1, v___y_1435_);
lean_ctor_set(v___x_1457_, 2, v___x_1456_);
v___x_1458_ = l_Lean_Syntax_node6(v___y_1444_, v___y_1440_, v___y_1441_, v___y_1434_, v___y_1446_, v___y_1454_, v___y_1452_, v___x_1457_);
v___y_1299_ = v___y_1433_;
v___y_1300_ = v___y_1437_;
v___y_1301_ = v___y_1448_;
v___y_1302_ = v___y_1450_;
v___y_1303_ = v___y_1443_;
v_stxForSuggestion_1304_ = v___x_1458_;
v___y_1305_ = v___y_1453_;
v___y_1306_ = v___y_1436_;
v___y_1307_ = v___y_1442_;
v___y_1308_ = v___y_1447_;
v___y_1309_ = v___y_1439_;
v___y_1310_ = v___y_1438_;
v___y_1311_ = v___y_1449_;
v___y_1312_ = v___y_1451_;
goto v___jp_1298_;
}
v___jp_1459_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_inc_ref_n(v___y_1473_, 2);
v___x_1483_ = l_Array_append___redArg(v___y_1473_, v___y_1482_);
lean_dec_ref(v___y_1482_);
lean_inc_n(v___y_1462_, 3);
lean_inc_n(v___y_1471_, 5);
v___x_1484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1471_);
lean_ctor_set(v___x_1484_, 1, v___y_1462_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
v___x_1485_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1471_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1488_ = l_Lean_Syntax_SepArray_ofElems(v___x_1487_, v___y_1481_);
lean_dec_ref(v___y_1481_);
v___x_1489_ = l_Array_append___redArg(v___y_1473_, v___x_1488_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1471_);
lean_ctor_set(v___x_1490_, 1, v___y_1462_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1471_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_node3(v___y_1471_, v___y_1462_, v___x_1486_, v___x_1490_, v___x_1492_);
if (lean_obj_tag(v___y_1470_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1495_; 
v_val_1494_ = lean_ctor_get(v___y_1470_, 0);
lean_inc(v_val_1494_);
lean_dec_ref(v___y_1470_);
v___x_1495_ = l_Array_mkArray1___redArg(v_val_1494_);
v___y_1433_ = v___y_1460_;
v___y_1434_ = v___y_1461_;
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___y_1463_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___y_1468_;
v___y_1442_ = v___y_1469_;
v___y_1443_ = v___y_1472_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1477_;
v___y_1449_ = v___y_1476_;
v___y_1450_ = v___y_1479_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___x_1493_;
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___x_1484_;
v___y_1455_ = v___x_1495_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v___y_1470_);
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1433_ = v___y_1460_;
v___y_1434_ = v___y_1461_;
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___y_1463_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___y_1468_;
v___y_1442_ = v___y_1469_;
v___y_1443_ = v___y_1472_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1477_;
v___y_1449_ = v___y_1476_;
v___y_1450_ = v___y_1479_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___x_1493_;
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___x_1484_;
v___y_1455_ = v___x_1496_;
goto v___jp_1432_;
}
}
v___jp_1497_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc_ref(v___y_1511_);
v___x_1521_ = l_Array_append___redArg(v___y_1511_, v___y_1520_);
lean_dec_ref(v___y_1520_);
lean_inc(v___y_1500_);
lean_inc(v___y_1508_);
v___x_1522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1522_, 0, v___y_1508_);
lean_ctor_set(v___x_1522_, 1, v___y_1500_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
if (lean_obj_tag(v___y_1512_) == 1)
{
lean_object* v_val_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_val_1523_ = lean_ctor_get(v___y_1512_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___y_1512_);
v___x_1524_ = l_Lean_SourceInfo_fromRef(v_val_1523_, v___x_1212_);
lean_dec(v_val_1523_);
v___x_1525_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Array_mkArray1___redArg(v___x_1526_);
v___y_1460_ = v___y_1498_;
v___y_1461_ = v___y_1499_;
v___y_1462_ = v___y_1500_;
v___y_1463_ = v___y_1501_;
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___y_1504_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1506_;
v___y_1469_ = v___y_1507_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___y_1508_;
v___y_1472_ = v___y_1510_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___x_1522_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1515_;
v___y_1477_ = v___y_1514_;
v___y_1478_ = v___y_1517_;
v___y_1479_ = v___y_1516_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___x_1527_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1528_; 
lean_dec(v___y_1512_);
v___x_1528_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1460_ = v___y_1498_;
v___y_1461_ = v___y_1499_;
v___y_1462_ = v___y_1500_;
v___y_1463_ = v___y_1501_;
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___y_1504_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1506_;
v___y_1469_ = v___y_1507_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___y_1508_;
v___y_1472_ = v___y_1510_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___x_1522_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1515_;
v___y_1477_ = v___y_1514_;
v___y_1478_ = v___y_1517_;
v___y_1479_ = v___y_1516_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___x_1528_;
goto v___jp_1459_;
}
}
v___jp_1529_:
{
lean_object* v_ref_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_ref_1549_ = lean_ctor_get(v___y_1541_, 5);
v___x_1550_ = l_Lean_SourceInfo_fromRef(v_ref_1549_, v___y_1548_);
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1552_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1551_);
v___x_1553_ = l_Lean_SourceInfo_fromRef(v_tk_1228_, v___x_1212_);
v___x_1554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1551_);
v___x_1555_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1556_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1545_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1558_; 
v_val_1557_ = lean_ctor_get(v___y_1545_, 0);
lean_inc(v_val_1557_);
lean_dec_ref(v___y_1545_);
v___x_1558_ = l_Array_mkArray1___redArg(v_val_1557_);
v___y_1498_ = v___y_1530_;
v___y_1499_ = v___y_1531_;
v___y_1500_ = v___x_1555_;
v___y_1501_ = v___y_1532_;
v___y_1502_ = v___y_1533_;
v___y_1503_ = v___y_1534_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___x_1552_;
v___y_1506_ = v___x_1554_;
v___y_1507_ = v___y_1536_;
v___y_1508_ = v___x_1550_;
v___y_1509_ = v___y_1537_;
v___y_1510_ = v___y_1538_;
v___y_1511_ = v___x_1556_;
v___y_1512_ = v___y_1539_;
v___y_1513_ = v___y_1540_;
v___y_1514_ = v___y_1542_;
v___y_1515_ = v___y_1541_;
v___y_1516_ = v___y_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___y_1546_;
v___y_1519_ = v___y_1547_;
v___y_1520_ = v___x_1558_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1559_; 
lean_dec(v___y_1545_);
v___x_1559_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1498_ = v___y_1530_;
v___y_1499_ = v___y_1531_;
v___y_1500_ = v___x_1555_;
v___y_1501_ = v___y_1532_;
v___y_1502_ = v___y_1533_;
v___y_1503_ = v___y_1534_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___x_1552_;
v___y_1506_ = v___x_1554_;
v___y_1507_ = v___y_1536_;
v___y_1508_ = v___x_1550_;
v___y_1509_ = v___y_1537_;
v___y_1510_ = v___y_1538_;
v___y_1511_ = v___x_1556_;
v___y_1512_ = v___y_1539_;
v___y_1513_ = v___y_1540_;
v___y_1514_ = v___y_1542_;
v___y_1515_ = v___y_1541_;
v___y_1516_ = v___y_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___y_1546_;
v___y_1519_ = v___y_1547_;
v___y_1520_ = v___x_1559_;
goto v___jp_1497_;
}
}
v___jp_1560_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1562_);
if (lean_obj_tag(v___y_1564_) == 0)
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = 0;
v___y_1530_ = v___y_1561_;
v___y_1531_ = v_a_1580_;
v___y_1532_ = v___y_1572_;
v___y_1533_ = v_stxForExecution_1570_;
v___y_1534_ = v___y_1576_;
v___y_1535_ = v___y_1575_;
v___y_1536_ = v___y_1573_;
v___y_1537_ = v___y_1566_;
v___y_1538_ = v___y_1567_;
v___y_1539_ = v___y_1568_;
v___y_1540_ = v___y_1574_;
v___y_1541_ = v___y_1577_;
v___y_1542_ = v___y_1563_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1564_;
v___y_1545_ = v___y_1565_;
v___y_1546_ = v___y_1571_;
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___x_1581_;
goto v___jp_1529_;
}
else
{
if (v___y_1567_ == 0)
{
lean_object* v_a_1582_; 
v_a_1582_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v___x_1579_);
v___y_1530_ = v___y_1561_;
v___y_1531_ = v_a_1582_;
v___y_1532_ = v___y_1572_;
v___y_1533_ = v_stxForExecution_1570_;
v___y_1534_ = v___y_1576_;
v___y_1535_ = v___y_1575_;
v___y_1536_ = v___y_1573_;
v___y_1537_ = v___y_1566_;
v___y_1538_ = v___y_1567_;
v___y_1539_ = v___y_1568_;
v___y_1540_ = v___y_1574_;
v___y_1541_ = v___y_1577_;
v___y_1542_ = v___y_1563_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1564_;
v___y_1545_ = v___y_1565_;
v___y_1546_ = v___y_1571_;
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___y_1567_;
goto v___jp_1529_;
}
else
{
lean_object* v_a_1583_; lean_object* v_ref_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1583_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1579_);
v_ref_1584_ = lean_ctor_get(v___y_1577_, 5);
v___x_1585_ = 0;
v___x_1586_ = l_Lean_SourceInfo_fromRef(v_ref_1584_, v___x_1585_);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1588_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1587_);
v___x_1589_ = l_Lean_SourceInfo_fromRef(v_tk_1228_, v___x_1212_);
v___x_1590_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1593_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1565_) == 1)
{
lean_object* v_val_1594_; lean_object* v___x_1595_; 
v_val_1594_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_val_1594_);
lean_dec_ref(v___y_1565_);
v___x_1595_ = l_Array_mkArray1___redArg(v_val_1594_);
v___y_1401_ = v___y_1561_;
v___y_1402_ = v_a_1583_;
v___y_1403_ = v___x_1593_;
v___y_1404_ = v___y_1572_;
v___y_1405_ = v___x_1592_;
v___y_1406_ = v_stxForExecution_1570_;
v___y_1407_ = v___x_1591_;
v___y_1408_ = v___y_1576_;
v___y_1409_ = v___y_1575_;
v___y_1410_ = v___y_1573_;
v___y_1411_ = v___y_1566_;
v___y_1412_ = v___y_1567_;
v___y_1413_ = v___y_1568_;
v___y_1414_ = v___y_1574_;
v___y_1415_ = v___y_1563_;
v___y_1416_ = v___y_1577_;
v___y_1417_ = v___x_1586_;
v___y_1418_ = v___y_1564_;
v___y_1419_ = v___y_1578_;
v___y_1420_ = v___y_1571_;
v___y_1421_ = v___y_1569_;
v___y_1422_ = v___x_1588_;
v___y_1423_ = v___x_1595_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1596_; 
lean_dec(v___y_1565_);
v___x_1596_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1401_ = v___y_1561_;
v___y_1402_ = v_a_1583_;
v___y_1403_ = v___x_1593_;
v___y_1404_ = v___y_1572_;
v___y_1405_ = v___x_1592_;
v___y_1406_ = v_stxForExecution_1570_;
v___y_1407_ = v___x_1591_;
v___y_1408_ = v___y_1576_;
v___y_1409_ = v___y_1575_;
v___y_1410_ = v___y_1573_;
v___y_1411_ = v___y_1566_;
v___y_1412_ = v___y_1567_;
v___y_1413_ = v___y_1568_;
v___y_1414_ = v___y_1574_;
v___y_1415_ = v___y_1563_;
v___y_1416_ = v___y_1577_;
v___y_1417_ = v___x_1586_;
v___y_1418_ = v___y_1564_;
v___y_1419_ = v___y_1578_;
v___y_1420_ = v___y_1571_;
v___y_1421_ = v___y_1569_;
v___y_1422_ = v___x_1588_;
v___y_1423_ = v___x_1596_;
goto v___jp_1400_;
}
}
}
}
v___jp_1597_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_inc_ref(v___y_1616_);
v___x_1624_ = l_Array_append___redArg(v___y_1616_, v___y_1623_);
lean_dec_ref(v___y_1623_);
lean_inc(v___y_1620_);
lean_inc(v___y_1609_);
v___x_1625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1625_, 0, v___y_1609_);
lean_ctor_set(v___x_1625_, 1, v___y_1620_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
lean_inc(v___y_1599_);
v___x_1626_ = l_Lean_Syntax_node6(v___y_1609_, v___y_1603_, v___y_1605_, v___y_1599_, v___y_1618_, v___y_1614_, v___y_1611_, v___x_1625_);
v___y_1561_ = v___y_1598_;
v___y_1562_ = v___y_1599_;
v___y_1563_ = v___y_1606_;
v___y_1564_ = v___y_1607_;
v___y_1565_ = v___y_1619_;
v___y_1566_ = v___y_1601_;
v___y_1567_ = v___y_1602_;
v___y_1568_ = v___y_1604_;
v___y_1569_ = v___y_1610_;
v_stxForExecution_1570_ = v___x_1626_;
v___y_1571_ = v___y_1612_;
v___y_1572_ = v___y_1613_;
v___y_1573_ = v___y_1621_;
v___y_1574_ = v___y_1615_;
v___y_1575_ = v___y_1617_;
v___y_1576_ = v___y_1608_;
v___y_1577_ = v___y_1622_;
v___y_1578_ = v___y_1600_;
goto v___jp_1560_;
}
v___jp_1627_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_inc_ref_n(v___y_1638_, 2);
v___x_1652_ = l_Array_append___redArg(v___y_1638_, v___y_1651_);
lean_dec_ref(v___y_1651_);
lean_inc_n(v___y_1645_, 3);
lean_inc_n(v___y_1649_, 5);
v___x_1653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1649_);
lean_ctor_set(v___x_1653_, 1, v___y_1645_);
lean_ctor_set(v___x_1653_, 2, v___x_1652_);
v___x_1654_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___y_1649_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1657_ = l_Lean_Syntax_SepArray_ofElems(v___x_1656_, v___y_1650_);
v___x_1658_ = l_Array_append___redArg(v___y_1638_, v___x_1657_);
lean_dec_ref(v___x_1657_);
v___x_1659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___y_1649_);
lean_ctor_set(v___x_1659_, 1, v___y_1645_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1649_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = l_Lean_Syntax_node3(v___y_1649_, v___y_1645_, v___x_1655_, v___x_1659_, v___x_1661_);
if (lean_obj_tag(v___y_1633_) == 1)
{
lean_object* v_val_1663_; lean_object* v___x_1664_; 
v_val_1663_ = lean_ctor_get(v___y_1633_, 0);
lean_inc(v_val_1663_);
v___x_1664_ = l_Array_mkArray1___redArg(v_val_1663_);
v___y_1598_ = v___y_1628_;
v___y_1599_ = v___y_1629_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___y_1639_;
v___y_1606_ = v___y_1641_;
v___y_1607_ = v___y_1642_;
v___y_1608_ = v___y_1646_;
v___y_1609_ = v___y_1649_;
v___y_1610_ = v___y_1650_;
v___y_1611_ = v___x_1662_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1632_;
v___y_1614_ = v___x_1653_;
v___y_1615_ = v___y_1637_;
v___y_1616_ = v___y_1638_;
v___y_1617_ = v___y_1640_;
v___y_1618_ = v___y_1644_;
v___y_1619_ = v___y_1643_;
v___y_1620_ = v___y_1645_;
v___y_1621_ = v___y_1647_;
v___y_1622_ = v___y_1648_;
v___y_1623_ = v___x_1664_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1598_ = v___y_1628_;
v___y_1599_ = v___y_1629_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___y_1639_;
v___y_1606_ = v___y_1641_;
v___y_1607_ = v___y_1642_;
v___y_1608_ = v___y_1646_;
v___y_1609_ = v___y_1649_;
v___y_1610_ = v___y_1650_;
v___y_1611_ = v___x_1662_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1632_;
v___y_1614_ = v___x_1653_;
v___y_1615_ = v___y_1637_;
v___y_1616_ = v___y_1638_;
v___y_1617_ = v___y_1640_;
v___y_1618_ = v___y_1644_;
v___y_1619_ = v___y_1643_;
v___y_1620_ = v___y_1645_;
v___y_1621_ = v___y_1647_;
v___y_1622_ = v___y_1648_;
v___y_1623_ = v___x_1665_;
goto v___jp_1597_;
}
}
v___jp_1666_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_inc_ref(v___y_1676_);
v___x_1690_ = l_Array_append___redArg(v___y_1676_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_inc(v___y_1683_);
lean_inc(v___y_1688_);
v___x_1691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1688_);
lean_ctor_set(v___x_1691_, 1, v___y_1683_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
if (lean_obj_tag(v___y_1675_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_val_1692_ = lean_ctor_get(v___y_1675_, 0);
v___x_1693_ = l_Lean_SourceInfo_fromRef(v_val_1692_, v___x_1212_);
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Array_mkArray1___redArg(v___x_1695_);
v___y_1628_ = v___y_1667_;
v___y_1629_ = v___y_1668_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1677_;
v___y_1638_ = v___y_1676_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1680_;
v___y_1641_ = v___y_1679_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___x_1691_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1687_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1686_;
v___y_1651_ = v___x_1696_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1628_ = v___y_1667_;
v___y_1629_ = v___y_1668_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1677_;
v___y_1638_ = v___y_1676_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1680_;
v___y_1641_ = v___y_1679_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___x_1691_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1684_;
v___y_1647_ = v___y_1685_;
v___y_1648_ = v___y_1687_;
v___y_1649_ = v___y_1688_;
v___y_1650_ = v___y_1686_;
v___y_1651_ = v___x_1697_;
goto v___jp_1627_;
}
}
v___jp_1698_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_inc_ref(v___y_1717_);
v___x_1725_ = l_Array_append___redArg(v___y_1717_, v___y_1724_);
lean_dec_ref(v___y_1724_);
lean_inc(v___y_1712_);
lean_inc(v___y_1706_);
v___x_1726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1706_);
lean_ctor_set(v___x_1726_, 1, v___y_1712_);
lean_ctor_set(v___x_1726_, 2, v___x_1725_);
lean_inc(v___y_1700_);
v___x_1727_ = l_Lean_Syntax_node6(v___y_1706_, v___y_1716_, v___y_1707_, v___y_1700_, v___y_1711_, v___y_1723_, v___y_1702_, v___x_1726_);
v___y_1561_ = v___y_1699_;
v___y_1562_ = v___y_1700_;
v___y_1563_ = v___y_1708_;
v___y_1564_ = v___y_1709_;
v___y_1565_ = v___y_1720_;
v___y_1566_ = v___y_1703_;
v___y_1567_ = v___y_1704_;
v___y_1568_ = v___y_1705_;
v___y_1569_ = v___y_1713_;
v_stxForExecution_1570_ = v___x_1727_;
v___y_1571_ = v___y_1714_;
v___y_1572_ = v___y_1715_;
v___y_1573_ = v___y_1721_;
v___y_1574_ = v___y_1718_;
v___y_1575_ = v___y_1719_;
v___y_1576_ = v___y_1710_;
v___y_1577_ = v___y_1722_;
v___y_1578_ = v___y_1701_;
goto v___jp_1560_;
}
v___jp_1728_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc_ref_n(v___y_1735_, 2);
v___x_1753_ = l_Array_append___redArg(v___y_1735_, v___y_1752_);
lean_dec_ref(v___y_1752_);
lean_inc_n(v___y_1750_, 3);
lean_inc_n(v___y_1740_, 5);
v___x_1754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1754_, 0, v___y_1740_);
lean_ctor_set(v___x_1754_, 1, v___y_1750_);
lean_ctor_set(v___x_1754_, 2, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1740_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1758_ = l_Lean_Syntax_SepArray_ofElems(v___x_1757_, v___y_1751_);
v___x_1759_ = l_Array_append___redArg(v___y_1735_, v___x_1758_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1760_, 0, v___y_1740_);
lean_ctor_set(v___x_1760_, 1, v___y_1750_);
lean_ctor_set(v___x_1760_, 2, v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___y_1740_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_Syntax_node3(v___y_1740_, v___y_1750_, v___x_1756_, v___x_1760_, v___x_1762_);
if (lean_obj_tag(v___y_1736_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1765_; 
v_val_1764_ = lean_ctor_get(v___y_1736_, 0);
lean_inc(v_val_1764_);
v___x_1765_ = l_Array_mkArray1___redArg(v_val_1764_);
v___y_1699_ = v___y_1729_;
v___y_1700_ = v___y_1730_;
v___y_1701_ = v___y_1732_;
v___y_1702_ = v___x_1763_;
v___y_1703_ = v___y_1736_;
v___y_1704_ = v___y_1737_;
v___y_1705_ = v___y_1738_;
v___y_1706_ = v___y_1740_;
v___y_1707_ = v___y_1741_;
v___y_1708_ = v___y_1743_;
v___y_1709_ = v___y_1744_;
v___y_1710_ = v___y_1746_;
v___y_1711_ = v___y_1748_;
v___y_1712_ = v___y_1750_;
v___y_1713_ = v___y_1751_;
v___y_1714_ = v___y_1731_;
v___y_1715_ = v___y_1733_;
v___y_1716_ = v___y_1734_;
v___y_1717_ = v___y_1735_;
v___y_1718_ = v___y_1739_;
v___y_1719_ = v___y_1742_;
v___y_1720_ = v___y_1745_;
v___y_1721_ = v___y_1747_;
v___y_1722_ = v___y_1749_;
v___y_1723_ = v___x_1754_;
v___y_1724_ = v___x_1765_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1766_; 
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1699_ = v___y_1729_;
v___y_1700_ = v___y_1730_;
v___y_1701_ = v___y_1732_;
v___y_1702_ = v___x_1763_;
v___y_1703_ = v___y_1736_;
v___y_1704_ = v___y_1737_;
v___y_1705_ = v___y_1738_;
v___y_1706_ = v___y_1740_;
v___y_1707_ = v___y_1741_;
v___y_1708_ = v___y_1743_;
v___y_1709_ = v___y_1744_;
v___y_1710_ = v___y_1746_;
v___y_1711_ = v___y_1748_;
v___y_1712_ = v___y_1750_;
v___y_1713_ = v___y_1751_;
v___y_1714_ = v___y_1731_;
v___y_1715_ = v___y_1733_;
v___y_1716_ = v___y_1734_;
v___y_1717_ = v___y_1735_;
v___y_1718_ = v___y_1739_;
v___y_1719_ = v___y_1742_;
v___y_1720_ = v___y_1745_;
v___y_1721_ = v___y_1747_;
v___y_1722_ = v___y_1749_;
v___y_1723_ = v___x_1754_;
v___y_1724_ = v___x_1766_;
goto v___jp_1698_;
}
}
v___jp_1767_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_inc_ref(v___y_1773_);
v___x_1791_ = l_Array_append___redArg(v___y_1773_, v___y_1790_);
lean_dec_ref(v___y_1790_);
lean_inc(v___y_1789_);
lean_inc(v___y_1779_);
v___x_1792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1779_);
lean_ctor_set(v___x_1792_, 1, v___y_1789_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
if (lean_obj_tag(v___y_1777_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_val_1793_ = lean_ctor_get(v___y_1777_, 0);
v___x_1794_ = l_Lean_SourceInfo_fromRef(v_val_1793_, v___x_1212_);
v___x_1795_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Array_mkArray1___redArg(v___x_1796_);
v___y_1729_ = v___y_1768_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1770_;
v___y_1732_ = v___y_1771_;
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1774_;
v___y_1735_ = v___y_1773_;
v___y_1736_ = v___y_1775_;
v___y_1737_ = v___y_1776_;
v___y_1738_ = v___y_1777_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1782_;
v___y_1743_ = v___y_1781_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___x_1792_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1787_;
v___y_1752_ = v___x_1797_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1729_ = v___y_1768_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1770_;
v___y_1732_ = v___y_1771_;
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1774_;
v___y_1735_ = v___y_1773_;
v___y_1736_ = v___y_1775_;
v___y_1737_ = v___y_1776_;
v___y_1738_ = v___y_1777_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1782_;
v___y_1743_ = v___y_1781_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1784_;
v___y_1746_ = v___y_1785_;
v___y_1747_ = v___y_1786_;
v___y_1748_ = v___x_1792_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1789_;
v___y_1751_ = v___y_1787_;
v___y_1752_ = v___x_1798_;
goto v___jp_1728_;
}
}
v___jp_1799_:
{
lean_object* v_ref_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_ref_1818_ = lean_ctor_get(v___y_1816_, 5);
v___x_1819_ = l_Lean_SourceInfo_fromRef(v_ref_1818_, v___y_1817_);
v___x_1820_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_1821_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1820_);
v___x_1822_ = l_Lean_SourceInfo_fromRef(v_tk_1228_, v___x_1212_);
v___x_1823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1820_);
v___x_1824_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1825_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1812_) == 1)
{
lean_object* v_val_1826_; lean_object* v___x_1827_; 
v_val_1826_ = lean_ctor_get(v___y_1812_, 0);
lean_inc(v_val_1826_);
v___x_1827_ = l_Array_mkArray1___redArg(v_val_1826_);
v___y_1768_ = v___y_1800_;
v___y_1769_ = v___y_1801_;
v___y_1770_ = v___y_1802_;
v___y_1771_ = v___y_1803_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___x_1825_;
v___y_1774_ = v___x_1821_;
v___y_1775_ = v___y_1805_;
v___y_1776_ = v___y_1806_;
v___y_1777_ = v___y_1807_;
v___y_1778_ = v___y_1808_;
v___y_1779_ = v___x_1819_;
v___y_1780_ = v___x_1823_;
v___y_1781_ = v___y_1809_;
v___y_1782_ = v___y_1810_;
v___y_1783_ = v___y_1811_;
v___y_1784_ = v___y_1812_;
v___y_1785_ = v___y_1813_;
v___y_1786_ = v___y_1814_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1816_;
v___y_1789_ = v___x_1824_;
v___y_1790_ = v___x_1827_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1828_; 
v___x_1828_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1768_ = v___y_1800_;
v___y_1769_ = v___y_1801_;
v___y_1770_ = v___y_1802_;
v___y_1771_ = v___y_1803_;
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___x_1825_;
v___y_1774_ = v___x_1821_;
v___y_1775_ = v___y_1805_;
v___y_1776_ = v___y_1806_;
v___y_1777_ = v___y_1807_;
v___y_1778_ = v___y_1808_;
v___y_1779_ = v___x_1819_;
v___y_1780_ = v___x_1823_;
v___y_1781_ = v___y_1809_;
v___y_1782_ = v___y_1810_;
v___y_1783_ = v___y_1811_;
v___y_1784_ = v___y_1812_;
v___y_1785_ = v___y_1813_;
v___y_1786_ = v___y_1814_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1816_;
v___y_1789_ = v___x_1824_;
v___y_1790_ = v___x_1828_;
goto v___jp_1767_;
}
}
v___jp_1829_:
{
if (lean_obj_tag(v___y_1833_) == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = 0;
v___y_1800_ = v___y_1830_;
v___y_1801_ = v___y_1831_;
v___y_1802_ = v___y_1839_;
v___y_1803_ = v___y_1846_;
v___y_1804_ = v___y_1840_;
v___y_1805_ = v___y_1836_;
v___y_1806_ = v___y_1835_;
v___y_1807_ = v___y_1837_;
v___y_1808_ = v___y_1842_;
v___y_1809_ = v___y_1832_;
v___y_1810_ = v___y_1843_;
v___y_1811_ = v___y_1833_;
v___y_1812_ = v___y_1834_;
v___y_1813_ = v___y_1844_;
v___y_1814_ = v___y_1841_;
v___y_1815_ = v_argsArray_1838_;
v___y_1816_ = v___y_1845_;
v___y_1817_ = v___x_1847_;
goto v___jp_1799_;
}
else
{
if (v___y_1835_ == 0)
{
v___y_1800_ = v___y_1830_;
v___y_1801_ = v___y_1831_;
v___y_1802_ = v___y_1839_;
v___y_1803_ = v___y_1846_;
v___y_1804_ = v___y_1840_;
v___y_1805_ = v___y_1836_;
v___y_1806_ = v___y_1835_;
v___y_1807_ = v___y_1837_;
v___y_1808_ = v___y_1842_;
v___y_1809_ = v___y_1832_;
v___y_1810_ = v___y_1843_;
v___y_1811_ = v___y_1833_;
v___y_1812_ = v___y_1834_;
v___y_1813_ = v___y_1844_;
v___y_1814_ = v___y_1841_;
v___y_1815_ = v_argsArray_1838_;
v___y_1816_ = v___y_1845_;
v___y_1817_ = v___y_1835_;
goto v___jp_1799_;
}
else
{
lean_object* v_ref_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_ref_1848_ = lean_ctor_get(v___y_1845_, 5);
v___x_1849_ = 0;
v___x_1850_ = l_Lean_SourceInfo_fromRef(v_ref_1848_, v___x_1849_);
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_1852_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1851_);
v___x_1853_ = l_Lean_SourceInfo_fromRef(v_tk_1228_, v___x_1212_);
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1857_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1834_) == 1)
{
lean_object* v_val_1858_; lean_object* v___x_1859_; 
v_val_1858_ = lean_ctor_get(v___y_1834_, 0);
lean_inc(v_val_1858_);
v___x_1859_ = l_Array_mkArray1___redArg(v_val_1858_);
v___y_1667_ = v___y_1830_;
v___y_1668_ = v___y_1831_;
v___y_1669_ = v___y_1839_;
v___y_1670_ = v___y_1846_;
v___y_1671_ = v___y_1840_;
v___y_1672_ = v___y_1836_;
v___y_1673_ = v___y_1835_;
v___y_1674_ = v___x_1852_;
v___y_1675_ = v___y_1837_;
v___y_1676_ = v___x_1857_;
v___y_1677_ = v___y_1842_;
v___y_1678_ = v___x_1855_;
v___y_1679_ = v___y_1832_;
v___y_1680_ = v___y_1843_;
v___y_1681_ = v___y_1833_;
v___y_1682_ = v___y_1834_;
v___y_1683_ = v___x_1856_;
v___y_1684_ = v___y_1844_;
v___y_1685_ = v___y_1841_;
v___y_1686_ = v_argsArray_1838_;
v___y_1687_ = v___y_1845_;
v___y_1688_ = v___x_1850_;
v___y_1689_ = v___x_1859_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1667_ = v___y_1830_;
v___y_1668_ = v___y_1831_;
v___y_1669_ = v___y_1839_;
v___y_1670_ = v___y_1846_;
v___y_1671_ = v___y_1840_;
v___y_1672_ = v___y_1836_;
v___y_1673_ = v___y_1835_;
v___y_1674_ = v___x_1852_;
v___y_1675_ = v___y_1837_;
v___y_1676_ = v___x_1857_;
v___y_1677_ = v___y_1842_;
v___y_1678_ = v___x_1855_;
v___y_1679_ = v___y_1832_;
v___y_1680_ = v___y_1843_;
v___y_1681_ = v___y_1833_;
v___y_1682_ = v___y_1834_;
v___y_1683_ = v___x_1856_;
v___y_1684_ = v___y_1844_;
v___y_1685_ = v___y_1841_;
v___y_1686_ = v_argsArray_1838_;
v___y_1687_ = v___y_1845_;
v___y_1688_ = v___x_1850_;
v___y_1689_ = v___x_1860_;
goto v___jp_1666_;
}
}
}
}
v___jp_1861_:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1875_, v___y_1876_, v___y_1864_, v___y_1865_, v___y_1878_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_LibrarySuggestions_select(v_a_1881_, v___y_1879_, v___y_1876_, v___y_1864_, v___y_1865_, v___y_1878_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; size_t v_sz_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v_sz_1884_ = lean_array_size(v_a_1883_);
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1883_, v_sz_1884_, v___x_1885_, v___y_1870_, v___y_1866_, v___y_1875_, v___y_1877_, v___y_1871_, v___y_1876_, v___y_1864_, v___y_1865_, v___y_1878_);
lean_dec(v_a_1883_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
v___y_1830_ = v___y_1862_;
v___y_1831_ = v___y_1863_;
v___y_1832_ = v___y_1872_;
v___y_1833_ = v___y_1873_;
v___y_1834_ = v___y_1874_;
v___y_1835_ = v___y_1868_;
v___y_1836_ = v___y_1867_;
v___y_1837_ = v___y_1869_;
v_argsArray_1838_ = v_a_1887_;
v___y_1839_ = v___y_1866_;
v___y_1840_ = v___y_1875_;
v___y_1841_ = v___y_1877_;
v___y_1842_ = v___y_1871_;
v___y_1843_ = v___y_1876_;
v___y_1844_ = v___y_1864_;
v___y_1845_ = v___y_1865_;
v___y_1846_ = v___y_1878_;
goto v___jp_1829_;
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1869_);
lean_dec(v___y_1867_);
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v_a_1888_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1867_);
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v_a_1896_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1882_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1882_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1867_);
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v_a_1904_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1880_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1880_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
v___jp_1912_:
{
uint8_t v_suggestions_1931_; 
v_suggestions_1931_ = lean_ctor_get_uint8(v___y_1928_, sizeof(void*)*3 + 26);
if (v_suggestions_1931_ == 0)
{
lean_dec_ref(v___y_1928_);
lean_dec_ref(v___f_1216_);
v___y_1830_ = v___y_1913_;
v___y_1831_ = v___y_1914_;
v___y_1832_ = v___y_1922_;
v___y_1833_ = v___y_1923_;
v___y_1834_ = v___y_1925_;
v___y_1835_ = v___y_1919_;
v___y_1836_ = v___y_1918_;
v___y_1837_ = v___y_1920_;
v_argsArray_1838_ = v___y_1930_;
v___y_1839_ = v___y_1917_;
v___y_1840_ = v___y_1926_;
v___y_1841_ = v___y_1927_;
v___y_1842_ = v___y_1921_;
v___y_1843_ = v___y_1924_;
v___y_1844_ = v___y_1915_;
v___y_1845_ = v___y_1916_;
v___y_1846_ = v___y_1929_;
goto v___jp_1829_;
}
else
{
lean_object* v_maxSuggestions_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_maxSuggestions_1932_ = lean_ctor_get(v___y_1928_, 2);
lean_inc(v_maxSuggestions_1932_);
lean_dec_ref(v___y_1928_);
v___x_1933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1934_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1932_) == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(100u);
v___x_1936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___x_1933_);
lean_ctor_set(v___x_1936_, 2, v___f_1216_);
lean_ctor_set(v___x_1936_, 3, v___x_1934_);
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1914_;
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1917_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1919_;
v___y_1869_ = v___y_1920_;
v___y_1870_ = v___y_1930_;
v___y_1871_ = v___y_1921_;
v___y_1872_ = v___y_1922_;
v___y_1873_ = v___y_1923_;
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1924_;
v___y_1877_ = v___y_1927_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___x_1936_;
goto v___jp_1861_;
}
else
{
lean_object* v_val_1937_; lean_object* v___x_1938_; 
v_val_1937_ = lean_ctor_get(v_maxSuggestions_1932_, 0);
lean_inc(v_val_1937_);
lean_dec_ref(v_maxSuggestions_1932_);
v___x_1938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1938_, 0, v_val_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1933_);
lean_ctor_set(v___x_1938_, 2, v___f_1216_);
lean_ctor_set(v___x_1938_, 3, v___x_1934_);
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1914_;
v___y_1864_ = v___y_1915_;
v___y_1865_ = v___y_1916_;
v___y_1866_ = v___y_1917_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1919_;
v___y_1869_ = v___y_1920_;
v___y_1870_ = v___y_1930_;
v___y_1871_ = v___y_1921_;
v___y_1872_ = v___y_1922_;
v___y_1873_ = v___y_1923_;
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1924_;
v___y_1877_ = v___y_1927_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___x_1938_;
goto v___jp_1861_;
}
}
}
v___jp_1939_:
{
uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = 0;
lean_inc(v___y_1951_);
v___x_1956_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1951_, v___x_1955_, v___y_1941_, v___y_1949_, v___y_1944_, v___y_1953_, v___y_1945_, v___y_1947_, v___y_1946_);
if (lean_obj_tag(v___x_1956_) == 0)
{
if (lean_obj_tag(v___y_1942_) == 1)
{
lean_object* v_a_1957_; lean_object* v_val_1958_; lean_object* v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
v_val_1958_ = lean_ctor_get(v___y_1942_, 0);
lean_inc(v_val_1958_);
lean_dec_ref(v___y_1942_);
v___x_1959_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1958_);
lean_dec(v_val_1958_);
lean_inc(v___y_1952_);
v___y_1913_ = v___y_1952_;
v___y_1914_ = v___y_1951_;
v___y_1915_ = v___y_1945_;
v___y_1916_ = v___y_1947_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1952_;
v___y_1919_ = v___y_1950_;
v___y_1920_ = v___y_1943_;
v___y_1921_ = v___y_1944_;
v___y_1922_ = v___x_1955_;
v___y_1923_ = v___y_1940_;
v___y_1924_ = v___y_1953_;
v___y_1925_ = v___y_1954_;
v___y_1926_ = v___y_1948_;
v___y_1927_ = v___y_1949_;
v___y_1928_ = v_a_1957_;
v___y_1929_ = v___y_1946_;
v___y_1930_ = v___x_1959_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
lean_dec(v___y_1942_);
v_a_1960_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1956_);
v___x_1961_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1952_);
v___y_1913_ = v___y_1952_;
v___y_1914_ = v___y_1951_;
v___y_1915_ = v___y_1945_;
v___y_1916_ = v___y_1947_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1952_;
v___y_1919_ = v___y_1950_;
v___y_1920_ = v___y_1943_;
v___y_1921_ = v___y_1944_;
v___y_1922_ = v___x_1955_;
v___y_1923_ = v___y_1940_;
v___y_1924_ = v___y_1953_;
v___y_1925_ = v___y_1954_;
v___y_1926_ = v___y_1948_;
v___y_1927_ = v___y_1949_;
v___y_1928_ = v_a_1960_;
v___y_1929_ = v___y_1946_;
v___y_1930_ = v___x_1961_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___y_1954_);
lean_dec(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec(v___y_1940_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v_a_1962_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1956_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1956_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
v___jp_1970_:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Syntax_getOptional_x3f(v___y_1972_);
lean_dec(v___y_1972_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
v___y_1940_ = v___y_1980_;
v___y_1941_ = v___y_1975_;
v___y_1942_ = v___y_1978_;
v___y_1943_ = v___y_1977_;
v___y_1944_ = v___y_1979_;
v___y_1945_ = v___y_1973_;
v___y_1946_ = v___y_1984_;
v___y_1947_ = v___y_1974_;
v___y_1948_ = v___y_1981_;
v___y_1949_ = v___y_1983_;
v___y_1950_ = v___y_1976_;
v___y_1951_ = v___y_1971_;
v___y_1952_ = v___y_1985_;
v___y_1953_ = v___y_1982_;
v___y_1954_ = v___x_1987_;
goto v___jp_1939_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_val_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_val_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
v___y_1940_ = v___y_1980_;
v___y_1941_ = v___y_1975_;
v___y_1942_ = v___y_1978_;
v___y_1943_ = v___y_1977_;
v___y_1944_ = v___y_1979_;
v___y_1945_ = v___y_1973_;
v___y_1946_ = v___y_1984_;
v___y_1947_ = v___y_1974_;
v___y_1948_ = v___y_1981_;
v___y_1949_ = v___y_1983_;
v___y_1950_ = v___y_1976_;
v___y_1951_ = v___y_1971_;
v___y_1952_ = v___y_1985_;
v___y_1953_ = v___y_1982_;
v___y_1954_ = v___x_1993_;
goto v___jp_1939_;
}
}
}
}
v___jp_1996_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_unsigned_to_nat(4u);
v___x_2013_ = l_Lean_Syntax_getArg(v___y_2002_, v___x_2012_);
lean_dec(v___y_2002_);
v___x_2014_ = l_Lean_Syntax_getOptional_x3f(v___x_2013_);
lean_dec(v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_box(0);
v___y_1971_ = v___y_1997_;
v___y_1972_ = v___y_1998_;
v___y_1973_ = v___y_2009_;
v___y_1974_ = v___y_2010_;
v___y_1975_ = v___y_2004_;
v___y_1976_ = v___y_2000_;
v___y_1977_ = v___y_2001_;
v___y_1978_ = v_args_2003_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2005_;
v___y_1982_ = v___y_2008_;
v___y_1983_ = v___y_2006_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___x_2015_;
goto v___jp_1970_;
}
else
{
lean_object* v_val_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_val_2016_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2014_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_val_2016_);
lean_dec(v___x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_val_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
v___y_1971_ = v___y_1997_;
v___y_1972_ = v___y_1998_;
v___y_1973_ = v___y_2009_;
v___y_1974_ = v___y_2010_;
v___y_1975_ = v___y_2004_;
v___y_1976_ = v___y_2000_;
v___y_1977_ = v___y_2001_;
v___y_1978_ = v_args_2003_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2005_;
v___y_1982_ = v___y_2008_;
v___y_1983_ = v___y_2006_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___x_2021_;
goto v___jp_1970_;
}
}
}
}
v___jp_2025_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2040_ = lean_unsigned_to_nat(3u);
v___x_2041_ = l_Lean_Syntax_getArg(v___y_2030_, v___x_2040_);
v___x_2042_ = l_Lean_Syntax_isNone(v___x_2041_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; 
lean_inc(v___x_2041_);
v___x_2043_ = l_Lean_Syntax_matchesNull(v___x_2041_, v___x_2024_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v___x_2041_);
lean_dec(v_o_2031_);
lean_dec(v___y_2030_);
lean_dec(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_2044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2045_ = l_Lean_Syntax_getArg(v___x_2041_, v___x_1227_);
lean_dec(v___x_2041_);
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_2047_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_2046_);
lean_inc(v___x_2045_);
v___x_2048_ = l_Lean_Syntax_isOfKind(v___x_2045_, v___x_2047_);
lean_dec(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v___x_2045_);
lean_dec(v_o_2031_);
lean_dec(v___y_2030_);
lean_dec(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_2049_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v_args_2051_; lean_object* v___x_2052_; 
v___x_2050_ = l_Lean_Syntax_getArg(v___x_2045_, v___x_2024_);
lean_dec(v___x_2045_);
v_args_2051_ = l_Lean_Syntax_getArgs(v___x_2050_);
lean_dec(v___x_2050_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_args_2051_);
v___y_1997_ = v___y_2026_;
v___y_1998_ = v___y_2027_;
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v_o_2031_;
v___y_2002_ = v___y_2030_;
v_args_2003_ = v___x_2052_;
v___y_2004_ = v___y_2032_;
v___y_2005_ = v___y_2033_;
v___y_2006_ = v___y_2034_;
v___y_2007_ = v___y_2035_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
goto v___jp_1996_;
}
}
}
else
{
lean_object* v___x_2053_; 
lean_dec(v___x_2041_);
v___x_2053_ = lean_box(0);
v___y_1997_ = v___y_2026_;
v___y_1998_ = v___y_2027_;
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v_o_2031_;
v___y_2002_ = v___y_2030_;
v_args_2003_ = v___x_2053_;
v___y_2004_ = v___y_2032_;
v___y_2005_ = v___y_2033_;
v___y_2006_ = v___y_2034_;
v___y_2007_ = v___y_2035_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
goto v___jp_1996_;
}
}
v___jp_2054_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2064_ = lean_unsigned_to_nat(2u);
v___x_2065_ = l_Lean_Syntax_getArg(v_stx_1211_, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_2067_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_2066_);
lean_inc(v___x_2065_);
v___x_2068_ = l_Lean_Syntax_isOfKind(v___x_2065_, v___x_2067_);
lean_dec(v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec(v___x_2065_);
lean_dec(v_bang_2055_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_2069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2069_;
}
else
{
lean_object* v_cfg_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_cfg_2070_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_1227_);
v___x_2071_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_2072_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_2071_);
lean_inc(v_cfg_2070_);
v___x_2073_ = l_Lean_Syntax_isOfKind(v_cfg_2070_, v___x_2072_);
lean_dec(v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_dec(v_cfg_2070_);
lean_dec(v___x_2065_);
lean_dec(v_bang_2055_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_2074_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_2024_);
v___x_2076_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_2064_);
v___x_2077_ = l_Lean_Syntax_isNone(v___x_2076_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; 
lean_inc(v___x_2076_);
v___x_2078_ = l_Lean_Syntax_matchesNull(v___x_2076_, v___x_2024_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_dec(v___x_2076_);
lean_dec(v___x_2075_);
lean_dec(v_cfg_2070_);
lean_dec(v___x_2065_);
lean_dec(v_bang_2055_);
lean_dec(v_tk_1228_);
lean_dec_ref(v___f_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
v___x_2079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2079_;
}
else
{
lean_object* v_o_2080_; lean_object* v___x_2081_; 
v_o_2080_ = l_Lean_Syntax_getArg(v___x_2076_, v___x_1227_);
lean_dec(v___x_2076_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_o_2080_);
v___y_2026_ = v_cfg_2070_;
v___y_2027_ = v___x_2075_;
v___y_2028_ = v_bang_2055_;
v___y_2029_ = v___x_2073_;
v___y_2030_ = v___x_2065_;
v_o_2031_ = v___x_2081_;
v___y_2032_ = v___y_2056_;
v___y_2033_ = v___y_2057_;
v___y_2034_ = v___y_2058_;
v___y_2035_ = v___y_2059_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
goto v___jp_2025_;
}
}
else
{
lean_object* v___x_2082_; 
lean_dec(v___x_2076_);
v___x_2082_ = lean_box(0);
v___y_2026_ = v_cfg_2070_;
v___y_2027_ = v___x_2075_;
v___y_2028_ = v_bang_2055_;
v___y_2029_ = v___x_2073_;
v___y_2030_ = v___x_2065_;
v_o_2031_ = v___x_2082_;
v___y_2032_ = v___y_2056_;
v___y_2033_ = v___y_2057_;
v___y_2034_ = v___y_2058_;
v___y_2035_ = v___y_2059_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
goto v___jp_2025_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2090_, lean_object* v_stx_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v___f_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_40397__boxed_2106_; uint8_t v___x_40398__boxed_2107_; lean_object* v_res_2108_; 
v___x_40397__boxed_2106_ = lean_unbox(v___x_2090_);
v___x_40398__boxed_2107_ = lean_unbox(v___x_2092_);
v_res_2108_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_40397__boxed_2106_, v_stx_2091_, v___x_40398__boxed_2107_, v___x_2093_, v___x_2094_, v___x_2095_, v___f_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v_stx_2091_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___y_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2131_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2118_);
v___x_2132_ = l_Lean_Syntax_isOfKind(v_stx_2118_, v___x_2131_);
v___x_2133_ = 1;
v___f_2134_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2135_ = lean_box(v___x_2132_);
v___x_2136_ = lean_box(v___x_2133_);
v___y_2137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2137_, 0, v___x_2135_);
lean_closure_set(v___y_2137_, 1, v_stx_2118_);
lean_closure_set(v___y_2137_, 2, v___x_2136_);
lean_closure_set(v___y_2137_, 3, v___x_2128_);
lean_closure_set(v___y_2137_, 4, v___x_2129_);
lean_closure_set(v___y_2137_, 5, v___x_2130_);
lean_closure_set(v___y_2137_, 6, v___f_2134_);
v___x_2138_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2138_, 0, v___y_2137_);
v___x_2139_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2138_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2151_, lean_object* v_as_2152_, lean_object* v_as_x27_2153_, lean_object* v_b_2154_, lean_object* v_a_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2151_, v_as_x27_2153_, v_b_2154_, v___y_2162_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2166_, lean_object* v_as_2167_, lean_object* v_as_x27_2168_, lean_object* v_b_2169_, lean_object* v_a_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2166_, v_as_2167_, v_as_x27_2168_, v_b_2169_, v_a_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v_as_2167_);
lean_dec(v___x_2166_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2181_, lean_object* v_ref_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2182_, v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2194_, lean_object* v_ref_2195_, lean_object* v_msg_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2194_, v_ref_2195_, v_msg_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v_ref_2195_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b1_2207_, lean_object* v_ref_2208_, lean_object* v_constName_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___redArg(v_ref_2208_, v_constName_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b1_2220_, lean_object* v_ref_2221_, lean_object* v_constName_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_00_u03b1_2220_, v_ref_2221_, v_constName_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v_ref_2221_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b1_2233_, lean_object* v_msg_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___redArg(v_msg_2234_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__13(v_00_u03b1_2245_, v_msg_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7(lean_object* v_opt_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___redArg(v_opt_2257_, v___y_2264_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_opt_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__7(v_opt_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_opt_2268_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b1_2279_, lean_object* v_ref_2280_, lean_object* v_msg_2281_, lean_object* v_declHint_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___redArg(v_ref_2280_, v_msg_2281_, v_declHint_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_ref_2294_, lean_object* v_msg_2295_, lean_object* v_declHint_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13(v_00_u03b1_2293_, v_ref_2294_, v_msg_2295_, v_declHint_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v_ref_2294_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22(lean_object* v_msg_2307_, lean_object* v_declHint_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___redArg(v_msg_2307_, v_declHint_2308_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22___boxed(lean_object* v_msg_2319_, lean_object* v_declHint_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9_spec__13_spec__18_spec__22(v_msg_2319_, v_declHint_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19(lean_object* v_ref_2331_, lean_object* v_msgData_2332_, uint8_t v_severity_2333_, uint8_t v_isSilent_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___redArg(v_ref_2331_, v_msgData_2332_, v_severity_2333_, v_isSilent_2334_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19___boxed(lean_object* v_ref_2345_, lean_object* v_msgData_2346_, lean_object* v_severity_2347_, lean_object* v_isSilent_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_severity_boxed_2358_; uint8_t v_isSilent_boxed_2359_; lean_object* v_res_2360_; 
v_severity_boxed_2358_ = lean_unbox(v_severity_2347_);
v_isSilent_boxed_2359_ = lean_unbox(v_isSilent_2348_);
v_res_2360_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5_spec__8_spec__13_spec__19(v_ref_2345_, v_msgData_2346_, v_severity_boxed_2358_, v_isSilent_boxed_2359_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v_ref_2345_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2368_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2369_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2371_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2372_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2368_, v___x_2369_, v___x_2370_, v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2403_ = l_Lean_addBuiltinDeclarationRanges(v___x_2401_, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2406_, lean_object* v_as_x27_2407_, lean_object* v_b_2408_, lean_object* v___y_2409_){
_start:
{
if (lean_obj_tag(v_as_x27_2407_) == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_b_2408_);
return v___x_2411_;
}
else
{
lean_object* v_head_2412_; lean_object* v_tail_2413_; lean_object* v_ref_2414_; uint8_t v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_head_2412_ = lean_ctor_get(v_as_x27_2407_, 0);
lean_inc(v_head_2412_);
v_tail_2413_ = lean_ctor_get(v_as_x27_2407_, 1);
lean_inc(v_tail_2413_);
lean_dec_ref(v_as_x27_2407_);
v_ref_2414_ = lean_ctor_get(v___y_2409_, 5);
v___x_2415_ = 1;
v___x_2416_ = 0;
v___x_2417_ = l_Lean_SourceInfo_fromRef(v_ref_2414_, v___x_2416_);
v___x_2418_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2419_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2420_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2417_);
v___x_2421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2417_);
lean_ctor_set(v___x_2421_, 1, v___x_2419_);
lean_ctor_set(v___x_2421_, 2, v___x_2420_);
v___x_2422_ = l_Lean_mkCIdentFrom(v___x_2406_, v_head_2412_, v___x_2415_);
lean_inc_ref(v___x_2421_);
v___x_2423_ = l_Lean_Syntax_node3(v___x_2417_, v___x_2418_, v___x_2421_, v___x_2421_, v___x_2422_);
v___x_2424_ = lean_array_push(v_b_2408_, v___x_2423_);
v_as_x27_2407_ = v_tail_2413_;
v_b_2408_ = v___x_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2426_, lean_object* v_as_x27_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2426_, v_as_x27_2427_, v_b_2428_, v___y_2429_);
lean_dec_ref(v___y_2429_);
lean_dec(v___x_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2432_, size_t v_sz_2433_, size_t v_i_2434_, lean_object* v_b_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_lt(v_i_2434_, v_sz_2433_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_b_2435_);
return v___x_2446_;
}
else
{
lean_object* v_a_2447_; lean_object* v_name_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_a_2447_ = lean_array_uget_borrowed(v_as_2432_, v_i_2434_);
v_name_2448_ = lean_ctor_get(v_a_2447_, 0);
lean_inc(v_name_2448_);
v___x_2449_ = lean_mk_syntax_ident(v_name_2448_);
lean_inc(v___x_2449_);
v___x_2450_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2449_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2452_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v___x_2452_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2449_, v_a_2451_, v_b_2435_, v___y_2442_);
lean_dec(v___x_2449_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; size_t v___x_2454_; size_t v___x_2455_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2434_, v___x_2454_);
v_i_2434_ = v___x_2455_;
v_b_2435_ = v_a_2453_;
goto _start;
}
else
{
return v___x_2452_;
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v___x_2449_);
lean_dec_ref(v_b_2435_);
v_a_2457_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2450_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2450_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2465_, lean_object* v_sz_2466_, lean_object* v_i_2467_, lean_object* v_b_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
size_t v_sz_boxed_2478_; size_t v_i_boxed_2479_; lean_object* v_res_2480_; 
v_sz_boxed_2478_ = lean_unbox_usize(v_sz_2466_);
lean_dec(v_sz_2466_);
v_i_boxed_2479_ = lean_unbox_usize(v_i_2467_);
lean_dec(v_i_2467_);
v_res_2480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2465_, v_sz_boxed_2478_, v_i_boxed_2479_, v_b_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec_ref(v_as_2465_);
return v_res_2480_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_unsigned_to_nat(32u);
v___x_2488_ = lean_mk_empty_array_with_capacity(v___x_2487_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2490_ = ((size_t)5ULL);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_unsigned_to_nat(32u);
v___x_2493_ = lean_mk_empty_array_with_capacity(v___x_2492_);
v___x_2494_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2495_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2493_);
lean_ctor_set(v___x_2495_, 2, v___x_2491_);
lean_ctor_set(v___x_2495_, 3, v___x_2491_);
lean_ctor_set_usize(v___x_2495_, 4, v___x_2490_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2497_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
lean_ctor_set(v___x_2498_, 2, v___x_2497_);
lean_ctor_set(v___x_2498_, 3, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2510_, lean_object* v_stx_2511_, uint8_t v___x_2512_, lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v___x_2515_, lean_object* v___f_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
if (v___x_2510_ == 0)
{
lean_object* v___x_2526_; 
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_2526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2526_;
}
else
{
lean_object* v___x_2527_; lean_object* v_tk_2528_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; lean_object* v_stxForSuggestion_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; uint8_t v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; uint8_t v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; uint8_t v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; uint8_t v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; uint8_t v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; uint8_t v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint8_t v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; uint8_t v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; uint8_t v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; uint8_t v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; uint8_t v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; uint8_t v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; uint8_t v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; uint8_t v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint8_t v___y_2925_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; uint8_t v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; uint8_t v___y_2955_; uint8_t v___y_2956_; lean_object* v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; uint8_t v___y_2988_; lean_object* v_stxForExecution_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; uint8_t v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; uint8_t v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; uint8_t v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; uint8_t v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; uint8_t v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; uint8_t v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; uint8_t v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3332_; uint8_t v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v_argsArray_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; uint8_t v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; lean_object* v_args_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___x_3492_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v_o_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v_bang_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v___x_2527_ = lean_unsigned_to_nat(0u);
v_tk_2528_ = l_Lean_Syntax_getArg(v_stx_2511_, v___x_2527_);
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3551_ = l_Lean_Syntax_getArg(v_stx_2511_, v___x_3492_);
v___x_3552_ = l_Lean_Syntax_isNone(v___x_3551_);
if (v___x_3552_ == 0)
{
uint8_t v___x_3553_; 
lean_inc(v___x_3551_);
v___x_3553_ = l_Lean_Syntax_matchesNull(v___x_3551_, v___x_3492_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_dec(v___x_3551_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_3554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3554_;
}
else
{
lean_object* v_bang_3555_; lean_object* v___x_3556_; 
v_bang_3555_ = l_Lean_Syntax_getArg(v___x_3551_, v___x_2527_);
lean_dec(v___x_3551_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_bang_3555_);
v_bang_3523_ = v___x_3556_;
v___y_3524_ = v___y_2517_;
v___y_3525_ = v___y_2518_;
v___y_3526_ = v___y_2519_;
v___y_3527_ = v___y_2520_;
v___y_3528_ = v___y_2521_;
v___y_3529_ = v___y_2522_;
v___y_3530_ = v___y_2523_;
v___y_3531_ = v___y_2524_;
goto v___jp_3522_;
}
}
else
{
lean_object* v___x_3557_; 
lean_dec(v___x_3551_);
v___x_3557_ = lean_box(0);
v_bang_3523_ = v___x_3557_;
v___y_3524_ = v___y_2517_;
v___y_3525_ = v___y_2518_;
v___y_3526_ = v___y_2519_;
v___y_3527_ = v___y_2520_;
v___y_3528_ = v___y_2521_;
v___y_3529_ = v___y_2522_;
v___y_3530_ = v___y_2523_;
v___y_3531_ = v___y_2524_;
goto v___jp_3522_;
}
v___jp_2529_:
{
lean_object* v_usedTheorems_2536_; lean_object* v_diag_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2578_; 
v_usedTheorems_2536_ = lean_ctor_get(v___y_2530_, 0);
v_diag_2537_ = lean_ctor_get(v___y_2530_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___y_2530_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2539_ = v___y_2530_;
v_isShared_2540_ = v_isSharedCheck_2578_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_diag_2537_);
lean_inc(v_usedTheorems_2536_);
lean_dec(v___y_2530_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2578_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2531_, v_usedTheorems_2536_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec_ref(v_usedTheorems_2536_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v_ref_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2541_);
v_ref_2543_ = lean_ctor_get(v___y_2534_, 5);
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v_a_2542_);
lean_ctor_set(v___x_2539_, 0, v___x_2544_);
v___x_2546_ = v___x_2539_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_a_2542_);
v___x_2546_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
lean_ctor_set(v___x_2548_, 2, v___x_2547_);
lean_ctor_set(v___x_2548_, 3, v___x_2547_);
lean_ctor_set(v___x_2548_, 4, v___x_2547_);
lean_ctor_set(v___x_2548_, 5, v___x_2547_);
lean_inc(v_ref_2543_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_ref_2543_);
v___x_2550_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2551_ = 4;
v___x_2552_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2528_, v___x_2548_, v___x_2549_, v___x_2550_, v___x_2547_, v___x_2551_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2552_, 0);
lean_dec(v_unused_2560_);
v___x_2554_ = v___x_2552_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v___x_2552_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_diag_2537_);
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_diag_2537_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec_ref(v_diag_2537_);
v_a_2561_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2552_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2552_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_del_object(v___x_2539_);
lean_dec_ref(v_diag_2537_);
lean_dec(v_tk_2528_);
v_a_2570_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2541_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2541_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
v___jp_2579_:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2580_, v___y_2584_, v___y_2586_, v___y_2582_, v___y_2581_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2591_ = l_Lean_Meta_simpAll(v_a_2589_, v___y_2587_, v___y_2583_, v___x_2590_, v___y_2584_, v___y_2586_, v___y_2582_, v___y_2581_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_fst_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
v_fst_2593_ = lean_ctor_get(v_a_2592_, 0);
if (lean_obj_tag(v_fst_2593_) == 0)
{
lean_object* v_snd_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_snd_2594_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2594_);
lean_dec(v_a_2592_);
v___x_2595_ = lean_box(0);
v___x_2596_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2595_, v___y_2580_, v___y_2584_, v___y_2586_, v___y_2582_, v___y_2581_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_dec_ref(v___x_2596_);
v___y_2530_ = v_snd_2594_;
v___y_2531_ = v___y_2585_;
v___y_2532_ = v___y_2584_;
v___y_2533_ = v___y_2586_;
v___y_2534_ = v___y_2582_;
v___y_2535_ = v___y_2581_;
goto v___jp_2529_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_snd_2594_);
lean_dec(v___y_2585_);
lean_dec(v_tk_2528_);
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_snd_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2623_; 
lean_inc_ref(v_fst_2593_);
v_snd_2605_ = lean_ctor_get(v_a_2592_, 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_a_2592_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v_a_2592_, 0);
lean_dec(v_unused_2624_);
v___x_2607_ = v_a_2592_;
v_isShared_2608_ = v_isSharedCheck_2623_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_snd_2605_);
lean_dec(v_a_2592_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2623_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_val_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v_val_2609_ = lean_ctor_get(v_fst_2593_, 0);
lean_inc(v_val_2609_);
lean_dec_ref(v_fst_2593_);
v___x_2610_ = lean_box(0);
if (v_isShared_2608_ == 0)
{
lean_ctor_set_tag(v___x_2607_, 1);
lean_ctor_set(v___x_2607_, 1, v___x_2610_);
lean_ctor_set(v___x_2607_, 0, v_val_2609_);
v___x_2612_ = v___x_2607_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_val_2609_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2612_, v___y_2580_, v___y_2584_, v___y_2586_, v___y_2582_, v___y_2581_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_dec_ref(v___x_2613_);
v___y_2530_ = v_snd_2605_;
v___y_2531_ = v___y_2585_;
v___y_2532_ = v___y_2584_;
v___y_2533_ = v___y_2586_;
v___y_2534_ = v___y_2582_;
v___y_2535_ = v___y_2581_;
goto v___jp_2529_;
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_snd_2605_);
lean_dec(v___y_2585_);
lean_dec(v_tk_2528_);
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v___y_2585_);
lean_dec(v_tk_2528_);
v_a_2625_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2591_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2591_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2583_);
lean_dec(v_tk_2528_);
v_a_2633_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2588_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2588_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
v___jp_2641_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2656_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2642_, v___x_2512_, v___y_2643_, v___x_2512_, v___x_2655_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2642_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
if (lean_obj_tag(v___y_2644_) == 0)
{
lean_object* v_ctx_2658_; lean_object* v_simprocs_2659_; 
v_ctx_2658_ = lean_ctor_get(v_a_2657_, 0);
lean_inc_ref(v_ctx_2658_);
v_simprocs_2659_ = lean_ctor_get(v_a_2657_, 1);
lean_inc_ref(v_simprocs_2659_);
lean_dec(v_a_2657_);
v___y_2580_ = v___y_2648_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2653_;
v___y_2583_ = v_simprocs_2659_;
v___y_2584_ = v___y_2651_;
v___y_2585_ = v_stxForSuggestion_2646_;
v___y_2586_ = v___y_2652_;
v___y_2587_ = v_ctx_2658_;
goto v___jp_2579_;
}
else
{
lean_dec_ref(v___y_2644_);
if (v___y_2645_ == 0)
{
lean_object* v_ctx_2660_; lean_object* v_simprocs_2661_; 
v_ctx_2660_ = lean_ctor_get(v_a_2657_, 0);
lean_inc_ref(v_ctx_2660_);
v_simprocs_2661_ = lean_ctor_get(v_a_2657_, 1);
lean_inc_ref(v_simprocs_2661_);
lean_dec(v_a_2657_);
v___y_2580_ = v___y_2648_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2653_;
v___y_2583_ = v_simprocs_2661_;
v___y_2584_ = v___y_2651_;
v___y_2585_ = v_stxForSuggestion_2646_;
v___y_2586_ = v___y_2652_;
v___y_2587_ = v_ctx_2660_;
goto v___jp_2579_;
}
else
{
lean_object* v_ctx_2662_; lean_object* v_simprocs_2663_; lean_object* v___x_2664_; 
v_ctx_2662_ = lean_ctor_get(v_a_2657_, 0);
lean_inc_ref(v_ctx_2662_);
v_simprocs_2663_ = lean_ctor_get(v_a_2657_, 1);
lean_inc_ref(v_simprocs_2663_);
lean_dec(v_a_2657_);
v___x_2664_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2662_);
v___y_2580_ = v___y_2648_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2653_;
v___y_2583_ = v_simprocs_2663_;
v___y_2584_ = v___y_2651_;
v___y_2585_ = v_stxForSuggestion_2646_;
v___y_2586_ = v___y_2652_;
v___y_2587_ = v___x_2664_;
goto v___jp_2579_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_stxForSuggestion_2646_);
lean_dec(v___y_2644_);
lean_dec(v_tk_2528_);
v_a_2665_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2656_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2656_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
v___jp_2673_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_inc_ref_n(v___y_2676_, 2);
v___x_2694_ = l_Array_append___redArg(v___y_2676_, v___y_2693_);
lean_dec_ref(v___y_2693_);
lean_inc_n(v___y_2692_, 2);
lean_inc_n(v___y_2681_, 2);
v___x_2695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2681_);
lean_ctor_set(v___x_2695_, 1, v___y_2692_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2696_, 0, v___y_2681_);
lean_ctor_set(v___x_2696_, 1, v___y_2692_);
lean_ctor_set(v___x_2696_, 2, v___y_2676_);
v___x_2697_ = l_Lean_Syntax_node5(v___y_2681_, v___y_2680_, v___y_2683_, v___y_2686_, v___y_2691_, v___x_2695_, v___x_2696_);
v___y_2642_ = v___y_2677_;
v___y_2643_ = v___y_2688_;
v___y_2644_ = v___y_2684_;
v___y_2645_ = v___y_2685_;
v_stxForSuggestion_2646_ = v___x_2697_;
v___y_2647_ = v___y_2674_;
v___y_2648_ = v___y_2678_;
v___y_2649_ = v___y_2675_;
v___y_2650_ = v___y_2690_;
v___y_2651_ = v___y_2682_;
v___y_2652_ = v___y_2689_;
v___y_2653_ = v___y_2679_;
v___y_2654_ = v___y_2687_;
goto v___jp_2641_;
}
v___jp_2698_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_inc_ref(v___y_2701_);
v___x_2719_ = l_Array_append___redArg(v___y_2701_, v___y_2718_);
lean_dec_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc(v___y_2706_);
v___x_2720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___y_2706_);
lean_ctor_set(v___x_2720_, 1, v___y_2717_);
lean_ctor_set(v___x_2720_, 2, v___x_2719_);
if (lean_obj_tag(v___y_2715_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_val_2721_ = lean_ctor_get(v___y_2715_, 0);
lean_inc(v_val_2721_);
lean_dec_ref(v___y_2715_);
v___x_2722_ = l_Lean_SourceInfo_fromRef(v_val_2721_, v___x_2512_);
lean_dec(v_val_2721_);
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = l_Array_mkArray1___redArg(v___x_2724_);
v___y_2674_ = v___y_2699_;
v___y_2675_ = v___y_2700_;
v___y_2676_ = v___y_2701_;
v___y_2677_ = v___y_2702_;
v___y_2678_ = v___y_2703_;
v___y_2679_ = v___y_2704_;
v___y_2680_ = v___y_2705_;
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___y_2708_;
v___y_2684_ = v___y_2709_;
v___y_2685_ = v___y_2710_;
v___y_2686_ = v___y_2711_;
v___y_2687_ = v___y_2712_;
v___y_2688_ = v___y_2714_;
v___y_2689_ = v___y_2713_;
v___y_2690_ = v___y_2716_;
v___y_2691_ = v___x_2720_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___x_2725_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2726_; 
lean_dec(v___y_2715_);
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2674_ = v___y_2699_;
v___y_2675_ = v___y_2700_;
v___y_2676_ = v___y_2701_;
v___y_2677_ = v___y_2702_;
v___y_2678_ = v___y_2703_;
v___y_2679_ = v___y_2704_;
v___y_2680_ = v___y_2705_;
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___y_2708_;
v___y_2684_ = v___y_2709_;
v___y_2685_ = v___y_2710_;
v___y_2686_ = v___y_2711_;
v___y_2687_ = v___y_2712_;
v___y_2688_ = v___y_2714_;
v___y_2689_ = v___y_2713_;
v___y_2690_ = v___y_2716_;
v___y_2691_ = v___x_2720_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___x_2726_;
goto v___jp_2673_;
}
}
v___jp_2727_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_inc_ref_n(v___y_2747_, 2);
v___x_2749_ = l_Array_append___redArg(v___y_2747_, v___y_2748_);
lean_dec_ref(v___y_2748_);
lean_inc_n(v___y_2732_, 3);
lean_inc_n(v___y_2734_, 5);
v___x_2750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2734_);
lean_ctor_set(v___x_2750_, 1, v___y_2732_);
lean_ctor_set(v___x_2750_, 2, v___x_2749_);
v___x_2751_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___y_2734_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2754_ = l_Lean_Syntax_SepArray_ofElems(v___x_2753_, v___y_2744_);
lean_dec_ref(v___y_2744_);
v___x_2755_ = l_Array_append___redArg(v___y_2747_, v___x_2754_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___y_2734_);
lean_ctor_set(v___x_2756_, 1, v___y_2732_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
v___x_2757_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___y_2734_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_Lean_Syntax_node3(v___y_2734_, v___y_2732_, v___x_2752_, v___x_2756_, v___x_2758_);
v___x_2760_ = l_Lean_Syntax_node5(v___y_2734_, v___y_2741_, v___y_2745_, v___y_2739_, v___y_2735_, v___x_2750_, v___x_2759_);
v___y_2642_ = v___y_2730_;
v___y_2643_ = v___y_2742_;
v___y_2644_ = v___y_2737_;
v___y_2645_ = v___y_2738_;
v_stxForSuggestion_2646_ = v___x_2760_;
v___y_2647_ = v___y_2728_;
v___y_2648_ = v___y_2731_;
v___y_2649_ = v___y_2729_;
v___y_2650_ = v___y_2746_;
v___y_2651_ = v___y_2736_;
v___y_2652_ = v___y_2743_;
v___y_2653_ = v___y_2733_;
v___y_2654_ = v___y_2740_;
goto v___jp_2641_;
}
v___jp_2761_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_inc_ref(v___y_2781_);
v___x_2783_ = l_Array_append___redArg(v___y_2781_, v___y_2782_);
lean_dec_ref(v___y_2782_);
lean_inc(v___y_2766_);
lean_inc(v___y_2768_);
v___x_2784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2784_, 0, v___y_2768_);
lean_ctor_set(v___x_2784_, 1, v___y_2766_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
if (lean_obj_tag(v___y_2779_) == 1)
{
lean_object* v_val_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_val_2785_ = lean_ctor_get(v___y_2779_, 0);
lean_inc(v_val_2785_);
lean_dec_ref(v___y_2779_);
v___x_2786_ = l_Lean_SourceInfo_fromRef(v_val_2785_, v___x_2512_);
lean_dec(v_val_2785_);
v___x_2787_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = l_Array_mkArray1___redArg(v___x_2788_);
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___x_2784_;
v___y_2736_ = v___y_2769_;
v___y_2737_ = v___y_2770_;
v___y_2738_ = v___y_2771_;
v___y_2739_ = v___y_2772_;
v___y_2740_ = v___y_2773_;
v___y_2741_ = v___y_2774_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2776_;
v___y_2744_ = v___y_2775_;
v___y_2745_ = v___y_2778_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___x_2789_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2790_; 
lean_dec(v___y_2779_);
v___x_2790_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2763_;
v___y_2730_ = v___y_2764_;
v___y_2731_ = v___y_2765_;
v___y_2732_ = v___y_2766_;
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___x_2784_;
v___y_2736_ = v___y_2769_;
v___y_2737_ = v___y_2770_;
v___y_2738_ = v___y_2771_;
v___y_2739_ = v___y_2772_;
v___y_2740_ = v___y_2773_;
v___y_2741_ = v___y_2774_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2776_;
v___y_2744_ = v___y_2775_;
v___y_2745_ = v___y_2778_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___x_2790_;
goto v___jp_2727_;
}
}
v___jp_2791_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_inc_ref_n(v___y_2798_, 2);
v___x_2813_ = l_Array_append___redArg(v___y_2798_, v___y_2812_);
lean_dec_ref(v___y_2812_);
lean_inc_n(v___y_2806_, 3);
lean_inc_n(v___y_2803_, 5);
v___x_2814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2814_, 0, v___y_2803_);
lean_ctor_set(v___x_2814_, 1, v___y_2806_);
lean_ctor_set(v___x_2814_, 2, v___x_2813_);
v___x_2815_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___y_2803_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2818_ = l_Lean_Syntax_SepArray_ofElems(v___x_2817_, v___y_2809_);
lean_dec_ref(v___y_2809_);
v___x_2819_ = l_Array_append___redArg(v___y_2798_, v___x_2818_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2820_, 0, v___y_2803_);
lean_ctor_set(v___x_2820_, 1, v___y_2806_);
lean_ctor_set(v___x_2820_, 2, v___x_2819_);
v___x_2821_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___y_2803_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_Syntax_node3(v___y_2803_, v___y_2806_, v___x_2816_, v___x_2820_, v___x_2822_);
v___x_2824_ = l_Lean_Syntax_node5(v___y_2803_, v___y_2799_, v___y_2811_, v___y_2804_, v___y_2792_, v___x_2814_, v___x_2823_);
v___y_2642_ = v___y_2795_;
v___y_2643_ = v___y_2807_;
v___y_2644_ = v___y_2801_;
v___y_2645_ = v___y_2802_;
v_stxForSuggestion_2646_ = v___x_2824_;
v___y_2647_ = v___y_2793_;
v___y_2648_ = v___y_2796_;
v___y_2649_ = v___y_2794_;
v___y_2650_ = v___y_2810_;
v___y_2651_ = v___y_2800_;
v___y_2652_ = v___y_2808_;
v___y_2653_ = v___y_2797_;
v___y_2654_ = v___y_2805_;
goto v___jp_2641_;
}
v___jp_2825_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_inc_ref(v___y_2831_);
v___x_2847_ = l_Array_append___redArg(v___y_2831_, v___y_2846_);
lean_dec_ref(v___y_2846_);
lean_inc(v___y_2839_);
lean_inc(v___y_2836_);
v___x_2848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2848_, 0, v___y_2836_);
lean_ctor_set(v___x_2848_, 1, v___y_2839_);
lean_ctor_set(v___x_2848_, 2, v___x_2847_);
if (lean_obj_tag(v___y_2843_) == 1)
{
lean_object* v_val_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_val_2849_ = lean_ctor_get(v___y_2843_, 0);
lean_inc(v_val_2849_);
lean_dec_ref(v___y_2843_);
v___x_2850_ = l_Lean_SourceInfo_fromRef(v_val_2849_, v___x_2512_);
lean_dec(v_val_2849_);
v___x_2851_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = l_Array_mkArray1___redArg(v___x_2852_);
v___y_2792_ = v___x_2848_;
v___y_2793_ = v___y_2826_;
v___y_2794_ = v___y_2827_;
v___y_2795_ = v___y_2828_;
v___y_2796_ = v___y_2829_;
v___y_2797_ = v___y_2830_;
v___y_2798_ = v___y_2831_;
v___y_2799_ = v___y_2832_;
v___y_2800_ = v___y_2833_;
v___y_2801_ = v___y_2834_;
v___y_2802_ = v___y_2835_;
v___y_2803_ = v___y_2836_;
v___y_2804_ = v___y_2837_;
v___y_2805_ = v___y_2838_;
v___y_2806_ = v___y_2839_;
v___y_2807_ = v___y_2842_;
v___y_2808_ = v___y_2841_;
v___y_2809_ = v___y_2840_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2845_;
v___y_2812_ = v___x_2853_;
goto v___jp_2791_;
}
else
{
lean_object* v___x_2854_; 
lean_dec(v___y_2843_);
v___x_2854_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2792_ = v___x_2848_;
v___y_2793_ = v___y_2826_;
v___y_2794_ = v___y_2827_;
v___y_2795_ = v___y_2828_;
v___y_2796_ = v___y_2829_;
v___y_2797_ = v___y_2830_;
v___y_2798_ = v___y_2831_;
v___y_2799_ = v___y_2832_;
v___y_2800_ = v___y_2833_;
v___y_2801_ = v___y_2834_;
v___y_2802_ = v___y_2835_;
v___y_2803_ = v___y_2836_;
v___y_2804_ = v___y_2837_;
v___y_2805_ = v___y_2838_;
v___y_2806_ = v___y_2839_;
v___y_2807_ = v___y_2842_;
v___y_2808_ = v___y_2841_;
v___y_2809_ = v___y_2840_;
v___y_2810_ = v___y_2844_;
v___y_2811_ = v___y_2845_;
v___y_2812_ = v___x_2854_;
goto v___jp_2791_;
}
}
v___jp_2855_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_inc_ref_n(v___y_2866_, 2);
v___x_2876_ = l_Array_append___redArg(v___y_2866_, v___y_2875_);
lean_dec_ref(v___y_2875_);
lean_inc_n(v___y_2861_, 2);
lean_inc_n(v___y_2873_, 2);
v___x_2877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2877_, 0, v___y_2873_);
lean_ctor_set(v___x_2877_, 1, v___y_2861_);
lean_ctor_set(v___x_2877_, 2, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2878_, 0, v___y_2873_);
lean_ctor_set(v___x_2878_, 1, v___y_2861_);
lean_ctor_set(v___x_2878_, 2, v___y_2866_);
v___x_2879_ = l_Lean_Syntax_node5(v___y_2873_, v___y_2864_, v___y_2863_, v___y_2869_, v___y_2856_, v___x_2877_, v___x_2878_);
v___y_2642_ = v___y_2859_;
v___y_2643_ = v___y_2871_;
v___y_2644_ = v___y_2867_;
v___y_2645_ = v___y_2868_;
v_stxForSuggestion_2646_ = v___x_2879_;
v___y_2647_ = v___y_2857_;
v___y_2648_ = v___y_2860_;
v___y_2649_ = v___y_2858_;
v___y_2650_ = v___y_2874_;
v___y_2651_ = v___y_2865_;
v___y_2652_ = v___y_2872_;
v___y_2653_ = v___y_2862_;
v___y_2654_ = v___y_2870_;
goto v___jp_2641_;
}
v___jp_2880_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_inc_ref(v___y_2890_);
v___x_2901_ = l_Array_append___redArg(v___y_2890_, v___y_2900_);
lean_dec_ref(v___y_2900_);
lean_inc(v___y_2885_);
lean_inc(v___y_2897_);
v___x_2902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2902_, 0, v___y_2897_);
lean_ctor_set(v___x_2902_, 1, v___y_2885_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
if (lean_obj_tag(v___y_2898_) == 1)
{
lean_object* v_val_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_val_2903_ = lean_ctor_get(v___y_2898_, 0);
lean_inc(v_val_2903_);
lean_dec_ref(v___y_2898_);
v___x_2904_ = l_Lean_SourceInfo_fromRef(v_val_2903_, v___x_2512_);
lean_dec(v_val_2903_);
v___x_2905_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Array_mkArray1___redArg(v___x_2906_);
v___y_2856_ = v___x_2902_;
v___y_2857_ = v___y_2881_;
v___y_2858_ = v___y_2882_;
v___y_2859_ = v___y_2883_;
v___y_2860_ = v___y_2884_;
v___y_2861_ = v___y_2885_;
v___y_2862_ = v___y_2886_;
v___y_2863_ = v___y_2887_;
v___y_2864_ = v___y_2888_;
v___y_2865_ = v___y_2889_;
v___y_2866_ = v___y_2890_;
v___y_2867_ = v___y_2891_;
v___y_2868_ = v___y_2892_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2894_;
v___y_2871_ = v___y_2896_;
v___y_2872_ = v___y_2895_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2899_;
v___y_2875_ = v___x_2907_;
goto v___jp_2855_;
}
else
{
lean_object* v___x_2908_; 
lean_dec(v___y_2898_);
v___x_2908_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2856_ = v___x_2902_;
v___y_2857_ = v___y_2881_;
v___y_2858_ = v___y_2882_;
v___y_2859_ = v___y_2883_;
v___y_2860_ = v___y_2884_;
v___y_2861_ = v___y_2885_;
v___y_2862_ = v___y_2886_;
v___y_2863_ = v___y_2887_;
v___y_2864_ = v___y_2888_;
v___y_2865_ = v___y_2889_;
v___y_2866_ = v___y_2890_;
v___y_2867_ = v___y_2891_;
v___y_2868_ = v___y_2892_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2894_;
v___y_2871_ = v___y_2896_;
v___y_2872_ = v___y_2895_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2899_;
v___y_2875_ = v___x_2908_;
goto v___jp_2855_;
}
}
v___jp_2909_:
{
lean_object* v_ref_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_ref_2926_ = lean_ctor_get(v___y_2915_, 5);
v___x_2927_ = l_Lean_SourceInfo_fromRef(v_ref_2926_, v___y_2925_);
v___x_2928_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2929_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_2928_);
v___x_2930_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_2931_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2934_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2914_) == 1)
{
lean_object* v_val_2935_; lean_object* v___x_2936_; 
v_val_2935_ = lean_ctor_get(v___y_2914_, 0);
lean_inc(v_val_2935_);
lean_dec_ref(v___y_2914_);
v___x_2936_ = l_Array_mkArray1___redArg(v_val_2935_);
v___y_2699_ = v___y_2910_;
v___y_2700_ = v___y_2911_;
v___y_2701_ = v___x_2934_;
v___y_2702_ = v___y_2912_;
v___y_2703_ = v___y_2913_;
v___y_2704_ = v___y_2915_;
v___y_2705_ = v___x_2929_;
v___y_2706_ = v___x_2927_;
v___y_2707_ = v___y_2916_;
v___y_2708_ = v___x_2932_;
v___y_2709_ = v___y_2917_;
v___y_2710_ = v___y_2918_;
v___y_2711_ = v___y_2919_;
v___y_2712_ = v___y_2920_;
v___y_2713_ = v___y_2921_;
v___y_2714_ = v___y_2922_;
v___y_2715_ = v___y_2923_;
v___y_2716_ = v___y_2924_;
v___y_2717_ = v___x_2933_;
v___y_2718_ = v___x_2936_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2937_; 
lean_dec(v___y_2914_);
v___x_2937_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2699_ = v___y_2910_;
v___y_2700_ = v___y_2911_;
v___y_2701_ = v___x_2934_;
v___y_2702_ = v___y_2912_;
v___y_2703_ = v___y_2913_;
v___y_2704_ = v___y_2915_;
v___y_2705_ = v___x_2929_;
v___y_2706_ = v___x_2927_;
v___y_2707_ = v___y_2916_;
v___y_2708_ = v___x_2932_;
v___y_2709_ = v___y_2917_;
v___y_2710_ = v___y_2918_;
v___y_2711_ = v___y_2919_;
v___y_2712_ = v___y_2920_;
v___y_2713_ = v___y_2921_;
v___y_2714_ = v___y_2922_;
v___y_2715_ = v___y_2923_;
v___y_2716_ = v___y_2924_;
v___y_2717_ = v___x_2933_;
v___y_2718_ = v___x_2937_;
goto v___jp_2698_;
}
}
v___jp_2938_:
{
if (v___y_2956_ == 0)
{
lean_object* v_ref_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_ref_2957_ = lean_ctor_get(v___y_2944_, 5);
v___x_2958_ = l_Lean_SourceInfo_fromRef(v_ref_2957_, v___y_2956_);
v___x_2959_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2960_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_2959_);
v___x_2961_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_2962_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2965_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2943_) == 1)
{
lean_object* v_val_2966_; lean_object* v___x_2967_; 
v_val_2966_ = lean_ctor_get(v___y_2943_, 0);
lean_inc(v_val_2966_);
lean_dec_ref(v___y_2943_);
v___x_2967_ = l_Array_mkArray1___redArg(v_val_2966_);
v___y_2762_ = v___y_2939_;
v___y_2763_ = v___y_2940_;
v___y_2764_ = v___y_2941_;
v___y_2765_ = v___y_2942_;
v___y_2766_ = v___x_2964_;
v___y_2767_ = v___y_2944_;
v___y_2768_ = v___x_2958_;
v___y_2769_ = v___y_2945_;
v___y_2770_ = v___y_2946_;
v___y_2771_ = v___y_2947_;
v___y_2772_ = v___y_2948_;
v___y_2773_ = v___y_2949_;
v___y_2774_ = v___x_2960_;
v___y_2775_ = v___y_2951_;
v___y_2776_ = v___y_2952_;
v___y_2777_ = v___y_2950_;
v___y_2778_ = v___x_2963_;
v___y_2779_ = v___y_2953_;
v___y_2780_ = v___y_2954_;
v___y_2781_ = v___x_2965_;
v___y_2782_ = v___x_2967_;
goto v___jp_2761_;
}
else
{
lean_object* v___x_2968_; 
lean_dec(v___y_2943_);
v___x_2968_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2762_ = v___y_2939_;
v___y_2763_ = v___y_2940_;
v___y_2764_ = v___y_2941_;
v___y_2765_ = v___y_2942_;
v___y_2766_ = v___x_2964_;
v___y_2767_ = v___y_2944_;
v___y_2768_ = v___x_2958_;
v___y_2769_ = v___y_2945_;
v___y_2770_ = v___y_2946_;
v___y_2771_ = v___y_2947_;
v___y_2772_ = v___y_2948_;
v___y_2773_ = v___y_2949_;
v___y_2774_ = v___x_2960_;
v___y_2775_ = v___y_2951_;
v___y_2776_ = v___y_2952_;
v___y_2777_ = v___y_2950_;
v___y_2778_ = v___x_2963_;
v___y_2779_ = v___y_2953_;
v___y_2780_ = v___y_2954_;
v___y_2781_ = v___x_2965_;
v___y_2782_ = v___x_2968_;
goto v___jp_2761_;
}
}
else
{
lean_object* v_ref_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_ref_2969_ = lean_ctor_get(v___y_2944_, 5);
v___x_2970_ = l_Lean_SourceInfo_fromRef(v_ref_2969_, v___y_2955_);
v___x_2971_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2972_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_2971_);
v___x_2973_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_2974_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2977_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2943_) == 1)
{
lean_object* v_val_2978_; lean_object* v___x_2979_; 
v_val_2978_ = lean_ctor_get(v___y_2943_, 0);
lean_inc(v_val_2978_);
lean_dec_ref(v___y_2943_);
v___x_2979_ = l_Array_mkArray1___redArg(v_val_2978_);
v___y_2826_ = v___y_2939_;
v___y_2827_ = v___y_2940_;
v___y_2828_ = v___y_2941_;
v___y_2829_ = v___y_2942_;
v___y_2830_ = v___y_2944_;
v___y_2831_ = v___x_2977_;
v___y_2832_ = v___x_2972_;
v___y_2833_ = v___y_2945_;
v___y_2834_ = v___y_2946_;
v___y_2835_ = v___y_2947_;
v___y_2836_ = v___x_2970_;
v___y_2837_ = v___y_2948_;
v___y_2838_ = v___y_2949_;
v___y_2839_ = v___x_2976_;
v___y_2840_ = v___y_2951_;
v___y_2841_ = v___y_2952_;
v___y_2842_ = v___y_2950_;
v___y_2843_ = v___y_2953_;
v___y_2844_ = v___y_2954_;
v___y_2845_ = v___x_2975_;
v___y_2846_ = v___x_2979_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2980_; 
lean_dec(v___y_2943_);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2826_ = v___y_2939_;
v___y_2827_ = v___y_2940_;
v___y_2828_ = v___y_2941_;
v___y_2829_ = v___y_2942_;
v___y_2830_ = v___y_2944_;
v___y_2831_ = v___x_2977_;
v___y_2832_ = v___x_2972_;
v___y_2833_ = v___y_2945_;
v___y_2834_ = v___y_2946_;
v___y_2835_ = v___y_2947_;
v___y_2836_ = v___x_2970_;
v___y_2837_ = v___y_2948_;
v___y_2838_ = v___y_2949_;
v___y_2839_ = v___x_2976_;
v___y_2840_ = v___y_2951_;
v___y_2841_ = v___y_2952_;
v___y_2842_ = v___y_2950_;
v___y_2843_ = v___y_2953_;
v___y_2844_ = v___y_2954_;
v___y_2845_ = v___x_2975_;
v___y_2846_ = v___x_2980_;
goto v___jp_2825_;
}
}
}
v___jp_2981_:
{
lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2998_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2986_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = lean_array_get_size(v___y_2983_);
v___x_3001_ = lean_nat_dec_eq(v___x_3000_, v___x_2527_);
if (v___x_3001_ == 0)
{
if (lean_obj_tag(v___y_2987_) == 0)
{
v___y_2939_ = v___y_2990_;
v___y_2940_ = v___y_2992_;
v___y_2941_ = v_stxForExecution_2989_;
v___y_2942_ = v___y_2991_;
v___y_2943_ = v___y_2982_;
v___y_2944_ = v___y_2996_;
v___y_2945_ = v___y_2994_;
v___y_2946_ = v___y_2987_;
v___y_2947_ = v___y_2988_;
v___y_2948_ = v_a_2999_;
v___y_2949_ = v___y_2997_;
v___y_2950_ = v___y_2984_;
v___y_2951_ = v___y_2983_;
v___y_2952_ = v___y_2995_;
v___y_2953_ = v___y_2985_;
v___y_2954_ = v___y_2993_;
v___y_2955_ = v___x_3001_;
v___y_2956_ = v___x_3001_;
goto v___jp_2938_;
}
else
{
v___y_2939_ = v___y_2990_;
v___y_2940_ = v___y_2992_;
v___y_2941_ = v_stxForExecution_2989_;
v___y_2942_ = v___y_2991_;
v___y_2943_ = v___y_2982_;
v___y_2944_ = v___y_2996_;
v___y_2945_ = v___y_2994_;
v___y_2946_ = v___y_2987_;
v___y_2947_ = v___y_2988_;
v___y_2948_ = v_a_2999_;
v___y_2949_ = v___y_2997_;
v___y_2950_ = v___y_2984_;
v___y_2951_ = v___y_2983_;
v___y_2952_ = v___y_2995_;
v___y_2953_ = v___y_2985_;
v___y_2954_ = v___y_2993_;
v___y_2955_ = v___x_3001_;
v___y_2956_ = v___y_2988_;
goto v___jp_2938_;
}
}
else
{
lean_dec_ref(v___y_2983_);
if (lean_obj_tag(v___y_2987_) == 0)
{
uint8_t v___x_3002_; 
v___x_3002_ = 0;
v___y_2910_ = v___y_2990_;
v___y_2911_ = v___y_2992_;
v___y_2912_ = v_stxForExecution_2989_;
v___y_2913_ = v___y_2991_;
v___y_2914_ = v___y_2982_;
v___y_2915_ = v___y_2996_;
v___y_2916_ = v___y_2994_;
v___y_2917_ = v___y_2987_;
v___y_2918_ = v___y_2988_;
v___y_2919_ = v_a_2999_;
v___y_2920_ = v___y_2997_;
v___y_2921_ = v___y_2995_;
v___y_2922_ = v___y_2984_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v___y_2993_;
v___y_2925_ = v___x_3002_;
goto v___jp_2909_;
}
else
{
if (v___y_2988_ == 0)
{
v___y_2910_ = v___y_2990_;
v___y_2911_ = v___y_2992_;
v___y_2912_ = v_stxForExecution_2989_;
v___y_2913_ = v___y_2991_;
v___y_2914_ = v___y_2982_;
v___y_2915_ = v___y_2996_;
v___y_2916_ = v___y_2994_;
v___y_2917_ = v___y_2987_;
v___y_2918_ = v___y_2988_;
v___y_2919_ = v_a_2999_;
v___y_2920_ = v___y_2997_;
v___y_2921_ = v___y_2995_;
v___y_2922_ = v___y_2984_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v___y_2993_;
v___y_2925_ = v___y_2988_;
goto v___jp_2909_;
}
else
{
lean_object* v_ref_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_ref_3003_ = lean_ctor_get(v___y_2996_, 5);
v___x_3004_ = 0;
v___x_3005_ = l_Lean_SourceInfo_fromRef(v_ref_3003_, v___x_3004_);
v___x_3006_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3007_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3006_);
v___x_3008_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_3009_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3012_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2982_) == 1)
{
lean_object* v_val_3013_; lean_object* v___x_3014_; 
v_val_3013_ = lean_ctor_get(v___y_2982_, 0);
lean_inc(v_val_3013_);
lean_dec_ref(v___y_2982_);
v___x_3014_ = l_Array_mkArray1___redArg(v_val_3013_);
v___y_2881_ = v___y_2990_;
v___y_2882_ = v___y_2992_;
v___y_2883_ = v_stxForExecution_2989_;
v___y_2884_ = v___y_2991_;
v___y_2885_ = v___x_3011_;
v___y_2886_ = v___y_2996_;
v___y_2887_ = v___x_3010_;
v___y_2888_ = v___x_3007_;
v___y_2889_ = v___y_2994_;
v___y_2890_ = v___x_3012_;
v___y_2891_ = v___y_2987_;
v___y_2892_ = v___y_2988_;
v___y_2893_ = v_a_2999_;
v___y_2894_ = v___y_2997_;
v___y_2895_ = v___y_2995_;
v___y_2896_ = v___y_2984_;
v___y_2897_ = v___x_3005_;
v___y_2898_ = v___y_2985_;
v___y_2899_ = v___y_2993_;
v___y_2900_ = v___x_3014_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_3015_; 
lean_dec(v___y_2982_);
v___x_3015_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2881_ = v___y_2990_;
v___y_2882_ = v___y_2992_;
v___y_2883_ = v_stxForExecution_2989_;
v___y_2884_ = v___y_2991_;
v___y_2885_ = v___x_3011_;
v___y_2886_ = v___y_2996_;
v___y_2887_ = v___x_3010_;
v___y_2888_ = v___x_3007_;
v___y_2889_ = v___y_2994_;
v___y_2890_ = v___x_3012_;
v___y_2891_ = v___y_2987_;
v___y_2892_ = v___y_2988_;
v___y_2893_ = v_a_2999_;
v___y_2894_ = v___y_2997_;
v___y_2895_ = v___y_2995_;
v___y_2896_ = v___y_2984_;
v___y_2897_ = v___x_3005_;
v___y_2898_ = v___y_2985_;
v___y_2899_ = v___y_2993_;
v___y_2900_ = v___x_3015_;
goto v___jp_2880_;
}
}
}
}
}
v___jp_3016_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_inc_ref_n(v___y_3023_, 2);
v___x_3039_ = l_Array_append___redArg(v___y_3023_, v___y_3038_);
lean_dec_ref(v___y_3038_);
lean_inc_n(v___y_3029_, 2);
lean_inc_n(v___y_3032_, 2);
v___x_3040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3032_);
lean_ctor_set(v___x_3040_, 1, v___y_3029_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3041_, 0, v___y_3032_);
lean_ctor_set(v___x_3041_, 1, v___y_3029_);
lean_ctor_set(v___x_3041_, 2, v___y_3023_);
lean_inc(v___y_3022_);
v___x_3042_ = l_Lean_Syntax_node5(v___y_3032_, v___y_3034_, v___y_3026_, v___y_3022_, v___y_3027_, v___x_3040_, v___x_3041_);
v___y_2982_ = v___y_3019_;
v___y_2983_ = v___y_3031_;
v___y_2984_ = v___y_3030_;
v___y_2985_ = v___y_3033_;
v___y_2986_ = v___y_3022_;
v___y_2987_ = v___y_3024_;
v___y_2988_ = v___y_3025_;
v_stxForExecution_2989_ = v___x_3042_;
v___y_2990_ = v___y_3018_;
v___y_2991_ = v___y_3021_;
v___y_2992_ = v___y_3037_;
v___y_2993_ = v___y_3035_;
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___y_3017_;
v___y_2996_ = v___y_3020_;
v___y_2997_ = v___y_3036_;
goto v___jp_2981_;
}
v___jp_3043_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_inc_ref(v___y_3050_);
v___x_3065_ = l_Array_append___redArg(v___y_3050_, v___y_3064_);
lean_dec_ref(v___y_3064_);
lean_inc(v___y_3055_);
lean_inc(v___y_3058_);
v___x_3066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3066_, 0, v___y_3058_);
lean_ctor_set(v___x_3066_, 1, v___y_3055_);
lean_ctor_set(v___x_3066_, 2, v___x_3065_);
if (lean_obj_tag(v___y_3059_) == 1)
{
lean_object* v_val_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_val_3067_ = lean_ctor_get(v___y_3059_, 0);
v___x_3068_ = l_Lean_SourceInfo_fromRef(v_val_3067_, v___x_2512_);
v___x_3069_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l_Array_mkArray1___redArg(v___x_3070_);
v___y_3017_ = v___y_3044_;
v___y_3018_ = v___y_3045_;
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3047_;
v___y_3021_ = v___y_3048_;
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___y_3050_;
v___y_3024_ = v___y_3051_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___x_3066_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3057_;
v___y_3031_ = v___y_3056_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3059_;
v___y_3034_ = v___y_3060_;
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3063_;
v___y_3037_ = v___y_3062_;
v___y_3038_ = v___x_3071_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3017_ = v___y_3044_;
v___y_3018_ = v___y_3045_;
v___y_3019_ = v___y_3046_;
v___y_3020_ = v___y_3047_;
v___y_3021_ = v___y_3048_;
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___y_3050_;
v___y_3024_ = v___y_3051_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___x_3066_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3057_;
v___y_3031_ = v___y_3056_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3059_;
v___y_3034_ = v___y_3060_;
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3063_;
v___y_3037_ = v___y_3062_;
v___y_3038_ = v___x_3072_;
goto v___jp_3016_;
}
}
v___jp_3073_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_inc_ref_n(v___y_3085_, 2);
v___x_3096_ = l_Array_append___redArg(v___y_3085_, v___y_3095_);
lean_dec_ref(v___y_3095_);
lean_inc_n(v___y_3086_, 3);
lean_inc_n(v___y_3079_, 5);
v___x_3097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3097_, 0, v___y_3079_);
lean_ctor_set(v___x_3097_, 1, v___y_3086_);
lean_ctor_set(v___x_3097_, 2, v___x_3096_);
v___x_3098_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___y_3079_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3101_ = l_Lean_Syntax_SepArray_ofElems(v___x_3100_, v___y_3089_);
v___x_3102_ = l_Array_append___redArg(v___y_3085_, v___x_3101_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3079_);
lean_ctor_set(v___x_3103_, 1, v___y_3086_);
lean_ctor_set(v___x_3103_, 2, v___x_3102_);
v___x_3104_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3079_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = l_Lean_Syntax_node3(v___y_3079_, v___y_3086_, v___x_3099_, v___x_3103_, v___x_3105_);
lean_inc(v___y_3080_);
v___x_3107_ = l_Lean_Syntax_node5(v___y_3079_, v___y_3082_, v___y_3090_, v___y_3080_, v___y_3084_, v___x_3097_, v___x_3106_);
v___y_2982_ = v___y_3076_;
v___y_2983_ = v___y_3089_;
v___y_2984_ = v___y_3088_;
v___y_2985_ = v___y_3091_;
v___y_2986_ = v___y_3080_;
v___y_2987_ = v___y_3081_;
v___y_2988_ = v___y_3083_;
v_stxForExecution_2989_ = v___x_3107_;
v___y_2990_ = v___y_3075_;
v___y_2991_ = v___y_3078_;
v___y_2992_ = v___y_3094_;
v___y_2993_ = v___y_3092_;
v___y_2994_ = v___y_3087_;
v___y_2995_ = v___y_3074_;
v___y_2996_ = v___y_3077_;
v___y_2997_ = v___y_3093_;
goto v___jp_2981_;
}
v___jp_3108_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_inc_ref(v___y_3119_);
v___x_3130_ = l_Array_append___redArg(v___y_3119_, v___y_3129_);
lean_dec_ref(v___y_3129_);
lean_inc(v___y_3120_);
lean_inc(v___y_3114_);
v___x_3131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3131_, 0, v___y_3114_);
lean_ctor_set(v___x_3131_, 1, v___y_3120_);
lean_ctor_set(v___x_3131_, 2, v___x_3130_);
if (lean_obj_tag(v___y_3125_) == 1)
{
lean_object* v_val_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_val_3132_ = lean_ctor_get(v___y_3125_, 0);
v___x_3133_ = l_Lean_SourceInfo_fromRef(v_val_3132_, v___x_2512_);
v___x_3134_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = l_Array_mkArray1___redArg(v___x_3135_);
v___y_3074_ = v___y_3109_;
v___y_3075_ = v___y_3110_;
v___y_3076_ = v___y_3111_;
v___y_3077_ = v___y_3112_;
v___y_3078_ = v___y_3113_;
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___x_3131_;
v___y_3085_ = v___y_3119_;
v___y_3086_ = v___y_3120_;
v___y_3087_ = v___y_3121_;
v___y_3088_ = v___y_3124_;
v___y_3089_ = v___y_3123_;
v___y_3090_ = v___y_3122_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___x_3136_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3074_ = v___y_3109_;
v___y_3075_ = v___y_3110_;
v___y_3076_ = v___y_3111_;
v___y_3077_ = v___y_3112_;
v___y_3078_ = v___y_3113_;
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___x_3131_;
v___y_3085_ = v___y_3119_;
v___y_3086_ = v___y_3120_;
v___y_3087_ = v___y_3121_;
v___y_3088_ = v___y_3124_;
v___y_3089_ = v___y_3123_;
v___y_3090_ = v___y_3122_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3126_;
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___x_3137_;
goto v___jp_3073_;
}
}
v___jp_3138_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_inc_ref_n(v___y_3148_, 2);
v___x_3161_ = l_Array_append___redArg(v___y_3148_, v___y_3160_);
lean_dec_ref(v___y_3160_);
lean_inc_n(v___y_3151_, 3);
lean_inc_n(v___y_3149_, 5);
v___x_3162_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3162_, 0, v___y_3149_);
lean_ctor_set(v___x_3162_, 1, v___y_3151_);
lean_ctor_set(v___x_3162_, 2, v___x_3161_);
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___y_3149_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3166_ = l_Lean_Syntax_SepArray_ofElems(v___x_3165_, v___y_3153_);
v___x_3167_ = l_Array_append___redArg(v___y_3148_, v___x_3166_);
lean_dec_ref(v___x_3166_);
v___x_3168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3168_, 0, v___y_3149_);
lean_ctor_set(v___x_3168_, 1, v___y_3151_);
lean_ctor_set(v___x_3168_, 2, v___x_3167_);
v___x_3169_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___y_3149_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_node3(v___y_3149_, v___y_3151_, v___x_3164_, v___x_3168_, v___x_3170_);
lean_inc(v___y_3145_);
v___x_3172_ = l_Lean_Syntax_node5(v___y_3149_, v___y_3155_, v___y_3143_, v___y_3145_, v___y_3156_, v___x_3162_, v___x_3171_);
v___y_2982_ = v___y_3141_;
v___y_2983_ = v___y_3153_;
v___y_2984_ = v___y_3152_;
v___y_2985_ = v___y_3154_;
v___y_2986_ = v___y_3145_;
v___y_2987_ = v___y_3146_;
v___y_2988_ = v___y_3147_;
v_stxForExecution_2989_ = v___x_3172_;
v___y_2990_ = v___y_3140_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3159_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3150_;
v___y_2995_ = v___y_3139_;
v___y_2996_ = v___y_3142_;
v___y_2997_ = v___y_3158_;
goto v___jp_2981_;
}
v___jp_3173_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_inc_ref(v___y_3182_);
v___x_3195_ = l_Array_append___redArg(v___y_3182_, v___y_3194_);
lean_dec_ref(v___y_3194_);
lean_inc(v___y_3186_);
lean_inc(v___y_3184_);
v___x_3196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3196_, 0, v___y_3184_);
lean_ctor_set(v___x_3196_, 1, v___y_3186_);
lean_ctor_set(v___x_3196_, 2, v___x_3195_);
if (lean_obj_tag(v___y_3189_) == 1)
{
lean_object* v_val_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_val_3197_ = lean_ctor_get(v___y_3189_, 0);
v___x_3198_ = l_Lean_SourceInfo_fromRef(v_val_3197_, v___x_2512_);
v___x_3199_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Array_mkArray1___redArg(v___x_3200_);
v___y_3139_ = v___y_3174_;
v___y_3140_ = v___y_3175_;
v___y_3141_ = v___y_3176_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3178_;
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3183_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3184_;
v___y_3150_ = v___y_3185_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3188_;
v___y_3153_ = v___y_3187_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___x_3196_;
v___y_3157_ = v___y_3191_;
v___y_3158_ = v___y_3193_;
v___y_3159_ = v___y_3192_;
v___y_3160_ = v___x_3201_;
goto v___jp_3138_;
}
else
{
lean_object* v___x_3202_; 
v___x_3202_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3139_ = v___y_3174_;
v___y_3140_ = v___y_3175_;
v___y_3141_ = v___y_3176_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3178_;
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3183_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3184_;
v___y_3150_ = v___y_3185_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3188_;
v___y_3153_ = v___y_3187_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___x_3196_;
v___y_3157_ = v___y_3191_;
v___y_3158_ = v___y_3193_;
v___y_3159_ = v___y_3192_;
v___y_3160_ = v___x_3202_;
goto v___jp_3138_;
}
}
v___jp_3203_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_inc_ref_n(v___y_3204_, 2);
v___x_3226_ = l_Array_append___redArg(v___y_3204_, v___y_3225_);
lean_dec_ref(v___y_3225_);
lean_inc_n(v___y_3206_, 2);
lean_inc_n(v___y_3216_, 2);
v___x_3227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3227_, 0, v___y_3216_);
lean_ctor_set(v___x_3227_, 1, v___y_3206_);
lean_ctor_set(v___x_3227_, 2, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___y_3216_);
lean_ctor_set(v___x_3228_, 1, v___y_3206_);
lean_ctor_set(v___x_3228_, 2, v___y_3204_);
lean_inc(v___y_3212_);
v___x_3229_ = l_Lean_Syntax_node5(v___y_3216_, v___y_3211_, v___y_3213_, v___y_3212_, v___y_3222_, v___x_3227_, v___x_3228_);
v___y_2982_ = v___y_3208_;
v___y_2983_ = v___y_3219_;
v___y_2984_ = v___y_3218_;
v___y_2985_ = v___y_3220_;
v___y_2986_ = v___y_3212_;
v___y_2987_ = v___y_3214_;
v___y_2988_ = v___y_3215_;
v_stxForExecution_2989_ = v___x_3229_;
v___y_2990_ = v___y_3207_;
v___y_2991_ = v___y_3210_;
v___y_2992_ = v___y_3224_;
v___y_2993_ = v___y_3221_;
v___y_2994_ = v___y_3217_;
v___y_2995_ = v___y_3205_;
v___y_2996_ = v___y_3209_;
v___y_2997_ = v___y_3223_;
goto v___jp_2981_;
}
v___jp_3230_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_inc_ref(v___y_3231_);
v___x_3252_ = l_Array_append___redArg(v___y_3231_, v___y_3251_);
lean_dec_ref(v___y_3251_);
lean_inc(v___y_3233_);
lean_inc(v___y_3242_);
v___x_3253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3253_, 0, v___y_3242_);
lean_ctor_set(v___x_3253_, 1, v___y_3233_);
lean_ctor_set(v___x_3253_, 2, v___x_3252_);
if (lean_obj_tag(v___y_3247_) == 1)
{
lean_object* v_val_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_val_3254_ = lean_ctor_get(v___y_3247_, 0);
v___x_3255_ = l_Lean_SourceInfo_fromRef(v_val_3254_, v___x_2512_);
v___x_3256_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l_Array_mkArray1___redArg(v___x_3257_);
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3242_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3246_;
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3247_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___x_3253_;
v___y_3223_ = v___y_3250_;
v___y_3224_ = v___y_3249_;
v___y_3225_ = v___x_3258_;
goto v___jp_3203_;
}
else
{
lean_object* v___x_3259_; 
v___x_3259_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3242_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3246_;
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3247_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___x_3253_;
v___y_3223_ = v___y_3250_;
v___y_3224_ = v___y_3249_;
v___y_3225_ = v___x_3259_;
goto v___jp_3203_;
}
}
v___jp_3260_:
{
lean_object* v_ref_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_ref_3277_ = lean_ctor_get(v___y_3263_, 5);
v___x_3278_ = l_Lean_SourceInfo_fromRef(v_ref_3277_, v___y_3276_);
v___x_3279_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3280_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3279_);
v___x_3281_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3285_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3264_) == 1)
{
lean_object* v_val_3286_; lean_object* v___x_3287_; 
v_val_3286_ = lean_ctor_get(v___y_3264_, 0);
lean_inc(v_val_3286_);
v___x_3287_ = l_Array_mkArray1___redArg(v_val_3286_);
v___y_3044_ = v___y_3261_;
v___y_3045_ = v___y_3262_;
v___y_3046_ = v___y_3264_;
v___y_3047_ = v___y_3263_;
v___y_3048_ = v___y_3265_;
v___y_3049_ = v___y_3266_;
v___y_3050_ = v___x_3285_;
v___y_3051_ = v___y_3267_;
v___y_3052_ = v___y_3268_;
v___y_3053_ = v___x_3283_;
v___y_3054_ = v___y_3269_;
v___y_3055_ = v___x_3284_;
v___y_3056_ = v___y_3270_;
v___y_3057_ = v___y_3271_;
v___y_3058_ = v___x_3278_;
v___y_3059_ = v___y_3272_;
v___y_3060_ = v___x_3280_;
v___y_3061_ = v___y_3273_;
v___y_3062_ = v___y_3275_;
v___y_3063_ = v___y_3274_;
v___y_3064_ = v___x_3287_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3044_ = v___y_3261_;
v___y_3045_ = v___y_3262_;
v___y_3046_ = v___y_3264_;
v___y_3047_ = v___y_3263_;
v___y_3048_ = v___y_3265_;
v___y_3049_ = v___y_3266_;
v___y_3050_ = v___x_3285_;
v___y_3051_ = v___y_3267_;
v___y_3052_ = v___y_3268_;
v___y_3053_ = v___x_3283_;
v___y_3054_ = v___y_3269_;
v___y_3055_ = v___x_3284_;
v___y_3056_ = v___y_3270_;
v___y_3057_ = v___y_3271_;
v___y_3058_ = v___x_3278_;
v___y_3059_ = v___y_3272_;
v___y_3060_ = v___x_3280_;
v___y_3061_ = v___y_3273_;
v___y_3062_ = v___y_3275_;
v___y_3063_ = v___y_3274_;
v___y_3064_ = v___x_3288_;
goto v___jp_3043_;
}
}
v___jp_3289_:
{
if (v___y_3306_ == 0)
{
lean_object* v_ref_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_ref_3307_ = lean_ctor_get(v___y_3292_, 5);
v___x_3308_ = l_Lean_SourceInfo_fromRef(v_ref_3307_, v___y_3306_);
v___x_3309_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3310_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3309_);
v___x_3311_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_3312_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3315_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3293_) == 1)
{
lean_object* v_val_3316_; lean_object* v___x_3317_; 
v_val_3316_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3316_);
v___x_3317_ = l_Array_mkArray1___redArg(v_val_3316_);
v___y_3109_ = v___y_3290_;
v___y_3110_ = v___y_3291_;
v___y_3111_ = v___y_3293_;
v___y_3112_ = v___y_3292_;
v___y_3113_ = v___y_3294_;
v___y_3114_ = v___x_3308_;
v___y_3115_ = v___y_3295_;
v___y_3116_ = v___y_3296_;
v___y_3117_ = v___x_3310_;
v___y_3118_ = v___y_3297_;
v___y_3119_ = v___x_3315_;
v___y_3120_ = v___x_3314_;
v___y_3121_ = v___y_3299_;
v___y_3122_ = v___x_3313_;
v___y_3123_ = v___y_3300_;
v___y_3124_ = v___y_3301_;
v___y_3125_ = v___y_3302_;
v___y_3126_ = v___y_3303_;
v___y_3127_ = v___y_3305_;
v___y_3128_ = v___y_3304_;
v___y_3129_ = v___x_3317_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3318_; 
v___x_3318_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3109_ = v___y_3290_;
v___y_3110_ = v___y_3291_;
v___y_3111_ = v___y_3293_;
v___y_3112_ = v___y_3292_;
v___y_3113_ = v___y_3294_;
v___y_3114_ = v___x_3308_;
v___y_3115_ = v___y_3295_;
v___y_3116_ = v___y_3296_;
v___y_3117_ = v___x_3310_;
v___y_3118_ = v___y_3297_;
v___y_3119_ = v___x_3315_;
v___y_3120_ = v___x_3314_;
v___y_3121_ = v___y_3299_;
v___y_3122_ = v___x_3313_;
v___y_3123_ = v___y_3300_;
v___y_3124_ = v___y_3301_;
v___y_3125_ = v___y_3302_;
v___y_3126_ = v___y_3303_;
v___y_3127_ = v___y_3305_;
v___y_3128_ = v___y_3304_;
v___y_3129_ = v___x_3318_;
goto v___jp_3108_;
}
}
else
{
lean_object* v_ref_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_ref_3319_ = lean_ctor_get(v___y_3292_, 5);
v___x_3320_ = l_Lean_SourceInfo_fromRef(v_ref_3319_, v___y_3298_);
v___x_3321_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3322_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3321_);
v___x_3323_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_3324_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3327_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3293_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_val_3328_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3328_);
v___x_3329_ = l_Array_mkArray1___redArg(v_val_3328_);
v___y_3174_ = v___y_3290_;
v___y_3175_ = v___y_3291_;
v___y_3176_ = v___y_3293_;
v___y_3177_ = v___y_3292_;
v___y_3178_ = v___x_3325_;
v___y_3179_ = v___y_3294_;
v___y_3180_ = v___y_3295_;
v___y_3181_ = v___y_3296_;
v___y_3182_ = v___x_3327_;
v___y_3183_ = v___y_3297_;
v___y_3184_ = v___x_3320_;
v___y_3185_ = v___y_3299_;
v___y_3186_ = v___x_3326_;
v___y_3187_ = v___y_3300_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___y_3302_;
v___y_3190_ = v___x_3322_;
v___y_3191_ = v___y_3303_;
v___y_3192_ = v___y_3305_;
v___y_3193_ = v___y_3304_;
v___y_3194_ = v___x_3329_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3174_ = v___y_3290_;
v___y_3175_ = v___y_3291_;
v___y_3176_ = v___y_3293_;
v___y_3177_ = v___y_3292_;
v___y_3178_ = v___x_3325_;
v___y_3179_ = v___y_3294_;
v___y_3180_ = v___y_3295_;
v___y_3181_ = v___y_3296_;
v___y_3182_ = v___x_3327_;
v___y_3183_ = v___y_3297_;
v___y_3184_ = v___x_3320_;
v___y_3185_ = v___y_3299_;
v___y_3186_ = v___x_3326_;
v___y_3187_ = v___y_3300_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___y_3302_;
v___y_3190_ = v___x_3322_;
v___y_3191_ = v___y_3303_;
v___y_3192_ = v___y_3305_;
v___y_3193_ = v___y_3304_;
v___y_3194_ = v___x_3330_;
goto v___jp_3173_;
}
}
}
v___jp_3331_:
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = lean_array_get_size(v_argsArray_3338_);
v___x_3348_ = lean_nat_dec_eq(v___x_3347_, v___x_2527_);
if (v___x_3348_ == 0)
{
if (lean_obj_tag(v___y_3336_) == 0)
{
v___y_3290_ = v___y_3344_;
v___y_3291_ = v___y_3339_;
v___y_3292_ = v___y_3345_;
v___y_3293_ = v___y_3332_;
v___y_3294_ = v___y_3340_;
v___y_3295_ = v___y_3334_;
v___y_3296_ = v___y_3336_;
v___y_3297_ = v___y_3337_;
v___y_3298_ = v___x_3348_;
v___y_3299_ = v___y_3343_;
v___y_3300_ = v_argsArray_3338_;
v___y_3301_ = v___y_3333_;
v___y_3302_ = v___y_3335_;
v___y_3303_ = v___y_3342_;
v___y_3304_ = v___y_3346_;
v___y_3305_ = v___y_3341_;
v___y_3306_ = v___x_3348_;
goto v___jp_3289_;
}
else
{
v___y_3290_ = v___y_3344_;
v___y_3291_ = v___y_3339_;
v___y_3292_ = v___y_3345_;
v___y_3293_ = v___y_3332_;
v___y_3294_ = v___y_3340_;
v___y_3295_ = v___y_3334_;
v___y_3296_ = v___y_3336_;
v___y_3297_ = v___y_3337_;
v___y_3298_ = v___x_3348_;
v___y_3299_ = v___y_3343_;
v___y_3300_ = v_argsArray_3338_;
v___y_3301_ = v___y_3333_;
v___y_3302_ = v___y_3335_;
v___y_3303_ = v___y_3342_;
v___y_3304_ = v___y_3346_;
v___y_3305_ = v___y_3341_;
v___y_3306_ = v___y_3337_;
goto v___jp_3289_;
}
}
else
{
if (lean_obj_tag(v___y_3336_) == 0)
{
uint8_t v___x_3349_; 
v___x_3349_ = 0;
v___y_3261_ = v___y_3344_;
v___y_3262_ = v___y_3339_;
v___y_3263_ = v___y_3345_;
v___y_3264_ = v___y_3332_;
v___y_3265_ = v___y_3340_;
v___y_3266_ = v___y_3334_;
v___y_3267_ = v___y_3336_;
v___y_3268_ = v___y_3337_;
v___y_3269_ = v___y_3343_;
v___y_3270_ = v_argsArray_3338_;
v___y_3271_ = v___y_3333_;
v___y_3272_ = v___y_3335_;
v___y_3273_ = v___y_3342_;
v___y_3274_ = v___y_3346_;
v___y_3275_ = v___y_3341_;
v___y_3276_ = v___x_3349_;
goto v___jp_3260_;
}
else
{
if (v___y_3337_ == 0)
{
v___y_3261_ = v___y_3344_;
v___y_3262_ = v___y_3339_;
v___y_3263_ = v___y_3345_;
v___y_3264_ = v___y_3332_;
v___y_3265_ = v___y_3340_;
v___y_3266_ = v___y_3334_;
v___y_3267_ = v___y_3336_;
v___y_3268_ = v___y_3337_;
v___y_3269_ = v___y_3343_;
v___y_3270_ = v_argsArray_3338_;
v___y_3271_ = v___y_3333_;
v___y_3272_ = v___y_3335_;
v___y_3273_ = v___y_3342_;
v___y_3274_ = v___y_3346_;
v___y_3275_ = v___y_3341_;
v___y_3276_ = v___y_3337_;
goto v___jp_3260_;
}
else
{
lean_object* v_ref_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_ref_3350_ = lean_ctor_get(v___y_3345_, 5);
v___x_3351_ = 0;
v___x_3352_ = l_Lean_SourceInfo_fromRef(v_ref_3350_, v___x_3351_);
v___x_3353_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3354_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3353_);
v___x_3355_ = l_Lean_SourceInfo_fromRef(v_tk_2528_, v___x_2512_);
v___x_3356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3359_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3332_) == 1)
{
lean_object* v_val_3360_; lean_object* v___x_3361_; 
v_val_3360_ = lean_ctor_get(v___y_3332_, 0);
lean_inc(v_val_3360_);
v___x_3361_ = l_Array_mkArray1___redArg(v_val_3360_);
v___y_3231_ = v___x_3359_;
v___y_3232_ = v___y_3344_;
v___y_3233_ = v___x_3358_;
v___y_3234_ = v___y_3339_;
v___y_3235_ = v___y_3332_;
v___y_3236_ = v___y_3345_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___x_3354_;
v___y_3239_ = v___y_3334_;
v___y_3240_ = v___x_3357_;
v___y_3241_ = v___y_3336_;
v___y_3242_ = v___x_3352_;
v___y_3243_ = v___y_3337_;
v___y_3244_ = v___y_3343_;
v___y_3245_ = v_argsArray_3338_;
v___y_3246_ = v___y_3333_;
v___y_3247_ = v___y_3335_;
v___y_3248_ = v___y_3342_;
v___y_3249_ = v___y_3341_;
v___y_3250_ = v___y_3346_;
v___y_3251_ = v___x_3361_;
goto v___jp_3230_;
}
else
{
lean_object* v___x_3362_; 
v___x_3362_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3231_ = v___x_3359_;
v___y_3232_ = v___y_3344_;
v___y_3233_ = v___x_3358_;
v___y_3234_ = v___y_3339_;
v___y_3235_ = v___y_3332_;
v___y_3236_ = v___y_3345_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___x_3354_;
v___y_3239_ = v___y_3334_;
v___y_3240_ = v___x_3357_;
v___y_3241_ = v___y_3336_;
v___y_3242_ = v___x_3352_;
v___y_3243_ = v___y_3337_;
v___y_3244_ = v___y_3343_;
v___y_3245_ = v_argsArray_3338_;
v___y_3246_ = v___y_3333_;
v___y_3247_ = v___y_3335_;
v___y_3248_ = v___y_3342_;
v___y_3249_ = v___y_3341_;
v___y_3250_ = v___y_3346_;
v___y_3251_ = v___x_3362_;
goto v___jp_3230_;
}
}
}
}
}
v___jp_3363_:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3372_, v___y_3365_, v___y_3377_, v___y_3371_, v___y_3378_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = l_Lean_LibrarySuggestions_select(v_a_3381_, v___y_3379_, v___y_3365_, v___y_3377_, v___y_3371_, v___y_3378_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; size_t v_sz_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v_sz_3384_ = lean_array_size(v_a_3383_);
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3383_, v_sz_3384_, v___x_3385_, v___y_3376_, v___y_3375_, v___y_3372_, v___y_3364_, v___y_3369_, v___y_3365_, v___y_3377_, v___y_3371_, v___y_3378_);
lean_dec(v_a_3383_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref(v___x_3386_);
v___y_3332_ = v___y_3366_;
v___y_3333_ = v___y_3373_;
v___y_3334_ = v___y_3367_;
v___y_3335_ = v___y_3374_;
v___y_3336_ = v___y_3368_;
v___y_3337_ = v___y_3370_;
v_argsArray_3338_ = v_a_3387_;
v___y_3339_ = v___y_3375_;
v___y_3340_ = v___y_3372_;
v___y_3341_ = v___y_3364_;
v___y_3342_ = v___y_3369_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v___y_3377_;
v___y_3345_ = v___y_3371_;
v___y_3346_ = v___y_3378_;
goto v___jp_3331_;
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v___y_3374_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v_a_3388_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3386_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3374_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v_a_3396_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3382_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3382_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v___y_3379_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3374_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v_a_3404_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3380_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3380_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
v___jp_3412_:
{
uint8_t v_suggestions_3429_; 
v_suggestions_3429_ = lean_ctor_get_uint8(v___y_3415_, sizeof(void*)*3 + 26);
if (v_suggestions_3429_ == 0)
{
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___f_2516_);
v___y_3332_ = v___y_3416_;
v___y_3333_ = v___y_3423_;
v___y_3334_ = v___y_3417_;
v___y_3335_ = v___y_3424_;
v___y_3336_ = v___y_3418_;
v___y_3337_ = v___y_3420_;
v_argsArray_3338_ = v___y_3428_;
v___y_3339_ = v___y_3425_;
v___y_3340_ = v___y_3422_;
v___y_3341_ = v___y_3413_;
v___y_3342_ = v___y_3419_;
v___y_3343_ = v___y_3414_;
v___y_3344_ = v___y_3426_;
v___y_3345_ = v___y_3421_;
v___y_3346_ = v___y_3427_;
goto v___jp_3331_;
}
else
{
lean_object* v_maxSuggestions_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_maxSuggestions_3430_ = lean_ctor_get(v___y_3415_, 2);
lean_inc(v_maxSuggestions_3430_);
lean_dec_ref(v___y_3415_);
v___x_3431_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3432_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3430_) == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_unsigned_to_nat(100u);
v___x_3434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3431_);
lean_ctor_set(v___x_3434_, 2, v___f_2516_);
lean_ctor_set(v___x_3434_, 3, v___x_3432_);
v___y_3364_ = v___y_3413_;
v___y_3365_ = v___y_3414_;
v___y_3366_ = v___y_3416_;
v___y_3367_ = v___y_3417_;
v___y_3368_ = v___y_3418_;
v___y_3369_ = v___y_3419_;
v___y_3370_ = v___y_3420_;
v___y_3371_ = v___y_3421_;
v___y_3372_ = v___y_3422_;
v___y_3373_ = v___y_3423_;
v___y_3374_ = v___y_3424_;
v___y_3375_ = v___y_3425_;
v___y_3376_ = v___y_3428_;
v___y_3377_ = v___y_3426_;
v___y_3378_ = v___y_3427_;
v___y_3379_ = v___x_3434_;
goto v___jp_3363_;
}
else
{
lean_object* v_val_3435_; lean_object* v___x_3436_; 
v_val_3435_ = lean_ctor_get(v_maxSuggestions_3430_, 0);
lean_inc(v_val_3435_);
lean_dec_ref(v_maxSuggestions_3430_);
v___x_3436_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3436_, 0, v_val_3435_);
lean_ctor_set(v___x_3436_, 1, v___x_3431_);
lean_ctor_set(v___x_3436_, 2, v___f_2516_);
lean_ctor_set(v___x_3436_, 3, v___x_3432_);
v___y_3364_ = v___y_3413_;
v___y_3365_ = v___y_3414_;
v___y_3366_ = v___y_3416_;
v___y_3367_ = v___y_3417_;
v___y_3368_ = v___y_3418_;
v___y_3369_ = v___y_3419_;
v___y_3370_ = v___y_3420_;
v___y_3371_ = v___y_3421_;
v___y_3372_ = v___y_3422_;
v___y_3373_ = v___y_3423_;
v___y_3374_ = v___y_3424_;
v___y_3375_ = v___y_3425_;
v___y_3376_ = v___y_3428_;
v___y_3377_ = v___y_3426_;
v___y_3378_ = v___y_3427_;
v___y_3379_ = v___x_3436_;
goto v___jp_3363_;
}
}
}
v___jp_3437_:
{
uint8_t v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = 1;
lean_inc(v___y_3440_);
v___x_3453_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3440_, v___x_3452_, v___y_3448_, v___y_3438_, v___y_3442_, v___y_3439_, v___y_3449_, v___y_3445_, v___y_3450_);
if (lean_obj_tag(v___x_3453_) == 0)
{
if (lean_obj_tag(v___y_3444_) == 1)
{
lean_object* v_a_3454_; lean_object* v_val_3455_; lean_object* v___x_3456_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v_val_3455_ = lean_ctor_get(v___y_3444_, 0);
lean_inc(v_val_3455_);
lean_dec_ref(v___y_3444_);
v___x_3456_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3455_);
lean_dec(v_val_3455_);
v___y_3413_ = v___y_3438_;
v___y_3414_ = v___y_3439_;
v___y_3415_ = v_a_3454_;
v___y_3416_ = v___y_3451_;
v___y_3417_ = v___y_3440_;
v___y_3418_ = v___y_3441_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3443_;
v___y_3421_ = v___y_3445_;
v___y_3422_ = v___y_3446_;
v___y_3423_ = v___x_3452_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3448_;
v___y_3426_ = v___y_3449_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v___x_3456_;
goto v___jp_3412_;
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
lean_dec(v___y_3444_);
v_a_3457_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3457_);
lean_dec_ref(v___x_3453_);
v___x_3458_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3413_ = v___y_3438_;
v___y_3414_ = v___y_3439_;
v___y_3415_ = v_a_3457_;
v___y_3416_ = v___y_3451_;
v___y_3417_ = v___y_3440_;
v___y_3418_ = v___y_3441_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3443_;
v___y_3421_ = v___y_3445_;
v___y_3422_ = v___y_3446_;
v___y_3423_ = v___x_3452_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3448_;
v___y_3426_ = v___y_3449_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v___x_3458_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v___y_3451_);
lean_dec(v___y_3447_);
lean_dec(v___y_3444_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v_a_3459_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3453_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3453_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
v___jp_3467_:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Syntax_getOptional_x3f(v___y_3468_);
lean_dec(v___y_3468_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_box(0);
v___y_3438_ = v___y_3476_;
v___y_3439_ = v___y_3478_;
v___y_3440_ = v___y_3470_;
v___y_3441_ = v___y_3471_;
v___y_3442_ = v___y_3477_;
v___y_3443_ = v___y_3472_;
v___y_3444_ = v_args_3473_;
v___y_3445_ = v___y_3480_;
v___y_3446_ = v___y_3475_;
v___y_3447_ = v___y_3469_;
v___y_3448_ = v___y_3474_;
v___y_3449_ = v___y_3479_;
v___y_3450_ = v___y_3481_;
v___y_3451_ = v___x_3483_;
goto v___jp_3437_;
}
else
{
lean_object* v_val_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_val_3484_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3482_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_val_3484_);
lean_dec(v___x_3482_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_val_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
v___y_3438_ = v___y_3476_;
v___y_3439_ = v___y_3478_;
v___y_3440_ = v___y_3470_;
v___y_3441_ = v___y_3471_;
v___y_3442_ = v___y_3477_;
v___y_3443_ = v___y_3472_;
v___y_3444_ = v_args_3473_;
v___y_3445_ = v___y_3480_;
v___y_3446_ = v___y_3475_;
v___y_3447_ = v___y_3469_;
v___y_3448_ = v___y_3474_;
v___y_3449_ = v___y_3479_;
v___y_3450_ = v___y_3481_;
v___y_3451_ = v___x_3489_;
goto v___jp_3437_;
}
}
}
}
v___jp_3493_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3508_ = lean_unsigned_to_nat(3u);
v___x_3509_ = l_Lean_Syntax_getArg(v___y_3495_, v___x_3508_);
lean_dec(v___y_3495_);
v___x_3510_ = l_Lean_Syntax_isNone(v___x_3509_);
if (v___x_3510_ == 0)
{
uint8_t v___x_3511_; 
lean_inc(v___x_3509_);
v___x_3511_ = l_Lean_Syntax_matchesNull(v___x_3509_, v___x_3492_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; 
lean_dec(v___x_3509_);
lean_dec(v_o_3499_);
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v___y_3494_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_3512_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3512_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3513_ = l_Lean_Syntax_getArg(v___x_3509_, v___x_2527_);
lean_dec(v___x_3509_);
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3515_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3514_);
lean_inc(v___x_3513_);
v___x_3516_ = l_Lean_Syntax_isOfKind(v___x_3513_, v___x_3515_);
lean_dec(v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v___x_3513_);
lean_dec(v_o_3499_);
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v___y_3494_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_3517_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; lean_object* v_args_3519_; lean_object* v___x_3520_; 
v___x_3518_ = l_Lean_Syntax_getArg(v___x_3513_, v___x_3492_);
lean_dec(v___x_3513_);
v_args_3519_ = l_Lean_Syntax_getArgs(v___x_3518_);
lean_dec(v___x_3518_);
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_args_3519_);
v___y_3468_ = v___y_3494_;
v___y_3469_ = v_o_3499_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___y_3497_;
v___y_3472_ = v___y_3498_;
v_args_3473_ = v___x_3520_;
v___y_3474_ = v___y_3500_;
v___y_3475_ = v___y_3501_;
v___y_3476_ = v___y_3502_;
v___y_3477_ = v___y_3503_;
v___y_3478_ = v___y_3504_;
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
goto v___jp_3467_;
}
}
}
else
{
lean_object* v___x_3521_; 
lean_dec(v___x_3509_);
v___x_3521_ = lean_box(0);
v___y_3468_ = v___y_3494_;
v___y_3469_ = v_o_3499_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___y_3497_;
v___y_3472_ = v___y_3498_;
v_args_3473_ = v___x_3521_;
v___y_3474_ = v___y_3500_;
v___y_3475_ = v___y_3501_;
v___y_3476_ = v___y_3502_;
v___y_3477_ = v___y_3503_;
v___y_3478_ = v___y_3504_;
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
goto v___jp_3467_;
}
}
v___jp_3522_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3532_ = lean_unsigned_to_nat(2u);
v___x_3533_ = l_Lean_Syntax_getArg(v_stx_2511_, v___x_3532_);
v___x_3534_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3535_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3534_);
lean_inc(v___x_3533_);
v___x_3536_ = l_Lean_Syntax_isOfKind(v___x_3533_, v___x_3535_);
lean_dec(v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec(v___x_3533_);
lean_dec(v_bang_3523_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_3537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3537_;
}
else
{
lean_object* v_cfg_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_cfg_3538_ = l_Lean_Syntax_getArg(v___x_3533_, v___x_2527_);
v___x_3539_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2515_);
lean_inc_ref(v___x_2514_);
lean_inc_ref(v___x_2513_);
v___x_3540_ = l_Lean_Name_mkStr4(v___x_2513_, v___x_2514_, v___x_2515_, v___x_3539_);
lean_inc(v_cfg_3538_);
v___x_3541_ = l_Lean_Syntax_isOfKind(v_cfg_3538_, v___x_3540_);
lean_dec(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_cfg_3538_);
lean_dec(v___x_3533_);
lean_dec(v_bang_3523_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_3542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3543_ = l_Lean_Syntax_getArg(v___x_3533_, v___x_3492_);
v___x_3544_ = l_Lean_Syntax_getArg(v___x_3533_, v___x_3532_);
v___x_3545_ = l_Lean_Syntax_isNone(v___x_3544_);
if (v___x_3545_ == 0)
{
uint8_t v___x_3546_; 
lean_inc(v___x_3544_);
v___x_3546_ = l_Lean_Syntax_matchesNull(v___x_3544_, v___x_3492_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec(v___x_3544_);
lean_dec(v___x_3543_);
lean_dec(v_cfg_3538_);
lean_dec(v___x_3533_);
lean_dec(v_bang_3523_);
lean_dec(v_tk_2528_);
lean_dec_ref(v___f_2516_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v___x_2513_);
v___x_3547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3547_;
}
else
{
lean_object* v_o_3548_; lean_object* v___x_3549_; 
v_o_3548_ = l_Lean_Syntax_getArg(v___x_3544_, v___x_2527_);
lean_dec(v___x_3544_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_o_3548_);
v___y_3494_ = v___x_3543_;
v___y_3495_ = v___x_3533_;
v___y_3496_ = v_cfg_3538_;
v___y_3497_ = v_bang_3523_;
v___y_3498_ = v___x_3541_;
v_o_3499_ = v___x_3549_;
v___y_3500_ = v___y_3524_;
v___y_3501_ = v___y_3525_;
v___y_3502_ = v___y_3526_;
v___y_3503_ = v___y_3527_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3529_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
goto v___jp_3493_;
}
}
else
{
lean_object* v___x_3550_; 
lean_dec(v___x_3544_);
v___x_3550_ = lean_box(0);
v___y_3494_ = v___x_3543_;
v___y_3495_ = v___x_3533_;
v___y_3496_ = v_cfg_3538_;
v___y_3497_ = v_bang_3523_;
v___y_3498_ = v___x_3541_;
v_o_3499_ = v___x_3550_;
v___y_3500_ = v___y_3524_;
v___y_3501_ = v___y_3525_;
v___y_3502_ = v___y_3526_;
v___y_3503_ = v___y_3527_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3529_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
goto v___jp_3493_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3558_, lean_object* v_stx_3559_, lean_object* v___x_3560_, lean_object* v___x_3561_, lean_object* v___x_3562_, lean_object* v___x_3563_, lean_object* v___f_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
uint8_t v___x_39003__boxed_3574_; uint8_t v___x_39004__boxed_3575_; lean_object* v_res_3576_; 
v___x_39003__boxed_3574_ = lean_unbox(v___x_3558_);
v___x_39004__boxed_3575_ = lean_unbox(v___x_3560_);
v_res_3576_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_39003__boxed_3574_, v_stx_3559_, v___x_39004__boxed_3575_, v___x_3561_, v___x_3562_, v___x_3563_, v___f_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v_stx_3559_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; uint8_t v___x_3598_; lean_object* v___f_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___y_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3596_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3583_);
v___x_3597_ = l_Lean_Syntax_isOfKind(v_stx_3583_, v___x_3596_);
v___x_3598_ = 1;
v___f_3599_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3600_ = lean_box(v___x_3597_);
v___x_3601_ = lean_box(v___x_3598_);
v___y_3602_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3602_, 0, v___x_3600_);
lean_closure_set(v___y_3602_, 1, v_stx_3583_);
lean_closure_set(v___y_3602_, 2, v___x_3601_);
lean_closure_set(v___y_3602_, 3, v___x_3593_);
lean_closure_set(v___y_3602_, 4, v___x_3594_);
lean_closure_set(v___y_3602_, 5, v___x_3595_);
lean_closure_set(v___y_3602_, 6, v___f_3599_);
v___x_3603_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3603_, 0, v___y_3602_);
v___x_3604_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3603_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3616_, lean_object* v_as_3617_, lean_object* v_as_x27_3618_, lean_object* v_b_3619_, lean_object* v_a_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3616_, v_as_x27_3618_, v_b_3619_, v___y_3627_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3631_, lean_object* v_as_3632_, lean_object* v_as_x27_3633_, lean_object* v_b_3634_, lean_object* v_a_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3631_, v_as_3632_, v_as_x27_3633_, v_b_3634_, v_a_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v_as_3632_);
lean_dec(v___x_3631_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3653_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3656_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3657_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3653_, v___x_3654_, v___x_3655_, v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3687_ = l_Lean_addBuiltinDeclarationRanges(v___x_3685_, v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3690_, lean_object* v_simprocs_3691_, lean_object* v_fvarIdsToSimp_3692_, uint8_t v_simplifyTarget_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = lean_unsigned_to_nat(32u);
v___x_3703_ = lean_mk_empty_array_with_capacity(v___x_3702_);
lean_dec_ref(v___x_3703_);
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3705_ = l_Lean_Meta_dsimpGoal(v_a_3701_, v_ctx_3690_, v_simprocs_3691_, v_simplifyTarget_3693_, v_fvarIdsToSimp_3692_, v___x_3704_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v_fst_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
v_fst_3707_ = lean_ctor_get(v_a_3706_, 0);
if (lean_obj_tag(v_fst_3707_) == 0)
{
lean_object* v_snd_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_snd_3708_ = lean_ctor_get(v_a_3706_, 1);
lean_inc(v_snd_3708_);
lean_dec(v_a_3706_);
v___x_3709_ = lean_box(0);
v___x_3710_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3709_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; 
v_unused_3718_ = lean_ctor_get(v___x_3710_, 0);
lean_dec(v_unused_3718_);
v___x_3712_ = v___x_3710_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_dec(v___x_3710_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v_snd_3708_);
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_snd_3708_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_snd_3708_);
v_a_3719_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3710_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3710_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
lean_object* v_snd_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3753_; 
lean_inc_ref(v_fst_3707_);
v_snd_3727_ = lean_ctor_get(v_a_3706_, 1);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_a_3706_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; 
v_unused_3754_ = lean_ctor_get(v_a_3706_, 0);
lean_dec(v_unused_3754_);
v___x_3729_ = v_a_3706_;
v_isShared_3730_ = v_isSharedCheck_3753_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_snd_3727_);
lean_dec(v_a_3706_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3753_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v_val_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
v_val_3731_ = lean_ctor_get(v_fst_3707_, 0);
lean_inc(v_val_3731_);
lean_dec_ref(v_fst_3707_);
v___x_3732_ = lean_box(0);
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 1);
lean_ctor_set(v___x_3729_, 1, v___x_3732_);
lean_ctor_set(v___x_3729_, 0, v_val_3731_);
v___x_3734_ = v___x_3729_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_val_3731_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3734_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3743_);
v___x_3737_ = v___x_3735_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v___x_3735_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_snd_3727_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_snd_3727_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec(v_snd_3727_);
v_a_3744_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3735_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3735_);
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
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
v_a_3755_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3705_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3705_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec_ref(v_fvarIdsToSimp_3692_);
lean_dec_ref(v_simprocs_3691_);
lean_dec_ref(v_ctx_3690_);
v_a_3763_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3700_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3700_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3771_, lean_object* v_simprocs_3772_, lean_object* v_fvarIdsToSimp_3773_, lean_object* v_simplifyTarget_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
uint8_t v_simplifyTarget_boxed_3781_; lean_object* v_res_3782_; 
v_simplifyTarget_boxed_3781_ = lean_unbox(v_simplifyTarget_3774_);
v_res_3782_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3771_, v_simprocs_3772_, v_fvarIdsToSimp_3773_, v_simplifyTarget_boxed_3781_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3783_, lean_object* v_simprocs_3784_, lean_object* v_fvarIdsToSimp_3785_, uint8_t v_simplifyTarget_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3783_, v_simprocs_3784_, v_fvarIdsToSimp_3785_, v_simplifyTarget_3786_, v_a_3788_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3797_, lean_object* v_simprocs_3798_, lean_object* v_fvarIdsToSimp_3799_, lean_object* v_simplifyTarget_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
uint8_t v_simplifyTarget_boxed_3810_; lean_object* v_res_3811_; 
v_simplifyTarget_boxed_3810_ = lean_unbox(v_simplifyTarget_3800_);
v_res_3811_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3797_, v_simprocs_3798_, v_fvarIdsToSimp_3799_, v_simplifyTarget_boxed_3810_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3812_, lean_object* v_simprocs_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3815_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3825_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = l_Lean_MVarId_getNondepPropHyps(v_a_3824_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = 1;
v___x_3828_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3812_, v_simprocs_3813_, v_a_3826_, v___x_3827_, v___y_3815_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3828_;
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v_simprocs_3813_);
lean_dec_ref(v_ctx_3812_);
v_a_3829_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3825_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3825_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_simprocs_3813_);
lean_dec_ref(v_ctx_3812_);
v_a_3837_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3823_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3823_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3845_, lean_object* v_simprocs_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3845_, v_simprocs_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3857_, lean_object* v_ctx_3858_, lean_object* v_simprocs_3859_, uint8_t v_type_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3857_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3858_, v_simprocs_3859_, v_a_3871_, v_type_3860_, v___y_3862_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3872_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v_simprocs_3859_);
lean_dec_ref(v_ctx_3858_);
v_a_3873_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3870_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3870_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3881_, lean_object* v_ctx_3882_, lean_object* v_simprocs_3883_, lean_object* v_type_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
uint8_t v_type_635__boxed_3894_; lean_object* v_res_3895_; 
v_type_635__boxed_3894_ = lean_unbox(v_type_3884_);
v_res_3895_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3881_, v_ctx_3882_, v_simprocs_3883_, v_type_635__boxed_3894_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3896_, lean_object* v_simprocs_3897_, lean_object* v_loc_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
if (lean_obj_tag(v_loc_3898_) == 0)
{
lean_object* v___f_3908_; lean_object* v___x_3909_; 
v___f_3908_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3908_, 0, v_ctx_3896_);
lean_closure_set(v___f_3908_, 1, v_simprocs_3897_);
v___x_3909_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3908_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3909_;
}
else
{
lean_object* v_hypotheses_3910_; uint8_t v_type_3911_; lean_object* v___x_3912_; lean_object* v___f_3913_; lean_object* v___x_3914_; 
v_hypotheses_3910_ = lean_ctor_get(v_loc_3898_, 0);
lean_inc_ref(v_hypotheses_3910_);
v_type_3911_ = lean_ctor_get_uint8(v_loc_3898_, sizeof(void*)*1);
lean_dec_ref(v_loc_3898_);
v___x_3912_ = lean_box(v_type_3911_);
v___f_3913_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3913_, 0, v_hypotheses_3910_);
lean_closure_set(v___f_3913_, 1, v_ctx_3896_);
lean_closure_set(v___f_3913_, 2, v_simprocs_3897_);
lean_closure_set(v___f_3913_, 3, v___x_3912_);
v___x_3914_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3913_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3915_, lean_object* v_simprocs_3916_, lean_object* v_loc_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3915_, v_simprocs_3916_, v_loc_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3932_, lean_object* v_stx_3933_, uint8_t v___x_3934_, lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v___x_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
if (v___x_3932_ == 0)
{
lean_object* v___x_3947_; 
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_3947_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; lean_object* v_tk_3949_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; uint8_t v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v_stx_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; uint8_t v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4123_; uint8_t v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4155_; uint8_t v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4180_; uint8_t v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; uint8_t v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; uint8_t v___y_4253_; uint8_t v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; uint8_t v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v_args_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___x_4329_; uint8_t v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v_o_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v_bang_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_3948_ = lean_unsigned_to_nat(0u);
v_tk_3949_ = l_Lean_Syntax_getArg(v_stx_3933_, v___x_3948_);
v___x_4329_ = lean_unsigned_to_nat(1u);
v___x_4386_ = l_Lean_Syntax_getArg(v_stx_3933_, v___x_4329_);
v___x_4387_ = l_Lean_Syntax_isNone(v___x_4386_);
if (v___x_4387_ == 0)
{
uint8_t v___x_4388_; 
lean_inc(v___x_4386_);
v___x_4388_ = l_Lean_Syntax_matchesNull(v___x_4386_, v___x_4329_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; 
lean_dec(v___x_4386_);
lean_dec(v_tk_3949_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_4389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4389_;
}
else
{
lean_object* v_bang_4390_; lean_object* v___x_4391_; 
v_bang_4390_ = l_Lean_Syntax_getArg(v___x_4386_, v___x_3948_);
lean_dec(v___x_4386_);
v___x_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4391_, 0, v_bang_4390_);
v_bang_4359_ = v___x_4391_;
v___y_4360_ = v___y_3938_;
v___y_4361_ = v___y_3939_;
v___y_4362_ = v___y_3940_;
v___y_4363_ = v___y_3941_;
v___y_4364_ = v___y_3942_;
v___y_4365_ = v___y_3943_;
v___y_4366_ = v___y_3944_;
v___y_4367_ = v___y_3945_;
goto v___jp_4358_;
}
}
else
{
lean_object* v___x_4392_; 
lean_dec(v___x_4386_);
v___x_4392_ = lean_box(0);
v_bang_4359_ = v___x_4392_;
v___y_4360_ = v___y_3938_;
v___y_4361_ = v___y_3939_;
v___y_4362_ = v___y_3940_;
v___y_4363_ = v___y_3941_;
v___y_4364_ = v___y_3942_;
v___y_4365_ = v___y_3943_;
v___y_4366_ = v___y_3944_;
v___y_4367_ = v___y_3945_;
goto v___jp_4358_;
}
v___jp_3950_:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3960_, v___y_3961_, v___y_3962_, v___y_3957_, v___y_3956_, v___y_3959_, v___y_3951_, v___y_3955_, v___y_3954_, v___y_3953_, v___y_3958_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v_usedTheorems_3965_; lean_object* v_diag_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4007_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3963_);
v_usedTheorems_3965_ = lean_ctor_get(v_a_3964_, 0);
v_diag_3966_ = lean_ctor_get(v_a_3964_, 1);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_a_3964_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3968_ = v_a_3964_;
v_isShared_3969_ = v_isSharedCheck_4007_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_diag_3966_);
lean_inc(v_usedTheorems_3965_);
lean_dec(v_a_3964_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4007_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3952_, v_usedTheorems_3965_, v___y_3955_, v___y_3954_, v___y_3953_, v___y_3958_);
lean_dec_ref(v_usedTheorems_3965_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v_ref_3972_; lean_object* v___x_3973_; lean_object* v___x_3975_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3970_);
v_ref_3972_ = lean_ctor_get(v___y_3953_, 5);
v___x_3973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 1, v_a_3971_);
lean_ctor_set(v___x_3968_, 0, v___x_3973_);
v___x_3975_ = v___x_3968_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_a_3971_);
v___x_3975_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
lean_ctor_set(v___x_3977_, 2, v___x_3976_);
lean_ctor_set(v___x_3977_, 3, v___x_3976_);
lean_ctor_set(v___x_3977_, 4, v___x_3976_);
lean_ctor_set(v___x_3977_, 5, v___x_3976_);
lean_inc(v_ref_3972_);
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v_ref_3972_);
v___x_3979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3980_ = 4;
v___x_3981_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3949_, v___x_3977_, v___x_3978_, v___x_3979_, v___x_3976_, v___x_3980_, v___y_3953_, v___y_3958_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3981_, 0);
lean_dec(v_unused_3989_);
v___x_3983_ = v___x_3981_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_dec(v___x_3981_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v_diag_3966_);
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_diag_3966_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec_ref(v_diag_3966_);
v_a_3990_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3981_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3981_);
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
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_del_object(v___x_3968_);
lean_dec_ref(v_diag_3966_);
lean_dec(v_tk_3949_);
v_a_3999_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3970_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3970_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v___y_3952_);
lean_dec(v_tk_3949_);
v_a_4008_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3963_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3963_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
v___jp_4016_:
{
if (lean_obj_tag(v___y_4024_) == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4030_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*1, v___x_3934_);
v___y_3951_ = v___y_4017_;
v___y_3952_ = v___y_4018_;
v___y_3953_ = v___y_4019_;
v___y_3954_ = v___y_4022_;
v___y_3955_ = v___y_4021_;
v___y_3956_ = v___y_4020_;
v___y_3957_ = v___y_4023_;
v___y_3958_ = v___y_4026_;
v___y_3959_ = v___y_4025_;
v___y_3960_ = v___y_4028_;
v___y_3961_ = v___y_4027_;
v___y_3962_ = v___x_4030_;
goto v___jp_3950_;
}
else
{
lean_object* v_val_4031_; lean_object* v___x_4032_; 
v_val_4031_ = lean_ctor_get(v___y_4024_, 0);
lean_inc(v_val_4031_);
lean_dec_ref(v___y_4024_);
v___x_4032_ = l_Lean_Elab_Tactic_expandLocation(v_val_4031_);
lean_dec(v_val_4031_);
v___y_3951_ = v___y_4017_;
v___y_3952_ = v___y_4018_;
v___y_3953_ = v___y_4019_;
v___y_3954_ = v___y_4022_;
v___y_3955_ = v___y_4021_;
v___y_3956_ = v___y_4020_;
v___y_3957_ = v___y_4023_;
v___y_3958_ = v___y_4026_;
v___y_3959_ = v___y_4025_;
v___y_3960_ = v___y_4028_;
v___y_3961_ = v___y_4027_;
v___y_3962_ = v___x_4032_;
goto v___jp_3950_;
}
}
v___jp_4033_:
{
uint8_t v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4046_ = 0;
v___x_4047_ = 2;
v___x_4048_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4049_ = lean_box(v___x_4046_);
v___x_4050_ = lean_box(v___x_4047_);
v___x_4051_ = lean_box(v___x_4046_);
lean_inc(v_stx_4037_);
v___x_4052_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4052_, 0, v_stx_4037_);
lean_closure_set(v___x_4052_, 1, v___x_4049_);
lean_closure_set(v___x_4052_, 2, v___x_4050_);
lean_closure_set(v___x_4052_, 3, v___x_4051_);
lean_closure_set(v___x_4052_, 4, v___x_4048_);
v___x_4053_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4052_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
if (lean_obj_tag(v___y_4035_) == 0)
{
lean_object* v_ctx_4055_; lean_object* v_simprocs_4056_; 
v_ctx_4055_ = lean_ctor_get(v_a_4054_, 0);
lean_inc_ref(v_ctx_4055_);
v_simprocs_4056_ = lean_ctor_get(v_a_4054_, 1);
lean_inc_ref(v_simprocs_4056_);
lean_dec(v_a_4054_);
v___y_4017_ = v___y_4041_;
v___y_4018_ = v_stx_4037_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4039_;
v___y_4021_ = v___y_4042_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4038_;
v___y_4024_ = v___y_4036_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4045_;
v___y_4027_ = v_simprocs_4056_;
v___y_4028_ = v_ctx_4055_;
goto v___jp_4016_;
}
else
{
lean_dec_ref(v___y_4035_);
if (v___y_4034_ == 0)
{
lean_object* v_ctx_4057_; lean_object* v_simprocs_4058_; 
v_ctx_4057_ = lean_ctor_get(v_a_4054_, 0);
lean_inc_ref(v_ctx_4057_);
v_simprocs_4058_ = lean_ctor_get(v_a_4054_, 1);
lean_inc_ref(v_simprocs_4058_);
lean_dec(v_a_4054_);
v___y_4017_ = v___y_4041_;
v___y_4018_ = v_stx_4037_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4039_;
v___y_4021_ = v___y_4042_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4038_;
v___y_4024_ = v___y_4036_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4045_;
v___y_4027_ = v_simprocs_4058_;
v___y_4028_ = v_ctx_4057_;
goto v___jp_4016_;
}
else
{
lean_object* v_ctx_4059_; lean_object* v_simprocs_4060_; lean_object* v___x_4061_; 
v_ctx_4059_ = lean_ctor_get(v_a_4054_, 0);
lean_inc_ref(v_ctx_4059_);
v_simprocs_4060_ = lean_ctor_get(v_a_4054_, 1);
lean_inc_ref(v_simprocs_4060_);
lean_dec(v_a_4054_);
v___x_4061_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4059_);
v___y_4017_ = v___y_4041_;
v___y_4018_ = v_stx_4037_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4039_;
v___y_4021_ = v___y_4042_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4038_;
v___y_4024_ = v___y_4036_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4045_;
v___y_4027_ = v_simprocs_4060_;
v___y_4028_ = v___x_4061_;
goto v___jp_4016_;
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_stx_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v_tk_3949_);
v_a_4062_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4053_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4053_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
v___jp_4070_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_inc_ref(v___y_4085_);
v___x_4092_ = l_Array_append___redArg(v___y_4085_, v___y_4091_);
lean_dec_ref(v___y_4091_);
lean_inc(v___y_4079_);
lean_inc(v___y_4072_);
v___x_4093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4093_, 0, v___y_4072_);
lean_ctor_set(v___x_4093_, 1, v___y_4079_);
lean_ctor_set(v___x_4093_, 2, v___x_4092_);
v___x_4094_ = l_Lean_Syntax_node6(v___y_4072_, v___y_4084_, v___y_4078_, v___y_4086_, v___y_4075_, v___y_4082_, v___y_4087_, v___x_4093_);
v___y_4034_ = v___y_4071_;
v___y_4035_ = v___y_4081_;
v___y_4036_ = v___y_4073_;
v_stx_4037_ = v___x_4094_;
v___y_4038_ = v___y_4074_;
v___y_4039_ = v___y_4080_;
v___y_4040_ = v___y_4088_;
v___y_4041_ = v___y_4090_;
v___y_4042_ = v___y_4083_;
v___y_4043_ = v___y_4077_;
v___y_4044_ = v___y_4089_;
v___y_4045_ = v___y_4076_;
goto v___jp_4033_;
}
v___jp_4095_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_inc_ref(v___y_4111_);
v___x_4116_ = l_Array_append___redArg(v___y_4111_, v___y_4115_);
lean_dec_ref(v___y_4115_);
lean_inc(v___y_4104_);
lean_inc(v___y_4096_);
v___x_4117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4117_, 0, v___y_4096_);
lean_ctor_set(v___x_4117_, 1, v___y_4104_);
lean_ctor_set(v___x_4117_, 2, v___x_4116_);
if (lean_obj_tag(v___y_4098_) == 0)
{
lean_object* v___x_4118_; 
v___x_4118_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4071_ = v___y_4097_;
v___y_4072_ = v___y_4096_;
v___y_4073_ = v___y_4098_;
v___y_4074_ = v___y_4099_;
v___y_4075_ = v___y_4100_;
v___y_4076_ = v___y_4101_;
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4107_;
v___y_4082_ = v___y_4106_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4111_;
v___y_4086_ = v___y_4110_;
v___y_4087_ = v___x_4117_;
v___y_4088_ = v___y_4112_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4113_;
v___y_4091_ = v___x_4118_;
goto v___jp_4070_;
}
else
{
lean_object* v_val_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v_val_4119_ = lean_ctor_get(v___y_4098_, 0);
v___x_4120_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4119_);
v___x_4121_ = lean_array_push(v___x_4120_, v_val_4119_);
v___y_4071_ = v___y_4097_;
v___y_4072_ = v___y_4096_;
v___y_4073_ = v___y_4098_;
v___y_4074_ = v___y_4099_;
v___y_4075_ = v___y_4100_;
v___y_4076_ = v___y_4101_;
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4107_;
v___y_4082_ = v___y_4106_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4111_;
v___y_4086_ = v___y_4110_;
v___y_4087_ = v___x_4117_;
v___y_4088_ = v___y_4112_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4113_;
v___y_4091_ = v___x_4121_;
goto v___jp_4070_;
}
}
v___jp_4122_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_inc_ref(v___y_4138_);
v___x_4143_ = l_Array_append___redArg(v___y_4138_, v___y_4142_);
lean_dec_ref(v___y_4142_);
lean_inc(v___y_4131_);
lean_inc(v___y_4123_);
v___x_4144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4144_, 0, v___y_4123_);
lean_ctor_set(v___x_4144_, 1, v___y_4131_);
lean_ctor_set(v___x_4144_, 2, v___x_4143_);
if (lean_obj_tag(v___y_4133_) == 1)
{
lean_object* v_val_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_val_4145_ = lean_ctor_get(v___y_4133_, 0);
lean_inc(v_val_4145_);
lean_dec_ref(v___y_4133_);
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4123_, 3);
v___x_4147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___y_4123_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
lean_inc_ref(v___y_4138_);
v___x_4148_ = l_Array_append___redArg(v___y_4138_, v_val_4145_);
lean_dec(v_val_4145_);
lean_inc(v___y_4131_);
v___x_4149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4149_, 0, v___y_4123_);
lean_ctor_set(v___x_4149_, 1, v___y_4131_);
lean_ctor_set(v___x_4149_, 2, v___x_4148_);
v___x_4150_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___y_4123_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = l_Array_mkArray3___redArg(v___x_4147_, v___x_4149_, v___x_4151_);
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___y_4124_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
v___y_4106_ = v___x_4144_;
v___y_4107_ = v___y_4134_;
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4136_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4138_;
v___y_4112_ = v___y_4139_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___x_4152_;
goto v___jp_4095_;
}
else
{
lean_object* v___x_4153_; 
lean_dec(v___y_4133_);
v___x_4153_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___y_4124_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
v___y_4105_ = v___y_4132_;
v___y_4106_ = v___x_4144_;
v___y_4107_ = v___y_4134_;
v___y_4108_ = v___y_4135_;
v___y_4109_ = v___y_4136_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4138_;
v___y_4112_ = v___y_4139_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___x_4153_;
goto v___jp_4095_;
}
}
v___jp_4154_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_inc_ref(v___y_4155_);
v___x_4176_ = l_Array_append___redArg(v___y_4155_, v___y_4175_);
lean_dec_ref(v___y_4175_);
lean_inc(v___y_4159_);
lean_inc(v___y_4168_);
v___x_4177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___y_4168_);
lean_ctor_set(v___x_4177_, 1, v___y_4159_);
lean_ctor_set(v___x_4177_, 2, v___x_4176_);
v___x_4178_ = l_Lean_Syntax_node6(v___y_4168_, v___y_4170_, v___y_4162_, v___y_4171_, v___y_4157_, v___y_4158_, v___y_4165_, v___x_4177_);
v___y_4034_ = v___y_4156_;
v___y_4035_ = v___y_4167_;
v___y_4036_ = v___y_4160_;
v_stx_4037_ = v___x_4178_;
v___y_4038_ = v___y_4161_;
v___y_4039_ = v___y_4166_;
v___y_4040_ = v___y_4172_;
v___y_4041_ = v___y_4174_;
v___y_4042_ = v___y_4169_;
v___y_4043_ = v___y_4164_;
v___y_4044_ = v___y_4173_;
v___y_4045_ = v___y_4163_;
goto v___jp_4033_;
}
v___jp_4179_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
lean_inc_ref(v___y_4180_);
v___x_4200_ = l_Array_append___redArg(v___y_4180_, v___y_4199_);
lean_dec_ref(v___y_4199_);
lean_inc(v___y_4184_);
lean_inc(v___y_4192_);
v___x_4201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4201_, 0, v___y_4192_);
lean_ctor_set(v___x_4201_, 1, v___y_4184_);
lean_ctor_set(v___x_4201_, 2, v___x_4200_);
if (lean_obj_tag(v___y_4185_) == 0)
{
lean_object* v___x_4202_; 
v___x_4202_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4155_ = v___y_4180_;
v___y_4156_ = v___y_4181_;
v___y_4157_ = v___y_4182_;
v___y_4158_ = v___y_4183_;
v___y_4159_ = v___y_4184_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___y_4189_;
v___y_4165_ = v___x_4201_;
v___y_4166_ = v___y_4190_;
v___y_4167_ = v___y_4191_;
v___y_4168_ = v___y_4192_;
v___y_4169_ = v___y_4193_;
v___y_4170_ = v___y_4194_;
v___y_4171_ = v___y_4195_;
v___y_4172_ = v___y_4196_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4197_;
v___y_4175_ = v___x_4202_;
goto v___jp_4154_;
}
else
{
lean_object* v_val_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_val_4203_ = lean_ctor_get(v___y_4185_, 0);
v___x_4204_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4203_);
v___x_4205_ = lean_array_push(v___x_4204_, v_val_4203_);
v___y_4155_ = v___y_4180_;
v___y_4156_ = v___y_4181_;
v___y_4157_ = v___y_4182_;
v___y_4158_ = v___y_4183_;
v___y_4159_ = v___y_4184_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___y_4189_;
v___y_4165_ = v___x_4201_;
v___y_4166_ = v___y_4190_;
v___y_4167_ = v___y_4191_;
v___y_4168_ = v___y_4192_;
v___y_4169_ = v___y_4193_;
v___y_4170_ = v___y_4194_;
v___y_4171_ = v___y_4195_;
v___y_4172_ = v___y_4196_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4197_;
v___y_4175_ = v___x_4205_;
goto v___jp_4154_;
}
}
v___jp_4206_:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_inc_ref(v___y_4207_);
v___x_4227_ = l_Array_append___redArg(v___y_4207_, v___y_4226_);
lean_dec_ref(v___y_4226_);
lean_inc(v___y_4210_);
lean_inc(v___y_4218_);
v___x_4228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4228_, 0, v___y_4218_);
lean_ctor_set(v___x_4228_, 1, v___y_4210_);
lean_ctor_set(v___x_4228_, 2, v___x_4227_);
if (lean_obj_tag(v___y_4217_) == 1)
{
lean_object* v_val_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_val_4229_ = lean_ctor_get(v___y_4217_, 0);
lean_inc(v_val_4229_);
lean_dec_ref(v___y_4217_);
v___x_4230_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4218_, 3);
v___x_4231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___y_4218_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
lean_inc_ref(v___y_4207_);
v___x_4232_ = l_Array_append___redArg(v___y_4207_, v_val_4229_);
lean_dec(v_val_4229_);
lean_inc(v___y_4210_);
v___x_4233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4233_, 0, v___y_4218_);
lean_ctor_set(v___x_4233_, 1, v___y_4210_);
lean_ctor_set(v___x_4233_, 2, v___x_4232_);
v___x_4234_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___y_4218_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = l_Array_mkArray3___redArg(v___x_4231_, v___x_4233_, v___x_4235_);
v___y_4180_ = v___y_4207_;
v___y_4181_ = v___y_4208_;
v___y_4182_ = v___y_4209_;
v___y_4183_ = v___x_4228_;
v___y_4184_ = v___y_4210_;
v___y_4185_ = v___y_4211_;
v___y_4186_ = v___y_4212_;
v___y_4187_ = v___y_4213_;
v___y_4188_ = v___y_4214_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___y_4216_;
v___y_4191_ = v___y_4219_;
v___y_4192_ = v___y_4218_;
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4221_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
v___y_4198_ = v___y_4224_;
v___y_4199_ = v___x_4236_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4237_; 
lean_dec(v___y_4217_);
v___x_4237_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4180_ = v___y_4207_;
v___y_4181_ = v___y_4208_;
v___y_4182_ = v___y_4209_;
v___y_4183_ = v___x_4228_;
v___y_4184_ = v___y_4210_;
v___y_4185_ = v___y_4211_;
v___y_4186_ = v___y_4212_;
v___y_4187_ = v___y_4213_;
v___y_4188_ = v___y_4214_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___y_4216_;
v___y_4191_ = v___y_4219_;
v___y_4192_ = v___y_4218_;
v___y_4193_ = v___y_4220_;
v___y_4194_ = v___y_4221_;
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
v___y_4198_ = v___y_4224_;
v___y_4199_ = v___x_4237_;
goto v___jp_4179_;
}
}
v___jp_4238_:
{
lean_object* v_ref_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_ref_4254_ = lean_ctor_get(v___y_4252_, 5);
v___x_4255_ = l_Lean_SourceInfo_fromRef(v_ref_4254_, v___y_4253_);
v___x_4256_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4257_ = l_Lean_Name_mkStr4(v___x_3935_, v___x_3936_, v___x_3937_, v___x_4256_);
v___x_4258_ = l_Lean_SourceInfo_fromRef(v_tk_3949_, v___x_3934_);
v___x_4259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
lean_ctor_set(v___x_4259_, 1, v___x_4256_);
v___x_4260_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4261_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4255_);
v___x_4262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4255_);
lean_ctor_set(v___x_4262_, 1, v___x_4260_);
lean_ctor_set(v___x_4262_, 2, v___x_4261_);
if (lean_obj_tag(v___y_4240_) == 1)
{
lean_object* v_val_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v_val_4263_ = lean_ctor_get(v___y_4240_, 0);
lean_inc(v_val_4263_);
lean_dec_ref(v___y_4240_);
v___x_4264_ = l_Lean_SourceInfo_fromRef(v_val_4263_, v___x_3934_);
lean_dec(v_val_4263_);
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4264_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = l_Array_mkArray1___redArg(v___x_4266_);
v___y_4123_ = v___x_4255_;
v___y_4124_ = v___y_4239_;
v___y_4125_ = v___y_4241_;
v___y_4126_ = v___y_4242_;
v___y_4127_ = v___x_4262_;
v___y_4128_ = v___y_4243_;
v___y_4129_ = v___y_4244_;
v___y_4130_ = v___x_4259_;
v___y_4131_ = v___x_4260_;
v___y_4132_ = v___y_4245_;
v___y_4133_ = v___y_4246_;
v___y_4134_ = v___y_4247_;
v___y_4135_ = v___y_4248_;
v___y_4136_ = v___x_4257_;
v___y_4137_ = v___y_4249_;
v___y_4138_ = v___x_4261_;
v___y_4139_ = v___y_4250_;
v___y_4140_ = v___y_4252_;
v___y_4141_ = v___y_4251_;
v___y_4142_ = v___x_4267_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4268_; 
lean_dec(v___y_4240_);
v___x_4268_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4123_ = v___x_4255_;
v___y_4124_ = v___y_4239_;
v___y_4125_ = v___y_4241_;
v___y_4126_ = v___y_4242_;
v___y_4127_ = v___x_4262_;
v___y_4128_ = v___y_4243_;
v___y_4129_ = v___y_4244_;
v___y_4130_ = v___x_4259_;
v___y_4131_ = v___x_4260_;
v___y_4132_ = v___y_4245_;
v___y_4133_ = v___y_4246_;
v___y_4134_ = v___y_4247_;
v___y_4135_ = v___y_4248_;
v___y_4136_ = v___x_4257_;
v___y_4137_ = v___y_4249_;
v___y_4138_ = v___x_4261_;
v___y_4139_ = v___y_4250_;
v___y_4140_ = v___y_4252_;
v___y_4141_ = v___y_4251_;
v___y_4142_ = v___x_4268_;
goto v___jp_4122_;
}
}
v___jp_4269_:
{
if (lean_obj_tag(v___y_4277_) == 0)
{
uint8_t v___x_4284_; 
v___x_4284_ = 0;
v___y_4239_ = v___y_4270_;
v___y_4240_ = v___y_4271_;
v___y_4241_ = v___y_4283_;
v___y_4242_ = v___y_4272_;
v___y_4243_ = v___y_4273_;
v___y_4244_ = v___y_4274_;
v___y_4245_ = v___y_4275_;
v___y_4246_ = v___y_4276_;
v___y_4247_ = v___y_4277_;
v___y_4248_ = v___y_4278_;
v___y_4249_ = v___y_4279_;
v___y_4250_ = v___y_4280_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4281_;
v___y_4253_ = v___x_4284_;
goto v___jp_4238_;
}
else
{
if (v___y_4270_ == 0)
{
v___y_4239_ = v___y_4270_;
v___y_4240_ = v___y_4271_;
v___y_4241_ = v___y_4283_;
v___y_4242_ = v___y_4272_;
v___y_4243_ = v___y_4273_;
v___y_4244_ = v___y_4274_;
v___y_4245_ = v___y_4275_;
v___y_4246_ = v___y_4276_;
v___y_4247_ = v___y_4277_;
v___y_4248_ = v___y_4278_;
v___y_4249_ = v___y_4279_;
v___y_4250_ = v___y_4280_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4281_;
v___y_4253_ = v___y_4270_;
goto v___jp_4238_;
}
else
{
lean_object* v_ref_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_ref_4285_ = lean_ctor_get(v___y_4281_, 5);
v___x_4286_ = 0;
v___x_4287_ = l_Lean_SourceInfo_fromRef(v_ref_4285_, v___x_4286_);
v___x_4288_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4289_ = l_Lean_Name_mkStr4(v___x_3935_, v___x_3936_, v___x_3937_, v___x_4288_);
v___x_4290_ = l_Lean_SourceInfo_fromRef(v_tk_3949_, v___x_3934_);
v___x_4291_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4294_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4287_);
v___x_4295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4287_);
lean_ctor_set(v___x_4295_, 1, v___x_4293_);
lean_ctor_set(v___x_4295_, 2, v___x_4294_);
if (lean_obj_tag(v___y_4271_) == 1)
{
lean_object* v_val_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v_val_4296_ = lean_ctor_get(v___y_4271_, 0);
lean_inc(v_val_4296_);
lean_dec_ref(v___y_4271_);
v___x_4297_ = l_Lean_SourceInfo_fromRef(v_val_4296_, v___x_3934_);
lean_dec(v_val_4296_);
v___x_4298_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = l_Array_mkArray1___redArg(v___x_4299_);
v___y_4207_ = v___x_4294_;
v___y_4208_ = v___y_4270_;
v___y_4209_ = v___x_4295_;
v___y_4210_ = v___x_4293_;
v___y_4211_ = v___y_4283_;
v___y_4212_ = v___y_4272_;
v___y_4213_ = v___x_4292_;
v___y_4214_ = v___y_4273_;
v___y_4215_ = v___y_4274_;
v___y_4216_ = v___y_4275_;
v___y_4217_ = v___y_4276_;
v___y_4218_ = v___x_4287_;
v___y_4219_ = v___y_4277_;
v___y_4220_ = v___y_4278_;
v___y_4221_ = v___x_4289_;
v___y_4222_ = v___y_4279_;
v___y_4223_ = v___y_4280_;
v___y_4224_ = v___y_4281_;
v___y_4225_ = v___y_4282_;
v___y_4226_ = v___x_4300_;
goto v___jp_4206_;
}
else
{
lean_object* v___x_4301_; 
lean_dec(v___y_4271_);
v___x_4301_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4207_ = v___x_4294_;
v___y_4208_ = v___y_4270_;
v___y_4209_ = v___x_4295_;
v___y_4210_ = v___x_4293_;
v___y_4211_ = v___y_4283_;
v___y_4212_ = v___y_4272_;
v___y_4213_ = v___x_4292_;
v___y_4214_ = v___y_4273_;
v___y_4215_ = v___y_4274_;
v___y_4216_ = v___y_4275_;
v___y_4217_ = v___y_4276_;
v___y_4218_ = v___x_4287_;
v___y_4219_ = v___y_4277_;
v___y_4220_ = v___y_4278_;
v___y_4221_ = v___x_4289_;
v___y_4222_ = v___y_4279_;
v___y_4223_ = v___y_4280_;
v___y_4224_ = v___y_4281_;
v___y_4225_ = v___y_4282_;
v___y_4226_ = v___x_4301_;
goto v___jp_4206_;
}
}
}
}
v___jp_4302_:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4317_ = lean_unsigned_to_nat(3u);
v___x_4318_ = l_Lean_Syntax_getArg(v___y_4305_, v___x_4317_);
lean_dec(v___y_4305_);
v___x_4319_ = l_Lean_Syntax_getOptional_x3f(v___x_4318_);
lean_dec(v___x_4318_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_box(0);
v___y_4270_ = v___y_4303_;
v___y_4271_ = v___y_4307_;
v___y_4272_ = v___y_4309_;
v___y_4273_ = v___y_4316_;
v___y_4274_ = v___y_4314_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v_args_4308_;
v___y_4277_ = v___y_4304_;
v___y_4278_ = v___y_4313_;
v___y_4279_ = v___y_4306_;
v___y_4280_ = v___y_4311_;
v___y_4281_ = v___y_4315_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___x_4320_;
goto v___jp_4269_;
}
else
{
lean_object* v_val_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
v_val_4321_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4319_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_val_4321_);
lean_dec(v___x_4319_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_val_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
v___y_4270_ = v___y_4303_;
v___y_4271_ = v___y_4307_;
v___y_4272_ = v___y_4309_;
v___y_4273_ = v___y_4316_;
v___y_4274_ = v___y_4314_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v_args_4308_;
v___y_4277_ = v___y_4304_;
v___y_4278_ = v___y_4313_;
v___y_4279_ = v___y_4306_;
v___y_4280_ = v___y_4311_;
v___y_4281_ = v___y_4315_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___x_4326_;
goto v___jp_4269_;
}
}
}
}
v___jp_4330_:
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = l_Lean_Syntax_getArg(v___y_4334_, v___y_4333_);
v___x_4346_ = l_Lean_Syntax_isNone(v___x_4345_);
if (v___x_4346_ == 0)
{
uint8_t v___x_4347_; 
lean_inc(v___x_4345_);
v___x_4347_ = l_Lean_Syntax_matchesNull(v___x_4345_, v___x_4329_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; 
lean_dec(v___x_4345_);
lean_dec(v_o_4336_);
lean_dec(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec(v___y_4332_);
lean_dec(v_tk_3949_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_4348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4349_ = l_Lean_Syntax_getArg(v___x_4345_, v___x_3948_);
lean_dec(v___x_4345_);
v___x_4350_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3937_);
lean_inc_ref(v___x_3936_);
lean_inc_ref(v___x_3935_);
v___x_4351_ = l_Lean_Name_mkStr4(v___x_3935_, v___x_3936_, v___x_3937_, v___x_4350_);
lean_inc(v___x_4349_);
v___x_4352_ = l_Lean_Syntax_isOfKind(v___x_4349_, v___x_4351_);
lean_dec(v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; 
lean_dec(v___x_4349_);
lean_dec(v_o_4336_);
lean_dec(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec(v___y_4332_);
lean_dec(v_tk_3949_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_4353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4353_;
}
else
{
lean_object* v___x_4354_; lean_object* v_args_4355_; lean_object* v___x_4356_; 
v___x_4354_ = l_Lean_Syntax_getArg(v___x_4349_, v___x_4329_);
lean_dec(v___x_4349_);
v_args_4355_ = l_Lean_Syntax_getArgs(v___x_4354_);
lean_dec(v___x_4354_);
v___x_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4356_, 0, v_args_4355_);
v___y_4303_ = v___y_4331_;
v___y_4304_ = v___y_4332_;
v___y_4305_ = v___y_4334_;
v___y_4306_ = v___y_4335_;
v___y_4307_ = v_o_4336_;
v_args_4308_ = v___x_4356_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___y_4340_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4342_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
goto v___jp_4302_;
}
}
}
else
{
lean_object* v___x_4357_; 
lean_dec(v___x_4345_);
v___x_4357_ = lean_box(0);
v___y_4303_ = v___y_4331_;
v___y_4304_ = v___y_4332_;
v___y_4305_ = v___y_4334_;
v___y_4306_ = v___y_4335_;
v___y_4307_ = v_o_4336_;
v_args_4308_ = v___x_4357_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___y_4340_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4342_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
goto v___jp_4302_;
}
}
v___jp_4358_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; uint8_t v___x_4372_; 
v___x_4368_ = lean_unsigned_to_nat(2u);
v___x_4369_ = l_Lean_Syntax_getArg(v_stx_3933_, v___x_4368_);
v___x_4370_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3937_);
lean_inc_ref(v___x_3936_);
lean_inc_ref(v___x_3935_);
v___x_4371_ = l_Lean_Name_mkStr4(v___x_3935_, v___x_3936_, v___x_3937_, v___x_4370_);
lean_inc(v___x_4369_);
v___x_4372_ = l_Lean_Syntax_isOfKind(v___x_4369_, v___x_4371_);
lean_dec(v___x_4371_);
if (v___x_4372_ == 0)
{
lean_object* v___x_4373_; 
lean_dec(v___x_4369_);
lean_dec(v_bang_4359_);
lean_dec(v_tk_3949_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_4373_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4373_;
}
else
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4374_ = l_Lean_Syntax_getArg(v___x_4369_, v___x_3948_);
v___x_4375_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3937_);
lean_inc_ref(v___x_3936_);
lean_inc_ref(v___x_3935_);
v___x_4376_ = l_Lean_Name_mkStr4(v___x_3935_, v___x_3936_, v___x_3937_, v___x_4375_);
lean_inc(v___x_4374_);
v___x_4377_ = l_Lean_Syntax_isOfKind(v___x_4374_, v___x_4376_);
lean_dec(v___x_4376_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; 
lean_dec(v___x_4374_);
lean_dec(v___x_4369_);
lean_dec(v_bang_4359_);
lean_dec(v_tk_3949_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_4378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4378_;
}
else
{
lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4379_ = l_Lean_Syntax_getArg(v___x_4369_, v___x_4329_);
v___x_4380_ = l_Lean_Syntax_isNone(v___x_4379_);
if (v___x_4380_ == 0)
{
uint8_t v___x_4381_; 
lean_inc(v___x_4379_);
v___x_4381_ = l_Lean_Syntax_matchesNull(v___x_4379_, v___x_4329_);
if (v___x_4381_ == 0)
{
lean_object* v___x_4382_; 
lean_dec(v___x_4379_);
lean_dec(v___x_4374_);
lean_dec(v___x_4369_);
lean_dec(v_bang_4359_);
lean_dec(v_tk_3949_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
v___x_4382_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4382_;
}
else
{
lean_object* v_o_4383_; lean_object* v___x_4384_; 
v_o_4383_ = l_Lean_Syntax_getArg(v___x_4379_, v___x_3948_);
lean_dec(v___x_4379_);
v___x_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4384_, 0, v_o_4383_);
v___y_4331_ = v___x_4377_;
v___y_4332_ = v_bang_4359_;
v___y_4333_ = v___x_4368_;
v___y_4334_ = v___x_4369_;
v___y_4335_ = v___x_4374_;
v_o_4336_ = v___x_4384_;
v___y_4337_ = v___y_4360_;
v___y_4338_ = v___y_4361_;
v___y_4339_ = v___y_4362_;
v___y_4340_ = v___y_4363_;
v___y_4341_ = v___y_4364_;
v___y_4342_ = v___y_4365_;
v___y_4343_ = v___y_4366_;
v___y_4344_ = v___y_4367_;
goto v___jp_4330_;
}
}
else
{
lean_object* v___x_4385_; 
lean_dec(v___x_4379_);
v___x_4385_ = lean_box(0);
v___y_4331_ = v___x_4377_;
v___y_4332_ = v_bang_4359_;
v___y_4333_ = v___x_4368_;
v___y_4334_ = v___x_4369_;
v___y_4335_ = v___x_4374_;
v_o_4336_ = v___x_4385_;
v___y_4337_ = v___y_4360_;
v___y_4338_ = v___y_4361_;
v___y_4339_ = v___y_4362_;
v___y_4340_ = v___y_4363_;
v___y_4341_ = v___y_4364_;
v___y_4342_ = v___y_4365_;
v___y_4343_ = v___y_4366_;
v___y_4344_ = v___y_4367_;
goto v___jp_4330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4393_, lean_object* v_stx_4394_, lean_object* v___x_4395_, lean_object* v___x_4396_, lean_object* v___x_4397_, lean_object* v___x_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
uint8_t v___x_10517__boxed_4408_; uint8_t v___x_10518__boxed_4409_; lean_object* v_res_4410_; 
v___x_10517__boxed_4408_ = lean_unbox(v___x_4393_);
v___x_10518__boxed_4409_ = lean_unbox(v___x_4395_);
v_res_4410_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_10517__boxed_4408_, v_stx_4394_, v___x_10518__boxed_4409_, v___x_4396_, v___x_4397_, v___x_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v_stx_4394_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; uint8_t v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___y_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4417_);
v___x_4431_ = l_Lean_Syntax_isOfKind(v_stx_4417_, v___x_4430_);
v___x_4432_ = 1;
v___x_4433_ = lean_box(v___x_4431_);
v___x_4434_ = lean_box(v___x_4432_);
v___y_4435_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4435_, 0, v___x_4433_);
lean_closure_set(v___y_4435_, 1, v_stx_4417_);
lean_closure_set(v___y_4435_, 2, v___x_4434_);
lean_closure_set(v___y_4435_, 3, v___x_4427_);
lean_closure_set(v___y_4435_, 4, v___x_4428_);
lean_closure_set(v___y_4435_, 5, v___x_4429_);
v___x_4436_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4436_, 0, v___y_4435_);
v___x_4437_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4436_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4456_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4457_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4459_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4456_, v___x_4457_, v___x_4458_, v___x_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4491_ = l_Lean_addBuiltinDeclarationRanges(v___x_4489_, v___x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4493_;
}
}
lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
