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
lean_object* lean_erase_macro_scopes(lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t v___x_38821__boxed_208_; lean_object* v_res_209_; 
v___x_38821__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_38821__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_38848__boxed_246_; lean_object* v_res_247_; 
v___x_38848__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_38848__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
lean_dec_ref(v___x_299_);
if (lean_obj_tag(v_val_301_) == 1)
{
uint8_t v_v_302_; 
v_v_302_ = lean_ctor_get_uint8(v_val_301_, 0);
lean_dec_ref(v_val_301_);
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
lean_object* v_options_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_options_311_ = lean_ctor_get(v___y_309_, 2);
v___x_312_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_311_, v_opt_308_);
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
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v___x_327_; lean_object* v_mctx_328_; lean_object* v_lctx_329_; lean_object* v_options_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = lean_st_ref_get(v___y_321_);
v_mctx_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_mctx_328_);
lean_dec(v___x_327_);
v_lctx_329_ = lean_ctor_get(v___y_320_, 2);
v_options_330_ = lean_ctor_get(v___y_322_, 2);
lean_inc_ref(v_options_330_);
lean_inc_ref(v_lctx_329_);
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v_env_326_);
lean_ctor_set(v___x_331_, 1, v_mctx_328_);
lean_ctor_set(v___x_331_, 2, v_lctx_329_);
lean_ctor_set(v___x_331_, 3, v_options_330_);
v___x_332_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_msgData_319_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(uint8_t v___y_348_, uint8_t v_suppressElabErrors_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 1)
{
lean_object* v_pre_351_; 
v_pre_351_ = lean_ctor_get(v_x_350_, 0);
switch(lean_obj_tag(v_pre_351_))
{
case 1:
{
lean_object* v_pre_352_; 
v_pre_352_ = lean_ctor_get(v_pre_351_, 0);
switch(lean_obj_tag(v_pre_352_))
{
case 0:
{
lean_object* v_str_353_; lean_object* v_str_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_str_353_ = lean_ctor_get(v_x_350_, 1);
v_str_354_ = lean_ctor_get(v_pre_351_, 1);
v___x_355_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0));
v___x_356_ = lean_string_dec_eq(v_str_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_358_ = lean_string_dec_eq(v_str_354_, v___x_357_);
if (v___x_358_ == 0)
{
return v___y_348_;
}
else
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1));
v___x_360_ = lean_string_dec_eq(v_str_353_, v___x_359_);
if (v___x_360_ == 0)
{
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
}
}
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2));
v___x_362_ = lean_string_dec_eq(v_str_353_, v___x_361_);
if (v___x_362_ == 0)
{
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
}
}
}
case 1:
{
lean_object* v_pre_363_; 
v_pre_363_ = lean_ctor_get(v_pre_352_, 0);
if (lean_obj_tag(v_pre_363_) == 0)
{
lean_object* v_str_364_; lean_object* v_str_365_; lean_object* v_str_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_str_364_ = lean_ctor_get(v_x_350_, 1);
v_str_365_ = lean_ctor_get(v_pre_351_, 1);
v_str_366_ = lean_ctor_get(v_pre_352_, 1);
v___x_367_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3));
v___x_368_ = lean_string_dec_eq(v_str_366_, v___x_367_);
if (v___x_368_ == 0)
{
return v___y_348_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4));
v___x_370_ = lean_string_dec_eq(v_str_365_, v___x_369_);
if (v___x_370_ == 0)
{
return v___y_348_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5));
v___x_372_ = lean_string_dec_eq(v_str_364_, v___x_371_);
if (v___x_372_ == 0)
{
return v___y_348_;
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
return v___y_348_;
}
}
default: 
{
return v___y_348_;
}
}
}
case 0:
{
lean_object* v_str_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_str_373_ = lean_ctor_get(v_x_350_, 1);
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6));
v___x_375_ = lean_string_dec_eq(v_str_373_, v___x_374_);
if (v___x_375_ == 0)
{
return v___y_348_;
}
else
{
return v_suppressElabErrors_349_;
}
}
default: 
{
return v___y_348_;
}
}
}
else
{
return v___y_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(lean_object* v___y_376_, lean_object* v_suppressElabErrors_377_, lean_object* v_x_378_){
_start:
{
uint8_t v___y_39047__boxed_379_; uint8_t v_suppressElabErrors_boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v___y_39047__boxed_379_ = lean_unbox(v___y_376_);
v_suppressElabErrors_boxed_380_ = lean_unbox(v_suppressElabErrors_377_);
v_res_381_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v___y_39047__boxed_379_, v_suppressElabErrors_boxed_380_, v_x_378_);
lean_dec(v_x_378_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_384_, lean_object* v_msgData_385_, uint8_t v_severity_386_, uint8_t v_isSilent_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_431_; uint8_t v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_467_; uint8_t v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; uint8_t v___x_478_; uint8_t v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; uint8_t v___y_486_; uint8_t v___y_488_; uint8_t v___x_503_; 
v___x_478_ = 2;
v___x_503_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_478_);
if (v___x_503_ == 0)
{
v___y_488_ = v___x_503_;
goto v___jp_487_;
}
else
{
uint8_t v___x_504_; 
lean_inc_ref(v_msgData_385_);
v___x_504_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_385_);
v___y_488_ = v___x_504_;
goto v___jp_487_;
}
v___jp_393_:
{
lean_object* v___x_403_; lean_object* v_currNamespace_404_; lean_object* v_openDecls_405_; lean_object* v_env_406_; lean_object* v_nextMacroScope_407_; lean_object* v_ngen_408_; lean_object* v_auxDeclNGen_409_; lean_object* v_traceState_410_; lean_object* v_cache_411_; lean_object* v_messages_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v_newDecls_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_429_; 
v___x_403_ = lean_st_ref_take(v___y_402_);
v_currNamespace_404_ = lean_ctor_get(v___y_401_, 6);
v_openDecls_405_ = lean_ctor_get(v___y_401_, 7);
v_env_406_ = lean_ctor_get(v___x_403_, 0);
v_nextMacroScope_407_ = lean_ctor_get(v___x_403_, 1);
v_ngen_408_ = lean_ctor_get(v___x_403_, 2);
v_auxDeclNGen_409_ = lean_ctor_get(v___x_403_, 3);
v_traceState_410_ = lean_ctor_get(v___x_403_, 4);
v_cache_411_ = lean_ctor_get(v___x_403_, 5);
v_messages_412_ = lean_ctor_get(v___x_403_, 6);
v_infoState_413_ = lean_ctor_get(v___x_403_, 7);
v_snapshotTasks_414_ = lean_ctor_get(v___x_403_, 8);
v_newDecls_415_ = lean_ctor_get(v___x_403_, 9);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_429_ == 0)
{
v___x_417_ = v___x_403_;
v_isShared_418_ = v_isSharedCheck_429_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_newDecls_415_);
lean_inc(v_snapshotTasks_414_);
lean_inc(v_infoState_413_);
lean_inc(v_messages_412_);
lean_inc(v_cache_411_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_409_);
lean_inc(v_ngen_408_);
lean_inc(v_nextMacroScope_407_);
lean_inc(v_env_406_);
lean_dec(v___x_403_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_429_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_inc(v_openDecls_405_);
lean_inc(v_currNamespace_404_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_currNamespace_404_);
lean_ctor_set(v___x_419_, 1, v_openDecls_405_);
v___x_420_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___y_397_);
lean_inc_ref(v___y_394_);
lean_inc_ref(v___y_396_);
v___x_421_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_421_, 0, v___y_396_);
lean_ctor_set(v___x_421_, 1, v___y_395_);
lean_ctor_set(v___x_421_, 2, v___y_399_);
lean_ctor_set(v___x_421_, 3, v___y_394_);
lean_ctor_set(v___x_421_, 4, v___x_420_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*5, v___y_398_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*5 + 1, v___y_400_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*5 + 2, v_isSilent_387_);
v___x_422_ = l_Lean_MessageLog_add(v___x_421_, v_messages_412_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 6, v___x_422_);
v___x_424_ = v___x_417_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_env_406_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_nextMacroScope_407_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_ngen_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_auxDeclNGen_409_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_traceState_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_cache_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v_infoState_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_snapshotTasks_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 9, v_newDecls_415_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_st_ref_set(v___y_402_, v___x_424_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
}
v___jp_430_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_454_; 
v___x_439_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_385_);
v___x_440_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_439_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_inc_ref_n(v___y_434_, 2);
v___x_445_ = l_Lean_FileMap_toPosition(v___y_434_, v___y_435_);
lean_dec(v___y_435_);
v___x_446_ = l_Lean_FileMap_toPosition(v___y_434_, v___y_438_);
lean_dec(v___y_438_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
v___x_448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0));
if (v___y_432_ == 0)
{
lean_del_object(v___x_443_);
lean_dec_ref(v___y_431_);
v___y_394_ = v___x_448_;
v___y_395_ = v___x_445_;
v___y_396_ = v___y_433_;
v___y_397_ = v_a_441_;
v___y_398_ = v___y_436_;
v___y_399_ = v___x_447_;
v___y_400_ = v___y_437_;
v___y_401_ = v___y_390_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
else
{
uint8_t v___x_449_; 
lean_inc(v_a_441_);
v___x_449_ = l_Lean_MessageData_hasTag(v___y_431_, v_a_441_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec_ref(v___x_447_);
lean_dec_ref(v___x_445_);
lean_dec(v_a_441_);
v___x_450_ = lean_box(0);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_450_);
v___x_452_ = v___x_443_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_del_object(v___x_443_);
v___y_394_ = v___x_448_;
v___y_395_ = v___x_445_;
v___y_396_ = v___y_433_;
v___y_397_ = v_a_441_;
v___y_398_ = v___y_436_;
v___y_399_ = v___x_447_;
v___y_400_ = v___y_437_;
v___y_401_ = v___y_390_;
v___y_402_ = v___y_391_;
goto v___jp_393_;
}
}
}
}
v___jp_455_:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Syntax_getTailPos_x3f(v___y_461_, v___y_460_);
lean_dec(v___y_461_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_inc(v___y_463_);
v___y_431_ = v___y_456_;
v___y_432_ = v___y_457_;
v___y_433_ = v___y_459_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_460_;
v___y_437_ = v___y_462_;
v___y_438_ = v___y_463_;
goto v___jp_430_;
}
else
{
lean_object* v_val_465_; 
v_val_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref(v___x_464_);
v___y_431_ = v___y_456_;
v___y_432_ = v___y_457_;
v___y_433_ = v___y_459_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_463_;
v___y_436_ = v___y_460_;
v___y_437_ = v___y_462_;
v___y_438_ = v_val_465_;
goto v___jp_430_;
}
}
v___jp_466_:
{
lean_object* v_ref_474_; lean_object* v___x_475_; 
v_ref_474_ = l_Lean_replaceRef(v_ref_384_, v___y_472_);
v___x_475_ = l_Lean_Syntax_getPos_x3f(v_ref_474_, v___y_471_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___y_456_ = v___y_467_;
v___y_457_ = v___y_468_;
v___y_458_ = v___y_470_;
v___y_459_ = v___y_469_;
v___y_460_ = v___y_471_;
v___y_461_ = v_ref_474_;
v___y_462_ = v___y_473_;
v___y_463_ = v___x_476_;
goto v___jp_455_;
}
else
{
lean_object* v_val_477_; 
v_val_477_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v___x_475_);
v___y_456_ = v___y_467_;
v___y_457_ = v___y_468_;
v___y_458_ = v___y_470_;
v___y_459_ = v___y_469_;
v___y_460_ = v___y_471_;
v___y_461_ = v_ref_474_;
v___y_462_ = v___y_473_;
v___y_463_ = v_val_477_;
goto v___jp_455_;
}
}
v___jp_479_:
{
if (v___y_486_ == 0)
{
v___y_467_ = v___y_483_;
v___y_468_ = v___y_480_;
v___y_469_ = v___y_482_;
v___y_470_ = v___y_481_;
v___y_471_ = v___y_485_;
v___y_472_ = v___y_484_;
v___y_473_ = v_severity_386_;
goto v___jp_466_;
}
else
{
v___y_467_ = v___y_483_;
v___y_468_ = v___y_480_;
v___y_469_ = v___y_482_;
v___y_470_ = v___y_481_;
v___y_471_ = v___y_485_;
v___y_472_ = v___y_484_;
v___y_473_ = v___x_478_;
goto v___jp_466_;
}
}
v___jp_487_:
{
if (v___y_488_ == 0)
{
lean_object* v_fileName_489_; lean_object* v_fileMap_490_; lean_object* v_options_491_; lean_object* v_ref_492_; uint8_t v_suppressElabErrors_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___f_496_; uint8_t v___x_497_; uint8_t v___x_498_; 
v_fileName_489_ = lean_ctor_get(v___y_390_, 0);
v_fileMap_490_ = lean_ctor_get(v___y_390_, 1);
v_options_491_ = lean_ctor_get(v___y_390_, 2);
v_ref_492_ = lean_ctor_get(v___y_390_, 5);
v_suppressElabErrors_493_ = lean_ctor_get_uint8(v___y_390_, sizeof(void*)*14 + 1);
v___x_494_ = lean_box(v___y_488_);
v___x_495_ = lean_box(v_suppressElabErrors_493_);
v___f_496_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_496_, 0, v___x_494_);
lean_closure_set(v___f_496_, 1, v___x_495_);
v___x_497_ = 1;
v___x_498_ = l_Lean_instBEqMessageSeverity_beq(v_severity_386_, v___x_497_);
if (v___x_498_ == 0)
{
v___y_480_ = v_suppressElabErrors_493_;
v___y_481_ = v_fileMap_490_;
v___y_482_ = v_fileName_489_;
v___y_483_ = v___f_496_;
v___y_484_ = v_ref_492_;
v___y_485_ = v___y_488_;
v___y_486_ = v___x_498_;
goto v___jp_479_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = l_Lean_warningAsError;
v___x_500_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_491_, v___x_499_);
v___y_480_ = v_suppressElabErrors_493_;
v___y_481_ = v_fileMap_490_;
v___y_482_ = v_fileName_489_;
v___y_483_ = v___f_496_;
v___y_484_ = v_ref_492_;
v___y_485_ = v___y_488_;
v___y_486_ = v___x_500_;
goto v___jp_479_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v_msgData_385_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_505_, lean_object* v_msgData_506_, lean_object* v_severity_507_, lean_object* v_isSilent_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v_severity_boxed_514_; uint8_t v_isSilent_boxed_515_; lean_object* v_res_516_; 
v_severity_boxed_514_ = lean_unbox(v_severity_507_);
v_isSilent_boxed_515_ = lean_unbox(v_isSilent_508_);
v_res_516_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_505_, v_msgData_506_, v_severity_boxed_514_, v_isSilent_boxed_515_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v_ref_505_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_517_, uint8_t v_severity_518_, uint8_t v_isSilent_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_ref_529_; lean_object* v___x_530_; 
v_ref_529_ = lean_ctor_get(v___y_526_, 5);
v___x_530_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_529_, v_msgData_517_, v_severity_518_, v_isSilent_519_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_531_, lean_object* v_severity_532_, lean_object* v_isSilent_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
uint8_t v_severity_boxed_543_; uint8_t v_isSilent_boxed_544_; lean_object* v_res_545_; 
v_severity_boxed_543_ = lean_unbox(v_severity_532_);
v_isSilent_boxed_544_ = lean_unbox(v_isSilent_533_);
v_res_545_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_531_, v_severity_boxed_543_, v_isSilent_boxed_544_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = 1;
v___x_557_ = 0;
v___x_558_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_546_, v___x_556_, v___x_557_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(lean_object* v_msgData_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v_env_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_609_; 
v___x_586_ = lean_st_ref_get(v___y_584_);
v_env_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc_ref(v_env_587_);
lean_dec(v___x_586_);
v___x_588_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_589_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_588_, v___y_583_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_609_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_609_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_609_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v_isExporting_599_; 
v_isExporting_599_ = lean_ctor_get_uint8(v_env_587_, sizeof(void*)*8);
lean_dec_ref(v_env_587_);
if (v_isExporting_599_ == 0)
{
lean_dec(v_a_590_);
lean_dec(v_id_576_);
goto v___jp_594_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_isPrivateName(v_id_576_);
if (v___x_600_ == 0)
{
lean_dec(v_a_590_);
lean_dec(v_id_576_);
goto v___jp_594_;
}
else
{
uint8_t v___x_601_; 
v___x_601_ = lean_unbox(v_a_590_);
lean_dec(v_a_590_);
if (v___x_601_ == 0)
{
lean_dec(v_id_576_);
goto v___jp_594_;
}
else
{
lean_object* v___x_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_592_);
v___x_602_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
v___x_603_ = 0;
v___x_604_ = l_Lean_MessageData_ofConstName(v_id_576_, v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_607_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_608_;
}
}
}
v___jp_594_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_595_);
v___x_597_ = v___x_592_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_621_, uint8_t v_enableLog_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v_env_633_; lean_object* v_options_634_; lean_object* v_currNamespace_635_; lean_object* v_openDecls_636_; lean_object* v___x_637_; lean_object* v_env_638_; lean_object* v_res_639_; 
v___x_632_ = lean_st_ref_get(v___y_630_);
v_env_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc_ref(v_env_633_);
lean_dec(v___x_632_);
v_options_634_ = lean_ctor_get(v___y_629_, 2);
v_currNamespace_635_ = lean_ctor_get(v___y_629_, 6);
v_openDecls_636_ = lean_ctor_get(v___y_629_, 7);
v___x_637_ = lean_st_ref_get(v___y_630_);
v_env_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_638_);
lean_dec(v___x_637_);
lean_inc(v_openDecls_636_);
lean_inc(v_currNamespace_635_);
v_res_639_ = l_Lean_ResolveName_resolveGlobalName(v_env_633_, v_options_634_, v_currNamespace_635_, v_openDecls_636_, v_id_621_);
if (v_enableLog_622_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_env_638_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_res_639_);
return v___x_640_;
}
else
{
uint8_t v_isExporting_641_; 
v_isExporting_641_ = lean_ctor_get_uint8(v_env_638_, sizeof(void*)*8);
lean_dec_ref(v_env_638_);
if (v_isExporting_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_res_639_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_639_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v_fst_645_; lean_object* v___x_646_; 
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref(v___x_643_);
v_fst_645_ = lean_ctor_get(v_val_644_, 0);
lean_inc(v_fst_645_);
lean_dec(v_val_644_);
v___x_646_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_645_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___x_646_, 0);
lean_dec(v_unused_654_);
v___x_648_ = v___x_646_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_dec(v___x_646_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_res_639_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_res_639_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v_res_639_);
v_a_655_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_646_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v___x_663_; 
lean_dec(v___x_643_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v_res_639_);
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_664_, lean_object* v_enableLog_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_enableLog_boxed_675_; lean_object* v_res_676_; 
v_enableLog_boxed_675_ = lean_unbox(v_enableLog_665_);
v_res_676_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_664_, v_enableLog_boxed_675_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
if (lean_obj_tag(v_a_677_) == 0)
{
lean_object* v___x_679_; 
v___x_679_ = l_List_reverse___redArg(v_a_678_);
return v___x_679_;
}
else
{
lean_object* v_head_680_; lean_object* v_tail_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_692_; 
v_head_680_ = lean_ctor_get(v_a_677_, 0);
v_tail_681_ = lean_ctor_get(v_a_677_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_677_);
if (v_isSharedCheck_692_ == 0)
{
v___x_683_ = v_a_677_;
v_isShared_684_ = v_isSharedCheck_692_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_tail_681_);
lean_inc(v_head_680_);
lean_dec(v_a_677_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_692_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_snd_685_; uint8_t v___x_686_; 
v_snd_685_ = lean_ctor_get(v_head_680_, 1);
v___x_686_ = l_List_isEmpty___redArg(v_snd_685_);
if (v___x_686_ == 0)
{
lean_del_object(v___x_683_);
lean_dec(v_head_680_);
v_a_677_ = v_tail_681_;
goto _start;
}
else
{
lean_object* v___x_689_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v_a_678_);
v___x_689_ = v___x_683_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_head_680_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_a_678_);
v___x_689_ = v_reuseFailAlloc_691_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_a_677_ = v_tail_681_;
v_a_678_ = v___x_689_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
if (lean_obj_tag(v_a_693_) == 0)
{
lean_object* v___x_695_; 
v___x_695_ = l_List_reverse___redArg(v_a_694_);
return v___x_695_;
}
else
{
lean_object* v_head_696_; lean_object* v_tail_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_706_; 
v_head_696_ = lean_ctor_get(v_a_693_, 0);
v_tail_697_ = lean_ctor_get(v_a_693_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_706_ == 0)
{
v___x_699_ = v_a_693_;
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_tail_697_);
lean_inc(v_head_696_);
lean_dec(v_a_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_fst_701_; lean_object* v___x_703_; 
v_fst_701_ = lean_ctor_get(v_head_696_, 0);
lean_inc(v_fst_701_);
lean_dec(v_head_696_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_a_694_);
lean_ctor_set(v___x_699_, 0, v_fst_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fst_701_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_a_694_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_a_693_ = v_tail_697_;
v_a_694_ = v___x_703_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_ref_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_ref_713_ = lean_ctor_get(v___y_710_, 5);
v___x_714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_inc(v_ref_713_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v_ref_713_);
lean_ctor_set(v___x_719_, 1, v_a_715_);
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 1);
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_731_, lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_fileName_742_; lean_object* v_fileMap_743_; lean_object* v_options_744_; lean_object* v_currRecDepth_745_; lean_object* v_maxRecDepth_746_; lean_object* v_ref_747_; lean_object* v_currNamespace_748_; lean_object* v_openDecls_749_; lean_object* v_initHeartbeats_750_; lean_object* v_maxHeartbeats_751_; lean_object* v_quotContext_752_; lean_object* v_currMacroScope_753_; uint8_t v_diag_754_; lean_object* v_cancelTk_x3f_755_; uint8_t v_suppressElabErrors_756_; lean_object* v_inheritedTraceOptions_757_; lean_object* v_ref_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_fileName_742_ = lean_ctor_get(v___y_739_, 0);
v_fileMap_743_ = lean_ctor_get(v___y_739_, 1);
v_options_744_ = lean_ctor_get(v___y_739_, 2);
v_currRecDepth_745_ = lean_ctor_get(v___y_739_, 3);
v_maxRecDepth_746_ = lean_ctor_get(v___y_739_, 4);
v_ref_747_ = lean_ctor_get(v___y_739_, 5);
v_currNamespace_748_ = lean_ctor_get(v___y_739_, 6);
v_openDecls_749_ = lean_ctor_get(v___y_739_, 7);
v_initHeartbeats_750_ = lean_ctor_get(v___y_739_, 8);
v_maxHeartbeats_751_ = lean_ctor_get(v___y_739_, 9);
v_quotContext_752_ = lean_ctor_get(v___y_739_, 10);
v_currMacroScope_753_ = lean_ctor_get(v___y_739_, 11);
v_diag_754_ = lean_ctor_get_uint8(v___y_739_, sizeof(void*)*14);
v_cancelTk_x3f_755_ = lean_ctor_get(v___y_739_, 12);
v_suppressElabErrors_756_ = lean_ctor_get_uint8(v___y_739_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_757_ = lean_ctor_get(v___y_739_, 13);
v_ref_758_ = l_Lean_replaceRef(v_ref_731_, v_ref_747_);
lean_inc_ref(v_inheritedTraceOptions_757_);
lean_inc(v_cancelTk_x3f_755_);
lean_inc(v_currMacroScope_753_);
lean_inc(v_quotContext_752_);
lean_inc(v_maxHeartbeats_751_);
lean_inc(v_initHeartbeats_750_);
lean_inc(v_openDecls_749_);
lean_inc(v_currNamespace_748_);
lean_inc(v_maxRecDepth_746_);
lean_inc(v_currRecDepth_745_);
lean_inc_ref(v_options_744_);
lean_inc_ref(v_fileMap_743_);
lean_inc_ref(v_fileName_742_);
v___x_759_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_759_, 0, v_fileName_742_);
lean_ctor_set(v___x_759_, 1, v_fileMap_743_);
lean_ctor_set(v___x_759_, 2, v_options_744_);
lean_ctor_set(v___x_759_, 3, v_currRecDepth_745_);
lean_ctor_set(v___x_759_, 4, v_maxRecDepth_746_);
lean_ctor_set(v___x_759_, 5, v_ref_758_);
lean_ctor_set(v___x_759_, 6, v_currNamespace_748_);
lean_ctor_set(v___x_759_, 7, v_openDecls_749_);
lean_ctor_set(v___x_759_, 8, v_initHeartbeats_750_);
lean_ctor_set(v___x_759_, 9, v_maxHeartbeats_751_);
lean_ctor_set(v___x_759_, 10, v_quotContext_752_);
lean_ctor_set(v___x_759_, 11, v_currMacroScope_753_);
lean_ctor_set(v___x_759_, 12, v_cancelTk_x3f_755_);
lean_ctor_set(v___x_759_, 13, v_inheritedTraceOptions_757_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*14, v_diag_754_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*14 + 1, v_suppressElabErrors_756_);
v___x_760_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_732_, v___y_737_, v___y_738_, v___x_759_, v___y_740_);
lean_dec_ref(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_761_, lean_object* v_msg_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_761_, v_msg_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v_ref_761_);
return v_res_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
lean_ctor_set(v___x_778_, 3, v___x_777_);
lean_ctor_set(v___x_778_, 4, v___x_776_);
lean_ctor_set(v___x_778_, 5, v___x_776_);
lean_ctor_set(v___x_778_, 6, v___x_776_);
lean_ctor_set(v___x_778_, 7, v___x_776_);
lean_ctor_set(v___x_778_, 8, v___x_776_);
lean_ctor_set(v___x_778_, 9, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_unsigned_to_nat(32u);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = ((size_t)5ULL);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_unsigned_to_nat(32u);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_784_);
v___x_786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_787_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
lean_ctor_set(v___x_787_, 2, v___x_783_);
lean_ctor_set(v___x_787_, 3, v___x_783_);
lean_ctor_set_usize(v___x_787_, 4, v___x_782_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_box(1);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
lean_ctor_set(v___x_791_, 2, v___x_788_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_813_, lean_object* v_declHint_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_env_818_; uint8_t v___x_819_; 
v___x_817_ = lean_st_ref_get(v___y_815_);
v_env_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref(v_env_818_);
lean_dec(v___x_817_);
v___x_819_ = l_Lean_Name_isAnonymous(v_declHint_814_);
if (v___x_819_ == 0)
{
uint8_t v_isExporting_820_; 
v_isExporting_820_ = lean_ctor_get_uint8(v_env_818_, sizeof(void*)*8);
if (v_isExporting_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_msg_813_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
lean_inc_ref(v_env_818_);
v___x_822_ = l_Lean_Environment_setExporting(v_env_818_, v___x_819_);
lean_inc(v_declHint_814_);
lean_inc_ref(v___x_822_);
v___x_823_ = l_Lean_Environment_contains(v___x_822_, v_declHint_814_, v_isExporting_820_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v___x_822_);
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v_msg_813_);
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
lean_inc(v_declHint_814_);
v___x_829_ = l_Lean_MessageData_ofConstName(v_declHint_814_, v___x_819_);
v_c_830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_830_, 0, v___x_828_);
lean_ctor_set(v_c_830_, 1, v___x_829_);
v___x_831_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_818_, v_declHint_814_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
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
lean_ctor_set(v___x_837_, 0, v_msg_813_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_874_; 
v_val_839_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_874_ == 0)
{
v___x_841_ = v___x_831_;
v_isShared_842_ = v_isSharedCheck_874_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_831_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_874_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_mod_846_; uint8_t v___x_847_; 
v___x_843_ = lean_box(0);
v___x_844_ = l_Lean_Environment_header(v_env_818_);
lean_dec_ref(v_env_818_);
v___x_845_ = l_Lean_EnvironmentHeader_moduleNames(v___x_844_);
v_mod_846_ = lean_array_get(v___x_843_, v___x_845_, v_val_839_);
lean_dec(v_val_839_);
lean_dec_ref(v___x_845_);
v___x_847_ = l_Lean_isPrivateName(v_declHint_814_);
lean_dec(v_declHint_814_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_c_830_);
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofName(v_mod_846_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_note(v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v_msg_813_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_857_);
v___x_859_ = v___x_841_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_c_830_);
v___x_863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_MessageData_ofName(v_mod_846_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_note(v___x_868_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v_msg_813_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_870_);
v___x_872_ = v___x_841_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_875_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v_msg_813_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_876_, lean_object* v_declHint_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_876_, v_declHint_877_, v___y_878_);
lean_dec(v___y_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_881_, lean_object* v_declHint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_902_; 
v___x_892_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_881_, v_declHint_882_, v___y_890_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_902_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_902_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_902_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_897_ = l_Lean_unknownIdentifierMessageTag;
v___x_898_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_a_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_898_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_903_, lean_object* v_declHint_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_903_, v_declHint_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_915_, lean_object* v_msg_916_, lean_object* v_declHint_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v_a_928_; lean_object* v___x_929_; 
v___x_927_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_916_, v_declHint_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref(v___x_927_);
v___x_929_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_915_, v_a_928_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_930_, lean_object* v_msg_931_, lean_object* v_declHint_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_930_, v_msg_931_, v_declHint_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v_ref_930_);
return v_res_942_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_949_, lean_object* v_constName_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_960_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_961_ = 0;
lean_inc(v_constName_950_);
v___x_962_ = l_Lean_MessageData_ofConstName(v_constName_950_, v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_960_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_949_, v___x_965_, v_constName_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_967_, lean_object* v_constName_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_967_, v_constName_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v_ref_967_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_979_, lean_object* v_cs_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v_cs_991_; uint8_t v___x_995_; 
v___x_990_ = lean_box(0);
v_cs_991_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_980_, v___x_990_);
v___x_995_ = l_List_isEmpty___redArg(v_cs_991_);
if (v___x_995_ == 0)
{
lean_dec(v_n_979_);
goto v___jp_992_;
}
else
{
lean_object* v_ref_996_; lean_object* v___x_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_cs_991_);
v_ref_996_ = lean_ctor_get(v___y_987_, 5);
v___x_997_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_996_, v_n_979_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
v___jp_992_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_991_, v___x_990_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1006_, lean_object* v_cs_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1006_, v_cs_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = 1;
lean_inc(v_n_1018_);
v___x_1029_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1018_, v___x_1028_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1018_, v_a_1030_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1031_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_n_1018_);
v_a_1032_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1029_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1029_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
if (lean_obj_tag(v_a_1051_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_array_to_list(v_a_1052_);
return v___x_1053_;
}
else
{
lean_object* v_head_1054_; 
v_head_1054_ = lean_ctor_get(v_a_1051_, 0);
if (lean_obj_tag(v_head_1054_) == 1)
{
lean_object* v_fields_1055_; 
v_fields_1055_ = lean_ctor_get(v_head_1054_, 1);
if (lean_obj_tag(v_fields_1055_) == 0)
{
lean_object* v_tail_1056_; lean_object* v_n_1057_; lean_object* v___x_1058_; 
lean_inc_ref(v_head_1054_);
v_tail_1056_ = lean_ctor_get(v_a_1051_, 1);
lean_inc(v_tail_1056_);
lean_dec_ref(v_a_1051_);
v_n_1057_ = lean_ctor_get(v_head_1054_, 0);
lean_inc(v_n_1057_);
lean_dec_ref(v_head_1054_);
v___x_1058_ = lean_array_push(v_a_1052_, v_n_1057_);
v_a_1051_ = v_tail_1056_;
v_a_1052_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v_tail_1060_; 
v_tail_1060_ = lean_ctor_get(v_a_1051_, 1);
lean_inc(v_tail_1060_);
lean_dec_ref(v_a_1051_);
v_a_1051_ = v_tail_1060_;
goto _start;
}
}
else
{
lean_object* v_tail_1062_; 
v_tail_1062_ = lean_ctor_get(v_a_1051_, 1);
lean_inc(v_tail_1062_);
lean_dec_ref(v_a_1051_);
v_a_1051_ = v_tail_1062_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1070_ = l_Lean_MessageData_ofFormat(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1071_, lean_object* v_k_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
if (lean_obj_tag(v_stx_1071_) == 3)
{
lean_object* v_val_1082_; lean_object* v_preresolved_1083_; lean_object* v___x_1084_; lean_object* v_pre_1085_; uint8_t v___x_1086_; 
v_val_1082_ = lean_ctor_get(v_stx_1071_, 2);
lean_inc(v_val_1082_);
v_preresolved_1083_ = lean_ctor_get(v_stx_1071_, 3);
v___x_1084_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1083_);
v_pre_1085_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1083_, v___x_1084_);
v___x_1086_ = l_List_isEmpty___redArg(v_pre_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v_stx_1071_);
lean_dec(v_val_1082_);
lean_dec_ref(v_k_1072_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_pre_1085_);
return v___x_1087_;
}
else
{
lean_object* v_fileName_1088_; lean_object* v_fileMap_1089_; lean_object* v_options_1090_; lean_object* v_currRecDepth_1091_; lean_object* v_maxRecDepth_1092_; lean_object* v_ref_1093_; lean_object* v_currNamespace_1094_; lean_object* v_openDecls_1095_; lean_object* v_initHeartbeats_1096_; lean_object* v_maxHeartbeats_1097_; lean_object* v_quotContext_1098_; lean_object* v_currMacroScope_1099_; uint8_t v_diag_1100_; lean_object* v_cancelTk_x3f_1101_; uint8_t v_suppressElabErrors_1102_; lean_object* v_inheritedTraceOptions_1103_; lean_object* v_ref_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_pre_1085_);
v_fileName_1088_ = lean_ctor_get(v___y_1079_, 0);
v_fileMap_1089_ = lean_ctor_get(v___y_1079_, 1);
v_options_1090_ = lean_ctor_get(v___y_1079_, 2);
v_currRecDepth_1091_ = lean_ctor_get(v___y_1079_, 3);
v_maxRecDepth_1092_ = lean_ctor_get(v___y_1079_, 4);
v_ref_1093_ = lean_ctor_get(v___y_1079_, 5);
v_currNamespace_1094_ = lean_ctor_get(v___y_1079_, 6);
v_openDecls_1095_ = lean_ctor_get(v___y_1079_, 7);
v_initHeartbeats_1096_ = lean_ctor_get(v___y_1079_, 8);
v_maxHeartbeats_1097_ = lean_ctor_get(v___y_1079_, 9);
v_quotContext_1098_ = lean_ctor_get(v___y_1079_, 10);
v_currMacroScope_1099_ = lean_ctor_get(v___y_1079_, 11);
v_diag_1100_ = lean_ctor_get_uint8(v___y_1079_, sizeof(void*)*14);
v_cancelTk_x3f_1101_ = lean_ctor_get(v___y_1079_, 12);
v_suppressElabErrors_1102_ = lean_ctor_get_uint8(v___y_1079_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1103_ = lean_ctor_get(v___y_1079_, 13);
v_ref_1104_ = l_Lean_replaceRef(v_stx_1071_, v_ref_1093_);
lean_dec_ref(v_stx_1071_);
lean_inc_ref(v_inheritedTraceOptions_1103_);
lean_inc(v_cancelTk_x3f_1101_);
lean_inc(v_currMacroScope_1099_);
lean_inc(v_quotContext_1098_);
lean_inc(v_maxHeartbeats_1097_);
lean_inc(v_initHeartbeats_1096_);
lean_inc(v_openDecls_1095_);
lean_inc(v_currNamespace_1094_);
lean_inc(v_maxRecDepth_1092_);
lean_inc(v_currRecDepth_1091_);
lean_inc_ref(v_options_1090_);
lean_inc_ref(v_fileMap_1089_);
lean_inc_ref(v_fileName_1088_);
v___x_1105_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1105_, 0, v_fileName_1088_);
lean_ctor_set(v___x_1105_, 1, v_fileMap_1089_);
lean_ctor_set(v___x_1105_, 2, v_options_1090_);
lean_ctor_set(v___x_1105_, 3, v_currRecDepth_1091_);
lean_ctor_set(v___x_1105_, 4, v_maxRecDepth_1092_);
lean_ctor_set(v___x_1105_, 5, v_ref_1104_);
lean_ctor_set(v___x_1105_, 6, v_currNamespace_1094_);
lean_ctor_set(v___x_1105_, 7, v_openDecls_1095_);
lean_ctor_set(v___x_1105_, 8, v_initHeartbeats_1096_);
lean_ctor_set(v___x_1105_, 9, v_maxHeartbeats_1097_);
lean_ctor_set(v___x_1105_, 10, v_quotContext_1098_);
lean_ctor_set(v___x_1105_, 11, v_currMacroScope_1099_);
lean_ctor_set(v___x_1105_, 12, v_cancelTk_x3f_1101_);
lean_ctor_set(v___x_1105_, 13, v_inheritedTraceOptions_1103_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*14, v_diag_1100_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*14 + 1, v_suppressElabErrors_1102_);
lean_inc(v___y_1080_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
v___x_1106_ = lean_apply_10(v_k_1072_, v_val_1082_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___x_1105_, v___y_1080_, lean_box(0));
return v___x_1106_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_k_1072_);
v___x_1107_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1108_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1071_, v___x_1107_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v_stx_1071_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1109_, lean_object* v_k_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1109_, v_k_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1133_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1122_, v___x_1132_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_b_1148_);
return v___x_1159_;
}
else
{
lean_object* v_a_1160_; lean_object* v_name_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_a_1160_ = lean_array_uget_borrowed(v_as_1145_, v_i_1147_);
v_name_1161_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_name_1161_);
v___x_1162_ = lean_mk_syntax_ident(v_name_1161_);
lean_inc(v___x_1162_);
v___x_1163_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1162_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v___x_1163_);
v___x_1165_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1162_, v_a_1164_, v_b_1148_, v___y_1155_);
lean_dec(v_a_1164_);
lean_dec(v___x_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; size_t v___x_1167_; size_t v___x_1168_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1147_, v___x_1167_);
v_i_1147_ = v___x_1168_;
v_b_1148_ = v_a_1166_;
goto _start;
}
else
{
return v___x_1165_;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v___x_1162_);
lean_dec_ref(v_b_1148_);
v_a_1170_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1163_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1163_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1178_, lean_object* v_sz_1179_, lean_object* v_i_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1178_, v_sz_boxed_1191_, v_i_boxed_1192_, v_b_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec_ref(v_as_1178_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1213_, lean_object* v_stx_1214_, uint8_t v___x_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___f_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
if (v___x_1213_ == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_1229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v_tk_1231_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1303_; lean_object* v___y_1304_; uint8_t v___y_1305_; uint8_t v___y_1306_; lean_object* v___y_1307_; lean_object* v_stxForSuggestion_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1340_; uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1405_; uint8_t v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1464_; lean_object* v___y_1465_; uint8_t v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; uint8_t v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1502_; lean_object* v___y_1503_; uint8_t v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; uint8_t v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1534_; uint8_t v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; uint8_t v___y_1552_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_stxForExecution_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; uint8_t v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; uint8_t v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; uint8_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; uint8_t v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1804_; lean_object* v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; uint8_t v___y_1821_; lean_object* v___y_1834_; lean_object* v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; uint8_t v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v_argsArray_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; uint8_t v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_2001_; uint8_t v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v_args_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___x_2028_; lean_object* v___y_2030_; uint8_t v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v_o_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v_bang_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v_tk_1231_ = l_Lean_Syntax_getArg(v_stx_1214_, v___x_1230_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2087_ = l_Lean_Syntax_getArg(v_stx_1214_, v___x_2028_);
v___x_2088_ = l_Lean_Syntax_isNone(v___x_2087_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
lean_inc(v___x_2087_);
v___x_2089_ = l_Lean_Syntax_matchesNull(v___x_2087_, v___x_2028_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v___x_2087_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2090_;
}
else
{
lean_object* v_bang_2091_; lean_object* v___x_2092_; 
v_bang_2091_ = l_Lean_Syntax_getArg(v___x_2087_, v___x_1230_);
lean_dec(v___x_2087_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_bang_2091_);
v_bang_2059_ = v___x_2092_;
v___y_2060_ = v___y_1220_;
v___y_2061_ = v___y_1221_;
v___y_2062_ = v___y_1222_;
v___y_2063_ = v___y_1223_;
v___y_2064_ = v___y_1224_;
v___y_2065_ = v___y_1225_;
v___y_2066_ = v___y_1226_;
v___y_2067_ = v___y_1227_;
goto v___jp_2058_;
}
}
else
{
lean_object* v___x_2093_; 
lean_dec(v___x_2087_);
v___x_2093_ = lean_box(0);
v_bang_2059_ = v___x_2093_;
v___y_2060_ = v___y_1220_;
v___y_2061_ = v___y_1221_;
v___y_2062_ = v___y_1222_;
v___y_2063_ = v___y_1223_;
v___y_2064_ = v___y_1224_;
v___y_2065_ = v___y_1225_;
v___y_2066_ = v___y_1226_;
v___y_2067_ = v___y_1227_;
goto v___jp_2058_;
}
v___jp_1232_:
{
lean_object* v___x_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_box(v___x_1215_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1247_, 0, v___y_1233_);
lean_closure_set(v___f_1247_, 1, v___x_1230_);
lean_closure_set(v___f_1247_, 2, v___x_1246_);
lean_closure_set(v___f_1247_, 3, v___y_1245_);
lean_closure_set(v___f_1247_, 4, v___y_1234_);
v___x_1248_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1235_, v___f_1247_, v___y_1242_, v___y_1240_, v___y_1244_, v___y_1243_, v___y_1239_, v___y_1238_, v___y_1237_, v___y_1241_);
lean_dec(v___y_1235_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_usedTheorems_1250_; lean_object* v_diag_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1293_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1248_);
v_usedTheorems_1250_ = lean_ctor_get(v_a_1249_, 0);
v_diag_1251_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1253_ = v_a_1249_;
v_isShared_1254_ = v_isSharedCheck_1293_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_diag_1251_);
lean_inc(v_usedTheorems_1250_);
lean_dec(v_a_1249_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1293_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1236_, v_usedTheorems_1250_, v___y_1239_, v___y_1238_, v___y_1237_, v___y_1241_);
lean_dec_ref(v_usedTheorems_1250_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_ref_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1255_);
v_ref_1257_ = lean_ctor_get(v___y_1237_, 5);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v_a_1256_);
lean_ctor_set(v___x_1253_, 0, v___x_1258_);
v___x_1260_ = v___x_1253_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1256_);
v___x_1260_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1261_);
lean_ctor_set(v___x_1262_, 4, v___x_1261_);
lean_ctor_set(v___x_1262_, 5, v___x_1261_);
lean_inc(v_ref_1257_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_ref_1257_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1265_ = 4;
v___x_1266_ = l_Lean_MessageData_nil;
v___x_1267_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1231_, v___x_1262_, v___x_1263_, v___x_1264_, v___x_1261_, v___x_1265_, v___x_1266_, v___y_1237_, v___y_1241_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_diag_1251_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_diag_1251_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_diag_1251_);
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1267_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1267_);
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
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1253_);
lean_dec_ref(v_diag_1251_);
lean_dec(v_tk_1231_);
v_a_1285_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1255_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1255_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___y_1236_);
lean_dec(v_tk_1231_);
v_a_1294_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1248_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1248_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
v___jp_1302_:
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = 0;
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1319_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1307_, v___x_1317_, v___y_1305_, v___x_1317_, v___x_1318_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1307_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
if (lean_obj_tag(v___y_1304_) == 0)
{
lean_object* v_ctx_1321_; lean_object* v_simprocs_1322_; lean_object* v_dischargeWrapper_1323_; 
v_ctx_1321_ = lean_ctor_get(v_a_1320_, 0);
lean_inc_ref(v_ctx_1321_);
v_simprocs_1322_ = lean_ctor_get(v_a_1320_, 1);
lean_inc_ref(v_simprocs_1322_);
v_dischargeWrapper_1323_ = lean_ctor_get(v_a_1320_, 2);
lean_inc(v_dischargeWrapper_1323_);
lean_dec(v_a_1320_);
v___y_1233_ = v___y_1303_;
v___y_1234_ = v_simprocs_1322_;
v___y_1235_ = v_dischargeWrapper_1323_;
v___y_1236_ = v_stxForSuggestion_1308_;
v___y_1237_ = v___y_1315_;
v___y_1238_ = v___y_1314_;
v___y_1239_ = v___y_1313_;
v___y_1240_ = v___y_1310_;
v___y_1241_ = v___y_1316_;
v___y_1242_ = v___y_1309_;
v___y_1243_ = v___y_1312_;
v___y_1244_ = v___y_1311_;
v___y_1245_ = v_ctx_1321_;
goto v___jp_1232_;
}
else
{
lean_dec_ref(v___y_1304_);
if (v___y_1306_ == 0)
{
lean_object* v_ctx_1324_; lean_object* v_simprocs_1325_; lean_object* v_dischargeWrapper_1326_; 
v_ctx_1324_ = lean_ctor_get(v_a_1320_, 0);
lean_inc_ref(v_ctx_1324_);
v_simprocs_1325_ = lean_ctor_get(v_a_1320_, 1);
lean_inc_ref(v_simprocs_1325_);
v_dischargeWrapper_1326_ = lean_ctor_get(v_a_1320_, 2);
lean_inc(v_dischargeWrapper_1326_);
lean_dec(v_a_1320_);
v___y_1233_ = v___y_1303_;
v___y_1234_ = v_simprocs_1325_;
v___y_1235_ = v_dischargeWrapper_1326_;
v___y_1236_ = v_stxForSuggestion_1308_;
v___y_1237_ = v___y_1315_;
v___y_1238_ = v___y_1314_;
v___y_1239_ = v___y_1313_;
v___y_1240_ = v___y_1310_;
v___y_1241_ = v___y_1316_;
v___y_1242_ = v___y_1309_;
v___y_1243_ = v___y_1312_;
v___y_1244_ = v___y_1311_;
v___y_1245_ = v_ctx_1324_;
goto v___jp_1232_;
}
else
{
lean_object* v_ctx_1327_; lean_object* v_simprocs_1328_; lean_object* v_dischargeWrapper_1329_; lean_object* v___x_1330_; 
v_ctx_1327_ = lean_ctor_get(v_a_1320_, 0);
lean_inc_ref(v_ctx_1327_);
v_simprocs_1328_ = lean_ctor_get(v_a_1320_, 1);
lean_inc_ref(v_simprocs_1328_);
v_dischargeWrapper_1329_ = lean_ctor_get(v_a_1320_, 2);
lean_inc(v_dischargeWrapper_1329_);
lean_dec(v_a_1320_);
v___x_1330_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1327_);
v___y_1233_ = v___y_1303_;
v___y_1234_ = v_simprocs_1328_;
v___y_1235_ = v_dischargeWrapper_1329_;
v___y_1236_ = v_stxForSuggestion_1308_;
v___y_1237_ = v___y_1315_;
v___y_1238_ = v___y_1314_;
v___y_1239_ = v___y_1313_;
v___y_1240_ = v___y_1310_;
v___y_1241_ = v___y_1316_;
v___y_1242_ = v___y_1309_;
v___y_1243_ = v___y_1312_;
v___y_1244_ = v___y_1311_;
v___y_1245_ = v___x_1330_;
goto v___jp_1232_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_stxForSuggestion_1308_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_tk_1231_);
v_a_1331_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1319_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1319_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
v___jp_1339_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_inc_ref(v___y_1347_);
v___x_1363_ = l_Array_append___redArg(v___y_1347_, v___y_1362_);
lean_dec_ref(v___y_1362_);
lean_inc(v___y_1357_);
lean_inc(v___y_1359_);
v___x_1364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1364_, 0, v___y_1359_);
lean_ctor_set(v___x_1364_, 1, v___y_1357_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
v___x_1365_ = l_Lean_Syntax_node6(v___y_1359_, v___y_1360_, v___y_1358_, v___y_1342_, v___y_1353_, v___y_1361_, v___y_1343_, v___x_1364_);
v___y_1303_ = v___y_1340_;
v___y_1304_ = v___y_1351_;
v___y_1305_ = v___y_1350_;
v___y_1306_ = v___y_1341_;
v___y_1307_ = v___y_1348_;
v_stxForSuggestion_1308_ = v___x_1365_;
v___y_1309_ = v___y_1352_;
v___y_1310_ = v___y_1345_;
v___y_1311_ = v___y_1344_;
v___y_1312_ = v___y_1349_;
v___y_1313_ = v___y_1346_;
v___y_1314_ = v___y_1356_;
v___y_1315_ = v___y_1355_;
v___y_1316_ = v___y_1354_;
goto v___jp_1302_;
}
v___jp_1366_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_inc_ref_n(v___y_1374_, 2);
v___x_1390_ = l_Array_append___redArg(v___y_1374_, v___y_1389_);
lean_dec_ref(v___y_1389_);
lean_inc_n(v___y_1384_, 3);
lean_inc_n(v___y_1387_, 5);
v___x_1391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1387_);
lean_ctor_set(v___x_1391_, 1, v___y_1384_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1387_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1395_ = l_Lean_Syntax_SepArray_ofElems(v___x_1394_, v___y_1371_);
lean_dec_ref(v___y_1371_);
v___x_1396_ = l_Array_append___redArg(v___y_1374_, v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1397_, 0, v___y_1387_);
lean_ctor_set(v___x_1397_, 1, v___y_1384_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___y_1387_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_Syntax_node3(v___y_1387_, v___y_1384_, v___x_1393_, v___x_1397_, v___x_1399_);
if (lean_obj_tag(v___y_1386_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1402_; 
v_val_1401_ = lean_ctor_get(v___y_1386_, 0);
lean_inc(v_val_1401_);
lean_dec_ref(v___y_1386_);
v___x_1402_ = l_Array_mkArray1___redArg(v_val_1401_);
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___x_1400_;
v___y_1344_ = v___y_1370_;
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___y_1376_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1377_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___y_1387_;
v___y_1360_ = v___y_1388_;
v___y_1361_ = v___x_1391_;
v___y_1362_ = v___x_1402_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1403_; 
lean_dec(v___y_1386_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___x_1400_;
v___y_1344_ = v___y_1370_;
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___y_1376_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1377_;
v___y_1353_ = v___y_1380_;
v___y_1354_ = v___y_1381_;
v___y_1355_ = v___y_1382_;
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___y_1387_;
v___y_1360_ = v___y_1388_;
v___y_1361_ = v___x_1391_;
v___y_1362_ = v___x_1403_;
goto v___jp_1339_;
}
}
v___jp_1404_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_inc_ref(v___y_1413_);
v___x_1428_ = l_Array_append___redArg(v___y_1413_, v___y_1427_);
lean_dec_ref(v___y_1427_);
lean_inc(v___y_1422_);
lean_inc(v___y_1425_);
v___x_1429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1429_, 0, v___y_1425_);
lean_ctor_set(v___x_1429_, 1, v___y_1422_);
lean_ctor_set(v___x_1429_, 2, v___x_1428_);
if (lean_obj_tag(v___y_1408_) == 1)
{
lean_object* v_val_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_val_1430_ = lean_ctor_get(v___y_1408_, 0);
lean_inc(v_val_1430_);
lean_dec_ref(v___y_1408_);
v___x_1431_ = l_Lean_SourceInfo_fromRef(v_val_1430_, v___x_1215_);
lean_dec(v_val_1430_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = l_Array_mkArray1___redArg(v___x_1433_);
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1409_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1411_;
v___y_1373_ = v___y_1412_;
v___y_1374_ = v___y_1413_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1415_;
v___y_1377_ = v___y_1418_;
v___y_1378_ = v___y_1417_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___x_1429_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1423_;
v___y_1386_ = v___y_1424_;
v___y_1387_ = v___y_1425_;
v___y_1388_ = v___y_1426_;
v___y_1389_ = v___x_1434_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1435_; 
lean_dec(v___y_1408_);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1409_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1411_;
v___y_1373_ = v___y_1412_;
v___y_1374_ = v___y_1413_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1415_;
v___y_1377_ = v___y_1418_;
v___y_1378_ = v___y_1417_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___x_1429_;
v___y_1381_ = v___y_1419_;
v___y_1382_ = v___y_1420_;
v___y_1383_ = v___y_1421_;
v___y_1384_ = v___y_1422_;
v___y_1385_ = v___y_1423_;
v___y_1386_ = v___y_1424_;
v___y_1387_ = v___y_1425_;
v___y_1388_ = v___y_1426_;
v___y_1389_ = v___x_1435_;
goto v___jp_1366_;
}
}
v___jp_1436_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_inc_ref(v___y_1452_);
v___x_1460_ = l_Array_append___redArg(v___y_1452_, v___y_1459_);
lean_dec_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc(v___y_1438_);
v___x_1461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1438_);
lean_ctor_set(v___x_1461_, 1, v___y_1458_);
lean_ctor_set(v___x_1461_, 2, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node6(v___y_1438_, v___y_1447_, v___y_1448_, v___y_1440_, v___y_1445_, v___y_1442_, v___y_1457_, v___x_1461_);
v___y_1303_ = v___y_1437_;
v___y_1304_ = v___y_1451_;
v___y_1305_ = v___y_1450_;
v___y_1306_ = v___y_1439_;
v___y_1307_ = v___y_1446_;
v_stxForSuggestion_1308_ = v___x_1462_;
v___y_1309_ = v___y_1453_;
v___y_1310_ = v___y_1443_;
v___y_1311_ = v___y_1441_;
v___y_1312_ = v___y_1449_;
v___y_1313_ = v___y_1444_;
v___y_1314_ = v___y_1456_;
v___y_1315_ = v___y_1455_;
v___y_1316_ = v___y_1454_;
goto v___jp_1302_;
}
v___jp_1463_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_inc_ref_n(v___y_1480_, 2);
v___x_1487_ = l_Array_append___redArg(v___y_1480_, v___y_1486_);
lean_dec_ref(v___y_1486_);
lean_inc_n(v___y_1485_, 3);
lean_inc_n(v___y_1465_, 5);
v___x_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1465_);
lean_ctor_set(v___x_1488_, 1, v___y_1485_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1465_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1492_ = l_Lean_Syntax_SepArray_ofElems(v___x_1491_, v___y_1469_);
lean_dec_ref(v___y_1469_);
v___x_1493_ = l_Array_append___redArg(v___y_1480_, v___x_1492_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1465_);
lean_ctor_set(v___x_1494_, 1, v___y_1485_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1465_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_Syntax_node3(v___y_1465_, v___y_1485_, v___x_1490_, v___x_1494_, v___x_1496_);
if (lean_obj_tag(v___y_1484_) == 1)
{
lean_object* v_val_1498_; lean_object* v___x_1499_; 
v_val_1498_ = lean_ctor_get(v___y_1484_, 0);
lean_inc(v_val_1498_);
lean_dec_ref(v___y_1484_);
v___x_1499_ = l_Array_mkArray1___redArg(v_val_1498_);
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___y_1468_;
v___y_1442_ = v___x_1488_;
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1472_;
v___y_1446_ = v___y_1473_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1476_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1479_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1480_;
v___y_1453_ = v___y_1477_;
v___y_1454_ = v___y_1481_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___x_1497_;
v___y_1458_ = v___y_1485_;
v___y_1459_ = v___x_1499_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1500_; 
lean_dec(v___y_1484_);
v___x_1500_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1466_;
v___y_1440_ = v___y_1467_;
v___y_1441_ = v___y_1468_;
v___y_1442_ = v___x_1488_;
v___y_1443_ = v___y_1470_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1472_;
v___y_1446_ = v___y_1473_;
v___y_1447_ = v___y_1475_;
v___y_1448_ = v___y_1476_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1479_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1480_;
v___y_1453_ = v___y_1477_;
v___y_1454_ = v___y_1481_;
v___y_1455_ = v___y_1482_;
v___y_1456_ = v___y_1483_;
v___y_1457_ = v___x_1497_;
v___y_1458_ = v___y_1485_;
v___y_1459_ = v___x_1500_;
goto v___jp_1436_;
}
}
v___jp_1501_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_inc_ref(v___y_1518_);
v___x_1525_ = l_Array_append___redArg(v___y_1518_, v___y_1524_);
lean_dec_ref(v___y_1524_);
lean_inc(v___y_1523_);
lean_inc(v___y_1503_);
v___x_1526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1526_, 0, v___y_1503_);
lean_ctor_set(v___x_1526_, 1, v___y_1523_);
lean_ctor_set(v___x_1526_, 2, v___x_1525_);
if (lean_obj_tag(v___y_1506_) == 1)
{
lean_object* v_val_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_val_1527_ = lean_ctor_get(v___y_1506_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v___y_1506_);
v___x_1528_ = l_Lean_SourceInfo_fromRef(v_val_1527_, v___x_1215_);
lean_dec(v_val_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_Array_mkArray1___redArg(v___x_1530_);
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___y_1504_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___y_1508_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___y_1510_;
v___y_1472_ = v___x_1526_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1517_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1515_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1522_;
v___y_1485_ = v___y_1523_;
v___y_1486_ = v___x_1531_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1532_; 
lean_dec(v___y_1506_);
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1503_;
v___y_1466_ = v___y_1504_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___y_1508_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___y_1510_;
v___y_1472_ = v___x_1526_;
v___y_1473_ = v___y_1511_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1517_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v___y_1515_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___y_1519_;
v___y_1482_ = v___y_1520_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1522_;
v___y_1485_ = v___y_1523_;
v___y_1486_ = v___x_1532_;
goto v___jp_1463_;
}
}
v___jp_1533_:
{
lean_object* v_ref_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_ref_1553_ = lean_ctor_get(v___y_1549_, 5);
v___x_1554_ = l_Lean_SourceInfo_fromRef(v_ref_1553_, v___y_1552_);
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1556_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1555_);
v___x_1557_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1555_);
v___x_1559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1560_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1544_) == 1)
{
lean_object* v_val_1561_; lean_object* v___x_1562_; 
v_val_1561_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_val_1561_);
lean_dec_ref(v___y_1544_);
v___x_1562_ = l_Array_mkArray1___redArg(v_val_1561_);
v___y_1502_ = v___y_1534_;
v___y_1503_ = v___x_1554_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___y_1536_;
v___y_1506_ = v___y_1537_;
v___y_1507_ = v___y_1538_;
v___y_1508_ = v___y_1539_;
v___y_1509_ = v___y_1540_;
v___y_1510_ = v___y_1541_;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1543_;
v___y_1513_ = v___x_1556_;
v___y_1514_ = v___x_1558_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1547_;
v___y_1517_ = v___y_1545_;
v___y_1518_ = v___x_1560_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___y_1549_;
v___y_1521_ = v___y_1550_;
v___y_1522_ = v___y_1551_;
v___y_1523_ = v___x_1559_;
v___y_1524_ = v___x_1562_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1563_; 
lean_dec(v___y_1544_);
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1502_ = v___y_1534_;
v___y_1503_ = v___x_1554_;
v___y_1504_ = v___y_1535_;
v___y_1505_ = v___y_1536_;
v___y_1506_ = v___y_1537_;
v___y_1507_ = v___y_1538_;
v___y_1508_ = v___y_1539_;
v___y_1509_ = v___y_1540_;
v___y_1510_ = v___y_1541_;
v___y_1511_ = v___y_1542_;
v___y_1512_ = v___y_1543_;
v___y_1513_ = v___x_1556_;
v___y_1514_ = v___x_1558_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1547_;
v___y_1517_ = v___y_1545_;
v___y_1518_ = v___x_1560_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___y_1549_;
v___y_1521_ = v___y_1550_;
v___y_1522_ = v___y_1551_;
v___y_1523_ = v___x_1559_;
v___y_1524_ = v___x_1563_;
goto v___jp_1501_;
}
}
v___jp_1564_:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1571_);
if (lean_obj_tag(v___y_1568_) == 0)
{
lean_object* v_a_1584_; uint8_t v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = 0;
v___y_1534_ = v___y_1565_;
v___y_1535_ = v___y_1569_;
v___y_1536_ = v_a_1584_;
v___y_1537_ = v___y_1570_;
v___y_1538_ = v___y_1577_;
v___y_1539_ = v___y_1572_;
v___y_1540_ = v___y_1576_;
v___y_1541_ = v___y_1579_;
v___y_1542_ = v_stxForExecution_1574_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1566_;
v___y_1545_ = v___y_1575_;
v___y_1546_ = v___y_1567_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1582_;
v___y_1549_ = v___y_1581_;
v___y_1550_ = v___y_1580_;
v___y_1551_ = v___y_1573_;
v___y_1552_ = v___x_1585_;
goto v___jp_1533_;
}
else
{
if (v___y_1569_ == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1583_);
v___y_1534_ = v___y_1565_;
v___y_1535_ = v___y_1569_;
v___y_1536_ = v_a_1586_;
v___y_1537_ = v___y_1570_;
v___y_1538_ = v___y_1577_;
v___y_1539_ = v___y_1572_;
v___y_1540_ = v___y_1576_;
v___y_1541_ = v___y_1579_;
v___y_1542_ = v_stxForExecution_1574_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1566_;
v___y_1545_ = v___y_1575_;
v___y_1546_ = v___y_1567_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1582_;
v___y_1549_ = v___y_1581_;
v___y_1550_ = v___y_1580_;
v___y_1551_ = v___y_1573_;
v___y_1552_ = v___y_1569_;
goto v___jp_1533_;
}
else
{
lean_object* v_a_1587_; lean_object* v_ref_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1587_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1583_);
v_ref_1588_ = lean_ctor_get(v___y_1581_, 5);
v___x_1589_ = 0;
v___x_1590_ = l_Lean_SourceInfo_fromRef(v_ref_1588_, v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1592_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1591_);
v___x_1593_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1597_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1566_) == 1)
{
lean_object* v_val_1598_; lean_object* v___x_1599_; 
v_val_1598_ = lean_ctor_get(v___y_1566_, 0);
lean_inc(v_val_1598_);
lean_dec_ref(v___y_1566_);
v___x_1599_ = l_Array_mkArray1___redArg(v_val_1598_);
v___y_1405_ = v___y_1565_;
v___y_1406_ = v___y_1569_;
v___y_1407_ = v_a_1587_;
v___y_1408_ = v___y_1570_;
v___y_1409_ = v___y_1577_;
v___y_1410_ = v___y_1572_;
v___y_1411_ = v___y_1576_;
v___y_1412_ = v___y_1579_;
v___y_1413_ = v___x_1597_;
v___y_1414_ = v_stxForExecution_1574_;
v___y_1415_ = v___y_1578_;
v___y_1416_ = v___y_1568_;
v___y_1417_ = v___y_1567_;
v___y_1418_ = v___y_1575_;
v___y_1419_ = v___y_1582_;
v___y_1420_ = v___y_1581_;
v___y_1421_ = v___y_1580_;
v___y_1422_ = v___x_1596_;
v___y_1423_ = v___x_1595_;
v___y_1424_ = v___y_1573_;
v___y_1425_ = v___x_1590_;
v___y_1426_ = v___x_1592_;
v___y_1427_ = v___x_1599_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1600_; 
lean_dec(v___y_1566_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1405_ = v___y_1565_;
v___y_1406_ = v___y_1569_;
v___y_1407_ = v_a_1587_;
v___y_1408_ = v___y_1570_;
v___y_1409_ = v___y_1577_;
v___y_1410_ = v___y_1572_;
v___y_1411_ = v___y_1576_;
v___y_1412_ = v___y_1579_;
v___y_1413_ = v___x_1597_;
v___y_1414_ = v_stxForExecution_1574_;
v___y_1415_ = v___y_1578_;
v___y_1416_ = v___y_1568_;
v___y_1417_ = v___y_1567_;
v___y_1418_ = v___y_1575_;
v___y_1419_ = v___y_1582_;
v___y_1420_ = v___y_1581_;
v___y_1421_ = v___y_1580_;
v___y_1422_ = v___x_1596_;
v___y_1423_ = v___x_1595_;
v___y_1424_ = v___y_1573_;
v___y_1425_ = v___x_1590_;
v___y_1426_ = v___x_1592_;
v___y_1427_ = v___x_1600_;
goto v___jp_1404_;
}
}
}
}
v___jp_1601_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_inc_ref(v___y_1608_);
v___x_1628_ = l_Array_append___redArg(v___y_1608_, v___y_1627_);
lean_dec_ref(v___y_1627_);
lean_inc(v___y_1614_);
lean_inc(v___y_1626_);
v___x_1629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1626_);
lean_ctor_set(v___x_1629_, 1, v___y_1614_);
lean_ctor_set(v___x_1629_, 2, v___x_1628_);
lean_inc(v___y_1604_);
v___x_1630_ = l_Lean_Syntax_node6(v___y_1626_, v___y_1616_, v___y_1607_, v___y_1604_, v___y_1624_, v___y_1603_, v___y_1621_, v___x_1629_);
v___y_1565_ = v___y_1602_;
v___y_1566_ = v___y_1622_;
v___y_1567_ = v___y_1609_;
v___y_1568_ = v___y_1610_;
v___y_1569_ = v___y_1617_;
v___y_1570_ = v___y_1618_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1613_;
v_stxForExecution_1574_ = v___x_1630_;
v___y_1575_ = v___y_1619_;
v___y_1576_ = v___y_1606_;
v___y_1577_ = v___y_1615_;
v___y_1578_ = v___y_1625_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1620_;
v___y_1581_ = v___y_1612_;
v___y_1582_ = v___y_1623_;
goto v___jp_1564_;
}
v___jp_1631_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_inc_ref_n(v___y_1644_, 2);
v___x_1656_ = l_Array_append___redArg(v___y_1644_, v___y_1655_);
lean_dec_ref(v___y_1655_);
lean_inc_n(v___y_1654_, 3);
lean_inc_n(v___y_1651_, 5);
v___x_1657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1657_, 0, v___y_1651_);
lean_ctor_set(v___x_1657_, 1, v___y_1654_);
lean_ctor_set(v___x_1657_, 2, v___x_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___y_1651_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1661_ = l_Lean_Syntax_SepArray_ofElems(v___x_1660_, v___y_1638_);
v___x_1662_ = l_Array_append___redArg(v___y_1644_, v___x_1661_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1651_);
lean_ctor_set(v___x_1663_, 1, v___y_1654_);
lean_ctor_set(v___x_1663_, 2, v___x_1662_);
v___x_1664_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1651_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_Syntax_node3(v___y_1651_, v___y_1654_, v___x_1659_, v___x_1663_, v___x_1665_);
if (lean_obj_tag(v___y_1653_) == 1)
{
lean_object* v_val_1667_; lean_object* v___x_1668_; 
v_val_1667_ = lean_ctor_get(v___y_1653_, 0);
lean_inc(v_val_1667_);
v___x_1668_ = l_Array_mkArray1___redArg(v_val_1667_);
v___y_1602_ = v___y_1632_;
v___y_1603_ = v___x_1657_;
v___y_1604_ = v___y_1637_;
v___y_1605_ = v___y_1638_;
v___y_1606_ = v___y_1641_;
v___y_1607_ = v___y_1642_;
v___y_1608_ = v___y_1644_;
v___y_1609_ = v___y_1645_;
v___y_1610_ = v___y_1646_;
v___y_1611_ = v___y_1648_;
v___y_1612_ = v___y_1652_;
v___y_1613_ = v___y_1653_;
v___y_1614_ = v___y_1654_;
v___y_1615_ = v___y_1633_;
v___y_1616_ = v___y_1634_;
v___y_1617_ = v___y_1635_;
v___y_1618_ = v___y_1636_;
v___y_1619_ = v___y_1639_;
v___y_1620_ = v___y_1640_;
v___y_1621_ = v___x_1666_;
v___y_1622_ = v___y_1643_;
v___y_1623_ = v___y_1647_;
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___x_1668_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1602_ = v___y_1632_;
v___y_1603_ = v___x_1657_;
v___y_1604_ = v___y_1637_;
v___y_1605_ = v___y_1638_;
v___y_1606_ = v___y_1641_;
v___y_1607_ = v___y_1642_;
v___y_1608_ = v___y_1644_;
v___y_1609_ = v___y_1645_;
v___y_1610_ = v___y_1646_;
v___y_1611_ = v___y_1648_;
v___y_1612_ = v___y_1652_;
v___y_1613_ = v___y_1653_;
v___y_1614_ = v___y_1654_;
v___y_1615_ = v___y_1633_;
v___y_1616_ = v___y_1634_;
v___y_1617_ = v___y_1635_;
v___y_1618_ = v___y_1636_;
v___y_1619_ = v___y_1639_;
v___y_1620_ = v___y_1640_;
v___y_1621_ = v___x_1666_;
v___y_1622_ = v___y_1643_;
v___y_1623_ = v___y_1647_;
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___x_1669_;
goto v___jp_1601_;
}
}
v___jp_1670_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_ref(v___y_1685_);
v___x_1694_ = l_Array_append___redArg(v___y_1685_, v___y_1693_);
lean_dec_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc(v___y_1690_);
v___x_1695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1690_);
lean_ctor_set(v___x_1695_, 1, v___y_1692_);
lean_ctor_set(v___x_1695_, 2, v___x_1694_);
if (lean_obj_tag(v___y_1675_) == 1)
{
lean_object* v_val_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1696_ = lean_ctor_get(v___y_1675_, 0);
v___x_1697_ = l_Lean_SourceInfo_fromRef(v_val_1696_, v___x_1215_);
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Array_mkArray1___redArg(v___x_1699_);
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1684_;
v___y_1644_ = v___y_1685_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1682_;
v___y_1647_ = v___y_1687_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___x_1695_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1690_;
v___y_1652_ = v___y_1688_;
v___y_1653_ = v___y_1691_;
v___y_1654_ = v___y_1692_;
v___y_1655_ = v___x_1700_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1675_;
v___y_1637_ = v___y_1676_;
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___y_1678_;
v___y_1640_ = v___y_1679_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1681_;
v___y_1643_ = v___y_1684_;
v___y_1644_ = v___y_1685_;
v___y_1645_ = v___y_1683_;
v___y_1646_ = v___y_1682_;
v___y_1647_ = v___y_1687_;
v___y_1648_ = v___y_1686_;
v___y_1649_ = v___x_1695_;
v___y_1650_ = v___y_1689_;
v___y_1651_ = v___y_1690_;
v___y_1652_ = v___y_1688_;
v___y_1653_ = v___y_1691_;
v___y_1654_ = v___y_1692_;
v___y_1655_ = v___x_1701_;
goto v___jp_1631_;
}
}
v___jp_1702_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_inc_ref(v___y_1705_);
v___x_1729_ = l_Array_append___redArg(v___y_1705_, v___y_1728_);
lean_dec_ref(v___y_1728_);
lean_inc(v___y_1708_);
lean_inc(v___y_1717_);
v___x_1730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1730_, 0, v___y_1717_);
lean_ctor_set(v___x_1730_, 1, v___y_1708_);
lean_ctor_set(v___x_1730_, 2, v___x_1729_);
lean_inc(v___y_1704_);
v___x_1731_ = l_Lean_Syntax_node6(v___y_1717_, v___y_1722_, v___y_1711_, v___y_1704_, v___y_1715_, v___y_1727_, v___y_1713_, v___x_1730_);
v___y_1565_ = v___y_1703_;
v___y_1566_ = v___y_1724_;
v___y_1567_ = v___y_1709_;
v___y_1568_ = v___y_1710_;
v___y_1569_ = v___y_1719_;
v___y_1570_ = v___y_1720_;
v___y_1571_ = v___y_1704_;
v___y_1572_ = v___y_1706_;
v___y_1573_ = v___y_1716_;
v_stxForExecution_1574_ = v___x_1731_;
v___y_1575_ = v___y_1721_;
v___y_1576_ = v___y_1707_;
v___y_1577_ = v___y_1718_;
v___y_1578_ = v___y_1726_;
v___y_1579_ = v___y_1712_;
v___y_1580_ = v___y_1723_;
v___y_1581_ = v___y_1714_;
v___y_1582_ = v___y_1725_;
goto v___jp_1564_;
}
v___jp_1732_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_inc_ref_n(v___y_1737_, 2);
v___x_1757_ = l_Array_append___redArg(v___y_1737_, v___y_1756_);
lean_dec_ref(v___y_1756_);
lean_inc_n(v___y_1745_, 3);
lean_inc_n(v___y_1755_, 5);
v___x_1758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1755_);
lean_ctor_set(v___x_1758_, 1, v___y_1745_);
lean_ctor_set(v___x_1758_, 2, v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___y_1755_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1762_ = l_Lean_Syntax_SepArray_ofElems(v___x_1761_, v___y_1739_);
v___x_1763_ = l_Array_append___redArg(v___y_1737_, v___x_1762_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1764_, 0, v___y_1755_);
lean_ctor_set(v___x_1764_, 1, v___y_1745_);
lean_ctor_set(v___x_1764_, 2, v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___y_1755_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = l_Lean_Syntax_node3(v___y_1755_, v___y_1745_, v___x_1760_, v___x_1764_, v___x_1766_);
if (lean_obj_tag(v___y_1754_) == 1)
{
lean_object* v_val_1768_; lean_object* v___x_1769_; 
v_val_1768_ = lean_ctor_get(v___y_1754_, 0);
lean_inc(v_val_1768_);
v___x_1769_ = l_Array_mkArray1___redArg(v_val_1768_);
v___y_1703_ = v___y_1733_;
v___y_1704_ = v___y_1738_;
v___y_1705_ = v___y_1737_;
v___y_1706_ = v___y_1739_;
v___y_1707_ = v___y_1743_;
v___y_1708_ = v___y_1745_;
v___y_1709_ = v___y_1746_;
v___y_1710_ = v___y_1747_;
v___y_1711_ = v___y_1749_;
v___y_1712_ = v___y_1750_;
v___y_1713_ = v___x_1767_;
v___y_1714_ = v___y_1752_;
v___y_1715_ = v___y_1753_;
v___y_1716_ = v___y_1754_;
v___y_1717_ = v___y_1755_;
v___y_1718_ = v___y_1734_;
v___y_1719_ = v___y_1735_;
v___y_1720_ = v___y_1736_;
v___y_1721_ = v___y_1740_;
v___y_1722_ = v___y_1741_;
v___y_1723_ = v___y_1742_;
v___y_1724_ = v___y_1744_;
v___y_1725_ = v___y_1748_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___x_1758_;
v___y_1728_ = v___x_1769_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1703_ = v___y_1733_;
v___y_1704_ = v___y_1738_;
v___y_1705_ = v___y_1737_;
v___y_1706_ = v___y_1739_;
v___y_1707_ = v___y_1743_;
v___y_1708_ = v___y_1745_;
v___y_1709_ = v___y_1746_;
v___y_1710_ = v___y_1747_;
v___y_1711_ = v___y_1749_;
v___y_1712_ = v___y_1750_;
v___y_1713_ = v___x_1767_;
v___y_1714_ = v___y_1752_;
v___y_1715_ = v___y_1753_;
v___y_1716_ = v___y_1754_;
v___y_1717_ = v___y_1755_;
v___y_1718_ = v___y_1734_;
v___y_1719_ = v___y_1735_;
v___y_1720_ = v___y_1736_;
v___y_1721_ = v___y_1740_;
v___y_1722_ = v___y_1741_;
v___y_1723_ = v___y_1742_;
v___y_1724_ = v___y_1744_;
v___y_1725_ = v___y_1748_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___x_1758_;
v___y_1728_ = v___x_1770_;
goto v___jp_1702_;
}
}
v___jp_1771_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_inc_ref(v___y_1775_);
v___x_1795_ = l_Array_append___redArg(v___y_1775_, v___y_1794_);
lean_dec_ref(v___y_1794_);
lean_inc(v___y_1786_);
lean_inc(v___y_1793_);
v___x_1796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1796_, 0, v___y_1793_);
lean_ctor_set(v___x_1796_, 1, v___y_1786_);
lean_ctor_set(v___x_1796_, 2, v___x_1795_);
if (lean_obj_tag(v___y_1776_) == 1)
{
lean_object* v_val_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_val_1797_ = lean_ctor_get(v___y_1776_, 0);
v___x_1798_ = l_Lean_SourceInfo_fromRef(v_val_1797_, v___x_1215_);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Array_mkArray1___redArg(v___x_1800_);
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1776_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1777_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1782_;
v___y_1744_ = v___y_1785_;
v___y_1745_ = v___y_1786_;
v___y_1746_ = v___y_1784_;
v___y_1747_ = v___y_1783_;
v___y_1748_ = v___y_1789_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1787_;
v___y_1751_ = v___y_1791_;
v___y_1752_ = v___y_1790_;
v___y_1753_ = v___x_1796_;
v___y_1754_ = v___y_1792_;
v___y_1755_ = v___y_1793_;
v___y_1756_ = v___x_1801_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1733_ = v___y_1772_;
v___y_1734_ = v___y_1773_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1776_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1777_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1779_;
v___y_1741_ = v___y_1780_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1782_;
v___y_1744_ = v___y_1785_;
v___y_1745_ = v___y_1786_;
v___y_1746_ = v___y_1784_;
v___y_1747_ = v___y_1783_;
v___y_1748_ = v___y_1789_;
v___y_1749_ = v___y_1788_;
v___y_1750_ = v___y_1787_;
v___y_1751_ = v___y_1791_;
v___y_1752_ = v___y_1790_;
v___y_1753_ = v___x_1796_;
v___y_1754_ = v___y_1792_;
v___y_1755_ = v___y_1793_;
v___y_1756_ = v___x_1802_;
goto v___jp_1732_;
}
}
v___jp_1803_:
{
lean_object* v_ref_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_ref_1822_ = lean_ctor_get(v___y_1819_, 5);
v___x_1823_ = l_Lean_SourceInfo_fromRef(v_ref_1822_, v___y_1821_);
v___x_1824_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_1825_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1824_);
v___x_1826_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___x_1824_);
v___x_1828_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1829_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1815_) == 1)
{
lean_object* v_val_1830_; lean_object* v___x_1831_; 
v_val_1830_ = lean_ctor_get(v___y_1815_, 0);
lean_inc(v_val_1830_);
v___x_1831_ = l_Array_mkArray1___redArg(v_val_1830_);
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1805_;
v___y_1774_ = v___y_1806_;
v___y_1775_ = v___x_1829_;
v___y_1776_ = v___y_1807_;
v___y_1777_ = v___y_1808_;
v___y_1778_ = v___y_1809_;
v___y_1779_ = v___y_1810_;
v___y_1780_ = v___x_1825_;
v___y_1781_ = v___y_1811_;
v___y_1782_ = v___y_1812_;
v___y_1783_ = v___y_1813_;
v___y_1784_ = v___y_1814_;
v___y_1785_ = v___y_1815_;
v___y_1786_ = v___x_1828_;
v___y_1787_ = v___y_1817_;
v___y_1788_ = v___x_1827_;
v___y_1789_ = v___y_1816_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1818_;
v___y_1792_ = v___y_1820_;
v___y_1793_ = v___x_1823_;
v___y_1794_ = v___x_1831_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1772_ = v___y_1804_;
v___y_1773_ = v___y_1805_;
v___y_1774_ = v___y_1806_;
v___y_1775_ = v___x_1829_;
v___y_1776_ = v___y_1807_;
v___y_1777_ = v___y_1808_;
v___y_1778_ = v___y_1809_;
v___y_1779_ = v___y_1810_;
v___y_1780_ = v___x_1825_;
v___y_1781_ = v___y_1811_;
v___y_1782_ = v___y_1812_;
v___y_1783_ = v___y_1813_;
v___y_1784_ = v___y_1814_;
v___y_1785_ = v___y_1815_;
v___y_1786_ = v___x_1828_;
v___y_1787_ = v___y_1817_;
v___y_1788_ = v___x_1827_;
v___y_1789_ = v___y_1816_;
v___y_1790_ = v___y_1819_;
v___y_1791_ = v___y_1818_;
v___y_1792_ = v___y_1820_;
v___y_1793_ = v___x_1823_;
v___y_1794_ = v___x_1832_;
goto v___jp_1771_;
}
}
v___jp_1833_:
{
if (lean_obj_tag(v___y_1835_) == 0)
{
uint8_t v___x_1851_; 
v___x_1851_ = 0;
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1845_;
v___y_1806_ = v___y_1838_;
v___y_1807_ = v___y_1840_;
v___y_1808_ = v___y_1839_;
v___y_1809_ = v_argsArray_1842_;
v___y_1810_ = v___y_1843_;
v___y_1811_ = v___y_1848_;
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___y_1835_;
v___y_1814_ = v___y_1836_;
v___y_1815_ = v___y_1837_;
v___y_1816_ = v___y_1850_;
v___y_1817_ = v___y_1847_;
v___y_1818_ = v___y_1846_;
v___y_1819_ = v___y_1849_;
v___y_1820_ = v___y_1841_;
v___y_1821_ = v___x_1851_;
goto v___jp_1803_;
}
else
{
if (v___y_1838_ == 0)
{
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1845_;
v___y_1806_ = v___y_1838_;
v___y_1807_ = v___y_1840_;
v___y_1808_ = v___y_1839_;
v___y_1809_ = v_argsArray_1842_;
v___y_1810_ = v___y_1843_;
v___y_1811_ = v___y_1848_;
v___y_1812_ = v___y_1844_;
v___y_1813_ = v___y_1835_;
v___y_1814_ = v___y_1836_;
v___y_1815_ = v___y_1837_;
v___y_1816_ = v___y_1850_;
v___y_1817_ = v___y_1847_;
v___y_1818_ = v___y_1846_;
v___y_1819_ = v___y_1849_;
v___y_1820_ = v___y_1841_;
v___y_1821_ = v___y_1838_;
goto v___jp_1803_;
}
else
{
lean_object* v_ref_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_ref_1852_ = lean_ctor_get(v___y_1849_, 5);
v___x_1853_ = 0;
v___x_1854_ = l_Lean_SourceInfo_fromRef(v_ref_1852_, v___x_1853_);
v___x_1855_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_1856_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1855_);
v___x_1857_ = l_Lean_SourceInfo_fromRef(v_tk_1231_, v___x_1215_);
v___x_1858_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1861_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1837_) == 1)
{
lean_object* v_val_1862_; lean_object* v___x_1863_; 
v_val_1862_ = lean_ctor_get(v___y_1837_, 0);
lean_inc(v_val_1862_);
v___x_1863_ = l_Array_mkArray1___redArg(v_val_1862_);
v___y_1671_ = v___y_1834_;
v___y_1672_ = v___y_1845_;
v___y_1673_ = v___x_1856_;
v___y_1674_ = v___y_1838_;
v___y_1675_ = v___y_1840_;
v___y_1676_ = v___y_1839_;
v___y_1677_ = v_argsArray_1842_;
v___y_1678_ = v___y_1843_;
v___y_1679_ = v___y_1848_;
v___y_1680_ = v___y_1844_;
v___y_1681_ = v___x_1859_;
v___y_1682_ = v___y_1835_;
v___y_1683_ = v___y_1836_;
v___y_1684_ = v___y_1837_;
v___y_1685_ = v___x_1861_;
v___y_1686_ = v___y_1847_;
v___y_1687_ = v___y_1850_;
v___y_1688_ = v___y_1849_;
v___y_1689_ = v___y_1846_;
v___y_1690_ = v___x_1854_;
v___y_1691_ = v___y_1841_;
v___y_1692_ = v___x_1860_;
v___y_1693_ = v___x_1863_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1864_; 
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1671_ = v___y_1834_;
v___y_1672_ = v___y_1845_;
v___y_1673_ = v___x_1856_;
v___y_1674_ = v___y_1838_;
v___y_1675_ = v___y_1840_;
v___y_1676_ = v___y_1839_;
v___y_1677_ = v_argsArray_1842_;
v___y_1678_ = v___y_1843_;
v___y_1679_ = v___y_1848_;
v___y_1680_ = v___y_1844_;
v___y_1681_ = v___x_1859_;
v___y_1682_ = v___y_1835_;
v___y_1683_ = v___y_1836_;
v___y_1684_ = v___y_1837_;
v___y_1685_ = v___x_1861_;
v___y_1686_ = v___y_1847_;
v___y_1687_ = v___y_1850_;
v___y_1688_ = v___y_1849_;
v___y_1689_ = v___y_1846_;
v___y_1690_ = v___x_1854_;
v___y_1691_ = v___y_1841_;
v___y_1692_ = v___x_1860_;
v___y_1693_ = v___x_1864_;
goto v___jp_1670_;
}
}
}
}
v___jp_1865_:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1873_, v___y_1869_, v___y_1875_, v___y_1867_, v___y_1881_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_LibrarySuggestions_select(v_a_1885_, v___y_1883_, v___y_1869_, v___y_1875_, v___y_1867_, v___y_1881_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; size_t v_sz_1888_; size_t v___x_1889_; lean_object* v___x_1890_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
v_sz_1888_ = lean_array_size(v_a_1887_);
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1887_, v_sz_1888_, v___x_1889_, v___y_1876_, v___y_1870_, v___y_1873_, v___y_1882_, v___y_1874_, v___y_1869_, v___y_1875_, v___y_1867_, v___y_1881_);
lean_dec(v_a_1887_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref(v___x_1890_);
v___y_1834_ = v___y_1866_;
v___y_1835_ = v___y_1877_;
v___y_1836_ = v___y_1878_;
v___y_1837_ = v___y_1879_;
v___y_1838_ = v___y_1868_;
v___y_1839_ = v___y_1872_;
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1880_;
v_argsArray_1842_ = v_a_1891_;
v___y_1843_ = v___y_1870_;
v___y_1844_ = v___y_1873_;
v___y_1845_ = v___y_1882_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1869_;
v___y_1848_ = v___y_1875_;
v___y_1849_ = v___y_1867_;
v___y_1850_ = v___y_1881_;
goto v___jp_1833_;
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1866_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1892_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1890_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1890_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1866_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1900_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1886_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1886_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1866_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1908_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1884_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1884_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
v___jp_1916_:
{
uint8_t v_suggestions_1935_; 
v_suggestions_1935_ = lean_ctor_get_uint8(v___y_1926_, sizeof(void*)*3 + 26);
if (v_suggestions_1935_ == 0)
{
lean_dec_ref(v___y_1926_);
lean_dec_ref(v___f_1219_);
v___y_1834_ = v___y_1917_;
v___y_1835_ = v___y_1928_;
v___y_1836_ = v___y_1929_;
v___y_1837_ = v___y_1930_;
v___y_1838_ = v___y_1919_;
v___y_1839_ = v___y_1923_;
v___y_1840_ = v___y_1922_;
v___y_1841_ = v___y_1931_;
v_argsArray_1842_ = v___y_1934_;
v___y_1843_ = v___y_1921_;
v___y_1844_ = v___y_1924_;
v___y_1845_ = v___y_1932_;
v___y_1846_ = v___y_1925_;
v___y_1847_ = v___y_1920_;
v___y_1848_ = v___y_1927_;
v___y_1849_ = v___y_1918_;
v___y_1850_ = v___y_1933_;
goto v___jp_1833_;
}
else
{
lean_object* v_maxSuggestions_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_maxSuggestions_1936_ = lean_ctor_get(v___y_1926_, 2);
lean_inc(v_maxSuggestions_1936_);
lean_dec_ref(v___y_1926_);
v___x_1937_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1938_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1936_) == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_unsigned_to_nat(100u);
v___x_1940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1937_);
lean_ctor_set(v___x_1940_, 2, v___f_1219_);
lean_ctor_set(v___x_1940_, 3, v___x_1938_);
v___y_1866_ = v___y_1917_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1919_;
v___y_1869_ = v___y_1920_;
v___y_1870_ = v___y_1921_;
v___y_1871_ = v___y_1922_;
v___y_1872_ = v___y_1923_;
v___y_1873_ = v___y_1924_;
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1927_;
v___y_1876_ = v___y_1934_;
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1933_;
v___y_1882_ = v___y_1932_;
v___y_1883_ = v___x_1940_;
goto v___jp_1865_;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1942_; 
v_val_1941_ = lean_ctor_get(v_maxSuggestions_1936_, 0);
lean_inc(v_val_1941_);
lean_dec_ref(v_maxSuggestions_1936_);
v___x_1942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1942_, 0, v_val_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1937_);
lean_ctor_set(v___x_1942_, 2, v___f_1219_);
lean_ctor_set(v___x_1942_, 3, v___x_1938_);
v___y_1866_ = v___y_1917_;
v___y_1867_ = v___y_1918_;
v___y_1868_ = v___y_1919_;
v___y_1869_ = v___y_1920_;
v___y_1870_ = v___y_1921_;
v___y_1871_ = v___y_1922_;
v___y_1872_ = v___y_1923_;
v___y_1873_ = v___y_1924_;
v___y_1874_ = v___y_1925_;
v___y_1875_ = v___y_1927_;
v___y_1876_ = v___y_1934_;
v___y_1877_ = v___y_1928_;
v___y_1878_ = v___y_1929_;
v___y_1879_ = v___y_1930_;
v___y_1880_ = v___y_1931_;
v___y_1881_ = v___y_1933_;
v___y_1882_ = v___y_1932_;
v___y_1883_ = v___x_1942_;
goto v___jp_1865_;
}
}
}
v___jp_1943_:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = 0;
lean_inc(v___y_1946_);
v___x_1960_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1946_, v___x_1959_, v___y_1951_, v___y_1953_, v___y_1949_, v___y_1952_, v___y_1944_, v___y_1955_, v___y_1947_);
if (lean_obj_tag(v___x_1960_) == 0)
{
if (lean_obj_tag(v___y_1950_) == 1)
{
lean_object* v_a_1961_; lean_object* v_val_1962_; lean_object* v___x_1963_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___x_1960_);
v_val_1962_ = lean_ctor_get(v___y_1950_, 0);
lean_inc(v_val_1962_);
lean_dec_ref(v___y_1950_);
v___x_1963_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1962_);
lean_dec(v_val_1962_);
lean_inc(v___y_1948_);
v___y_1917_ = v___y_1948_;
v___y_1918_ = v___y_1955_;
v___y_1919_ = v___y_1957_;
v___y_1920_ = v___y_1952_;
v___y_1921_ = v___y_1951_;
v___y_1922_ = v___y_1945_;
v___y_1923_ = v___y_1946_;
v___y_1924_ = v___y_1956_;
v___y_1925_ = v___y_1949_;
v___y_1926_ = v_a_1961_;
v___y_1927_ = v___y_1944_;
v___y_1928_ = v___y_1954_;
v___y_1929_ = v___x_1959_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1948_;
v___y_1932_ = v___y_1953_;
v___y_1933_ = v___y_1947_;
v___y_1934_ = v___x_1963_;
goto v___jp_1916_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1965_; 
lean_dec(v___y_1950_);
v_a_1964_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1960_);
v___x_1965_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1948_);
v___y_1917_ = v___y_1948_;
v___y_1918_ = v___y_1955_;
v___y_1919_ = v___y_1957_;
v___y_1920_ = v___y_1952_;
v___y_1921_ = v___y_1951_;
v___y_1922_ = v___y_1945_;
v___y_1923_ = v___y_1946_;
v___y_1924_ = v___y_1956_;
v___y_1925_ = v___y_1949_;
v___y_1926_ = v_a_1964_;
v___y_1927_ = v___y_1944_;
v___y_1928_ = v___y_1954_;
v___y_1929_ = v___x_1959_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1948_;
v___y_1932_ = v___y_1953_;
v___y_1933_ = v___y_1947_;
v___y_1934_ = v___x_1965_;
goto v___jp_1916_;
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v___y_1958_);
lean_dec(v___y_1954_);
lean_dec(v___y_1950_);
lean_dec(v___y_1948_);
lean_dec(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v_a_1966_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1960_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1960_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
v___jp_1974_:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Syntax_getOptional_x3f(v___y_1985_);
lean_dec(v___y_1985_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_box(0);
v___y_1944_ = v___y_1983_;
v___y_1945_ = v___y_1981_;
v___y_1946_ = v___y_1980_;
v___y_1947_ = v___y_1987_;
v___y_1948_ = v___y_1989_;
v___y_1949_ = v___y_1982_;
v___y_1950_ = v___y_1986_;
v___y_1951_ = v___y_1978_;
v___y_1952_ = v___y_1977_;
v___y_1953_ = v___y_1988_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1975_;
v___y_1956_ = v___y_1979_;
v___y_1957_ = v___y_1976_;
v___y_1958_ = v___x_1991_;
goto v___jp_1943_;
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_val_1992_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1990_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v___x_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_val_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
v___y_1944_ = v___y_1983_;
v___y_1945_ = v___y_1981_;
v___y_1946_ = v___y_1980_;
v___y_1947_ = v___y_1987_;
v___y_1948_ = v___y_1989_;
v___y_1949_ = v___y_1982_;
v___y_1950_ = v___y_1986_;
v___y_1951_ = v___y_1978_;
v___y_1952_ = v___y_1977_;
v___y_1953_ = v___y_1988_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1975_;
v___y_1956_ = v___y_1979_;
v___y_1957_ = v___y_1976_;
v___y_1958_ = v___x_1997_;
goto v___jp_1943_;
}
}
}
}
v___jp_2000_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = lean_unsigned_to_nat(4u);
v___x_2017_ = l_Lean_Syntax_getArg(v___y_2006_, v___x_2016_);
lean_dec(v___y_2006_);
v___x_2018_ = l_Lean_Syntax_getOptional_x3f(v___x_2017_);
lean_dec(v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_box(0);
v___y_1975_ = v___y_2014_;
v___y_1976_ = v___y_2002_;
v___y_1977_ = v___y_2012_;
v___y_1978_ = v___y_2008_;
v___y_1979_ = v___y_2009_;
v___y_1980_ = v___y_2005_;
v___y_1981_ = v___y_2004_;
v___y_1982_ = v___y_2011_;
v___y_1983_ = v___y_2013_;
v___y_1984_ = v___y_2001_;
v___y_1985_ = v___y_2003_;
v___y_1986_ = v_args_2007_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2010_;
v___y_1989_ = v___x_2019_;
goto v___jp_1974_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_val_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v___y_1975_ = v___y_2014_;
v___y_1976_ = v___y_2002_;
v___y_1977_ = v___y_2012_;
v___y_1978_ = v___y_2008_;
v___y_1979_ = v___y_2009_;
v___y_1980_ = v___y_2005_;
v___y_1981_ = v___y_2004_;
v___y_1982_ = v___y_2011_;
v___y_1983_ = v___y_2013_;
v___y_1984_ = v___y_2001_;
v___y_1985_ = v___y_2003_;
v___y_1986_ = v_args_2007_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2010_;
v___y_1989_ = v___x_2025_;
goto v___jp_1974_;
}
}
}
}
v___jp_2029_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_unsigned_to_nat(3u);
v___x_2045_ = l_Lean_Syntax_getArg(v___y_2034_, v___x_2044_);
v___x_2046_ = l_Lean_Syntax_isNone(v___x_2045_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; 
lean_inc(v___x_2045_);
v___x_2047_ = l_Lean_Syntax_matchesNull(v___x_2045_, v___x_2028_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v___x_2045_);
lean_dec(v_o_2035_);
lean_dec(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec(v___y_2030_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2049_ = l_Lean_Syntax_getArg(v___x_2045_, v___x_1230_);
lean_dec(v___x_2045_);
v___x_2050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_2051_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_2050_);
lean_inc(v___x_2049_);
v___x_2052_ = l_Lean_Syntax_isOfKind(v___x_2049_, v___x_2051_);
lean_dec(v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
lean_dec(v___x_2049_);
lean_dec(v_o_2035_);
lean_dec(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec(v___y_2030_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2053_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v_args_2055_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_Syntax_getArg(v___x_2049_, v___x_2028_);
lean_dec(v___x_2049_);
v_args_2055_ = l_Lean_Syntax_getArgs(v___x_2054_);
lean_dec(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_args_2055_);
v___y_2001_ = v___y_2030_;
v___y_2002_ = v___y_2031_;
v___y_2003_ = v___y_2033_;
v___y_2004_ = v_o_2035_;
v___y_2005_ = v___y_2032_;
v___y_2006_ = v___y_2034_;
v_args_2007_ = v___x_2056_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
goto v___jp_2000_;
}
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v___x_2045_);
v___x_2057_ = lean_box(0);
v___y_2001_ = v___y_2030_;
v___y_2002_ = v___y_2031_;
v___y_2003_ = v___y_2033_;
v___y_2004_ = v_o_2035_;
v___y_2005_ = v___y_2032_;
v___y_2006_ = v___y_2034_;
v_args_2007_ = v___x_2057_;
v___y_2008_ = v___y_2036_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2038_;
v___y_2011_ = v___y_2039_;
v___y_2012_ = v___y_2040_;
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
goto v___jp_2000_;
}
}
v___jp_2058_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = l_Lean_Syntax_getArg(v_stx_1214_, v___x_2068_);
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_2071_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_2070_);
lean_inc(v___x_2069_);
v___x_2072_ = l_Lean_Syntax_isOfKind(v___x_2069_, v___x_2071_);
lean_dec(v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v___x_2069_);
lean_dec(v_bang_2059_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2073_;
}
else
{
lean_object* v_cfg_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_cfg_2074_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_1230_);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1218_);
lean_inc_ref(v___x_1217_);
lean_inc_ref(v___x_1216_);
v___x_2076_ = l_Lean_Name_mkStr4(v___x_1216_, v___x_1217_, v___x_1218_, v___x_2075_);
lean_inc(v_cfg_2074_);
v___x_2077_ = l_Lean_Syntax_isOfKind(v_cfg_2074_, v___x_2076_);
lean_dec(v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v_cfg_2074_);
lean_dec(v___x_2069_);
lean_dec(v_bang_2059_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2028_);
v___x_2080_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2068_);
v___x_2081_ = l_Lean_Syntax_isNone(v___x_2080_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; 
lean_inc(v___x_2080_);
v___x_2082_ = l_Lean_Syntax_matchesNull(v___x_2080_, v___x_2028_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec(v___x_2080_);
lean_dec(v___x_2079_);
lean_dec(v_cfg_2074_);
lean_dec(v___x_2069_);
lean_dec(v_bang_2059_);
lean_dec(v_tk_1231_);
lean_dec_ref(v___f_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___x_1216_);
v___x_2083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2083_;
}
else
{
lean_object* v_o_2084_; lean_object* v___x_2085_; 
v_o_2084_ = l_Lean_Syntax_getArg(v___x_2080_, v___x_1230_);
lean_dec(v___x_2080_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_o_2084_);
v___y_2030_ = v_bang_2059_;
v___y_2031_ = v___x_2077_;
v___y_2032_ = v_cfg_2074_;
v___y_2033_ = v___x_2079_;
v___y_2034_ = v___x_2069_;
v_o_2035_ = v___x_2085_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
goto v___jp_2029_;
}
}
else
{
lean_object* v___x_2086_; 
lean_dec(v___x_2080_);
v___x_2086_ = lean_box(0);
v___y_2030_ = v_bang_2059_;
v___y_2031_ = v___x_2077_;
v___y_2032_ = v_cfg_2074_;
v___y_2033_ = v___x_2079_;
v___y_2034_ = v___x_2069_;
v_o_2035_ = v___x_2086_;
v___y_2036_ = v___y_2060_;
v___y_2037_ = v___y_2061_;
v___y_2038_ = v___y_2062_;
v___y_2039_ = v___y_2063_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
goto v___jp_2029_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2094_, lean_object* v_stx_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v___f_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
uint8_t v___x_40509__boxed_2110_; uint8_t v___x_40510__boxed_2111_; lean_object* v_res_2112_; 
v___x_40509__boxed_2110_ = lean_unbox(v___x_2094_);
v___x_40510__boxed_2111_ = lean_unbox(v___x_2096_);
v_res_2112_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_40509__boxed_2110_, v_stx_2095_, v___x_40510__boxed_2111_, v___x_2097_, v___x_2098_, v___x_2099_, v___f_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_stx_2095_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___f_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___y_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2135_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2122_);
v___x_2136_ = l_Lean_Syntax_isOfKind(v_stx_2122_, v___x_2135_);
v___x_2137_ = 1;
v___f_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2139_ = lean_box(v___x_2136_);
v___x_2140_ = lean_box(v___x_2137_);
v___y_2141_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2141_, 0, v___x_2139_);
lean_closure_set(v___y_2141_, 1, v_stx_2122_);
lean_closure_set(v___y_2141_, 2, v___x_2140_);
lean_closure_set(v___y_2141_, 3, v___x_2132_);
lean_closure_set(v___y_2141_, 4, v___x_2133_);
lean_closure_set(v___y_2141_, 5, v___x_2134_);
lean_closure_set(v___y_2141_, 6, v___f_2138_);
v___x_2142_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2142_, 0, v___y_2141_);
v___x_2143_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2142_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2155_, lean_object* v_as_2156_, lean_object* v_as_x27_2157_, lean_object* v_b_2158_, lean_object* v_a_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2155_, v_as_x27_2157_, v_b_2158_, v___y_2166_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2170_, lean_object* v_as_2171_, lean_object* v_as_x27_2172_, lean_object* v_b_2173_, lean_object* v_a_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2170_, v_as_2171_, v_as_x27_2172_, v_b_2173_, v_a_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v_as_x27_2172_);
lean_dec(v_as_2171_);
lean_dec(v___x_2170_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2185_, lean_object* v_ref_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2186_, v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_ref_2199_, lean_object* v_msg_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2198_, v_ref_2199_, v_msg_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_ref_2199_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2211_, lean_object* v_ref_2212_, lean_object* v_constName_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2212_, v_constName_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_ref_2225_, lean_object* v_constName_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2224_, v_ref_2225_, v_constName_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_ref_2225_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2237_, lean_object* v_msg_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2238_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_msg_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2249_, v_msg_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2261_, v___y_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_opt_2272_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2283_, lean_object* v_ref_2284_, lean_object* v_msg_2285_, lean_object* v_declHint_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2284_, v_msg_2285_, v_declHint_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_ref_2298_, lean_object* v_msg_2299_, lean_object* v_declHint_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2297_, v_ref_2298_, v_msg_2299_, v_declHint_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v_ref_2298_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2311_, lean_object* v_declHint_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2311_, v_declHint_2312_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2323_, lean_object* v_declHint_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2323_, v_declHint_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2335_, lean_object* v_msgData_2336_, uint8_t v_severity_2337_, uint8_t v_isSilent_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2335_, v_msgData_2336_, v_severity_2337_, v_isSilent_2338_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2349_, lean_object* v_msgData_2350_, lean_object* v_severity_2351_, lean_object* v_isSilent_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
uint8_t v_severity_boxed_2362_; uint8_t v_isSilent_boxed_2363_; lean_object* v_res_2364_; 
v_severity_boxed_2362_ = lean_unbox(v_severity_2351_);
v_isSilent_boxed_2363_ = lean_unbox(v_isSilent_2352_);
v_res_2364_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2349_, v_msgData_2350_, v_severity_boxed_2362_, v_isSilent_boxed_2363_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v_ref_2349_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2372_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2375_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2372_, v___x_2373_, v___x_2374_, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2407_ = l_Lean_addBuiltinDeclarationRanges(v___x_2405_, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2410_, lean_object* v_as_x27_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_){
_start:
{
if (lean_obj_tag(v_as_x27_2411_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_b_2412_);
return v___x_2415_;
}
else
{
lean_object* v_head_2416_; lean_object* v_tail_2417_; lean_object* v_ref_2418_; uint8_t v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_head_2416_ = lean_ctor_get(v_as_x27_2411_, 0);
v_tail_2417_ = lean_ctor_get(v_as_x27_2411_, 1);
v_ref_2418_ = lean_ctor_get(v___y_2413_, 5);
v___x_2419_ = 1;
v___x_2420_ = 0;
v___x_2421_ = l_Lean_SourceInfo_fromRef(v_ref_2418_, v___x_2420_);
v___x_2422_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2423_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2424_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2421_);
v___x_2425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2421_);
lean_ctor_set(v___x_2425_, 1, v___x_2423_);
lean_ctor_set(v___x_2425_, 2, v___x_2424_);
lean_inc(v_head_2416_);
v___x_2426_ = l_Lean_mkCIdentFrom(v___x_2410_, v_head_2416_, v___x_2419_);
lean_inc_ref(v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node3(v___x_2421_, v___x_2422_, v___x_2425_, v___x_2425_, v___x_2426_);
v___x_2428_ = lean_array_push(v_b_2412_, v___x_2427_);
v_as_x27_2411_ = v_tail_2417_;
v_b_2412_ = v___x_2428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2430_, lean_object* v_as_x27_2431_, lean_object* v_b_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2430_, v_as_x27_2431_, v_b_2432_, v___y_2433_);
lean_dec_ref(v___y_2433_);
lean_dec(v_as_x27_2431_);
lean_dec(v___x_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_usize_dec_lt(v_i_2438_, v_sz_2437_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_b_2439_);
return v___x_2450_;
}
else
{
lean_object* v_a_2451_; lean_object* v_name_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2451_ = lean_array_uget_borrowed(v_as_2436_, v_i_2438_);
v_name_2452_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_name_2452_);
v___x_2453_ = lean_mk_syntax_ident(v_name_2452_);
lean_inc(v___x_2453_);
v___x_2454_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2453_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2453_, v_a_2455_, v_b_2439_, v___y_2446_);
lean_dec(v_a_2455_);
lean_dec(v___x_2453_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; size_t v___x_2458_; size_t v___x_2459_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_add(v_i_2438_, v___x_2458_);
v_i_2438_ = v___x_2459_;
v_b_2439_ = v_a_2457_;
goto _start;
}
else
{
return v___x_2456_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v___x_2453_);
lean_dec_ref(v_b_2439_);
v_a_2461_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2454_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2454_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2469_, lean_object* v_sz_2470_, lean_object* v_i_2471_, lean_object* v_b_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2470_);
lean_dec(v_sz_2470_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2469_, v_sz_boxed_2482_, v_i_boxed_2483_, v_b_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_as_2469_);
return v_res_2484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_unsigned_to_nat(32u);
v___x_2492_ = lean_mk_empty_array_with_capacity(v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
size_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2494_ = ((size_t)5ULL);
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_unsigned_to_nat(32u);
v___x_2497_ = lean_mk_empty_array_with_capacity(v___x_2496_);
v___x_2498_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2499_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2497_);
lean_ctor_set(v___x_2499_, 2, v___x_2495_);
lean_ctor_set(v___x_2499_, 3, v___x_2495_);
lean_ctor_set_usize(v___x_2499_, 4, v___x_2494_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2501_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2502_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
lean_ctor_set(v___x_2502_, 3, v___x_2500_);
return v___x_2502_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2504_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v___x_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2514_, lean_object* v_stx_2515_, uint8_t v___x_2516_, lean_object* v___x_2517_, lean_object* v___x_2518_, lean_object* v___x_2519_, lean_object* v___f_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
if (v___x_2514_ == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_2530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v_tk_2532_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2647_; lean_object* v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v_stxForSuggestion_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2679_; uint8_t v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; uint8_t v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; uint8_t v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; uint8_t v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2767_; uint8_t v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2797_; uint8_t v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; uint8_t v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; uint8_t v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2861_; uint8_t v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; uint8_t v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; uint8_t v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; uint8_t v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; uint8_t v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; uint8_t v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; uint8_t v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; uint8_t v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; uint8_t v___y_2987_; lean_object* v___y_2988_; uint8_t v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_stxForExecution_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; uint8_t v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3079_; lean_object* v___y_3080_; uint8_t v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3114_; lean_object* v___y_3115_; uint8_t v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; uint8_t v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; uint8_t v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3209_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; uint8_t v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; uint8_t v___y_3337_; uint8_t v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v_argsArray_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; uint8_t v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; uint8_t v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; uint8_t v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; uint8_t v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v_args_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___x_3497_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v_o_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v_bang_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v_tk_2532_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_2531_);
v___x_3497_ = lean_unsigned_to_nat(1u);
v___x_3556_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_3497_);
v___x_3557_ = l_Lean_Syntax_isNone(v___x_3556_);
if (v___x_3557_ == 0)
{
uint8_t v___x_3558_; 
lean_inc(v___x_3556_);
v___x_3558_ = l_Lean_Syntax_matchesNull(v___x_3556_, v___x_3497_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; 
lean_dec(v___x_3556_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3559_;
}
else
{
lean_object* v_bang_3560_; lean_object* v___x_3561_; 
v_bang_3560_ = l_Lean_Syntax_getArg(v___x_3556_, v___x_2531_);
lean_dec(v___x_3556_);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v_bang_3560_);
v_bang_3528_ = v___x_3561_;
v___y_3529_ = v___y_2521_;
v___y_3530_ = v___y_2522_;
v___y_3531_ = v___y_2523_;
v___y_3532_ = v___y_2524_;
v___y_3533_ = v___y_2525_;
v___y_3534_ = v___y_2526_;
v___y_3535_ = v___y_2527_;
v___y_3536_ = v___y_2528_;
goto v___jp_3527_;
}
}
else
{
lean_object* v___x_3562_; 
lean_dec(v___x_3556_);
v___x_3562_ = lean_box(0);
v_bang_3528_ = v___x_3562_;
v___y_3529_ = v___y_2521_;
v___y_3530_ = v___y_2522_;
v___y_3531_ = v___y_2523_;
v___y_3532_ = v___y_2524_;
v___y_3533_ = v___y_2525_;
v___y_3534_ = v___y_2526_;
v___y_3535_ = v___y_2527_;
v___y_3536_ = v___y_2528_;
goto v___jp_3527_;
}
v___jp_2533_:
{
lean_object* v_usedTheorems_2540_; lean_object* v_diag_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2583_; 
v_usedTheorems_2540_ = lean_ctor_get(v___y_2535_, 0);
v_diag_2541_ = lean_ctor_get(v___y_2535_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___y_2535_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2543_ = v___y_2535_;
v_isShared_2544_ = v_isSharedCheck_2583_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_diag_2541_);
lean_inc(v_usedTheorems_2540_);
lean_dec(v___y_2535_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2583_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2534_, v_usedTheorems_2540_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v_usedTheorems_2540_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v_ref_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2545_);
v_ref_2547_ = lean_ctor_get(v___y_2538_, 5);
v___x_2548_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v_a_2546_);
lean_ctor_set(v___x_2543_, 0, v___x_2548_);
v___x_2550_ = v___x_2543_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_a_2546_);
v___x_2550_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_ctor_set(v___x_2552_, 2, v___x_2551_);
lean_ctor_set(v___x_2552_, 3, v___x_2551_);
lean_ctor_set(v___x_2552_, 4, v___x_2551_);
lean_ctor_set(v___x_2552_, 5, v___x_2551_);
lean_inc(v_ref_2547_);
v___x_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_ref_2547_);
v___x_2554_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2555_ = 4;
v___x_2556_ = l_Lean_MessageData_nil;
v___x_2557_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2532_, v___x_2552_, v___x_2553_, v___x_2554_, v___x_2551_, v___x_2555_, v___x_2556_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2565_);
v___x_2559_ = v___x_2557_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2557_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_diag_2541_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_diag_2541_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_diag_2541_);
v_a_2566_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2557_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2557_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_diag_2541_);
lean_dec(v_tk_2532_);
v_a_2575_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2545_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2545_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
v___jp_2584_:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2585_, v___y_2591_, v___y_2587_, v___y_2588_, v___y_2586_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_2596_ = l_Lean_Meta_simpAll(v_a_2594_, v___y_2592_, v___y_2590_, v___x_2595_, v___y_2591_, v___y_2587_, v___y_2588_, v___y_2586_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v_fst_2598_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref(v___x_2596_);
v_fst_2598_ = lean_ctor_get(v_a_2597_, 0);
if (lean_obj_tag(v_fst_2598_) == 0)
{
lean_object* v_snd_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_snd_2599_ = lean_ctor_get(v_a_2597_, 1);
lean_inc(v_snd_2599_);
lean_dec(v_a_2597_);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2600_, v___y_2585_, v___y_2591_, v___y_2587_, v___y_2588_, v___y_2586_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref(v___x_2601_);
v___y_2534_ = v___y_2589_;
v___y_2535_ = v_snd_2599_;
v___y_2536_ = v___y_2591_;
v___y_2537_ = v___y_2587_;
v___y_2538_ = v___y_2588_;
v___y_2539_ = v___y_2586_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_snd_2599_);
lean_dec(v___y_2589_);
lean_dec(v_tk_2532_);
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
else
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2628_; 
lean_inc_ref(v_fst_2598_);
v_snd_2610_ = lean_ctor_get(v_a_2597_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_a_2597_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v_a_2597_, 0);
lean_dec(v_unused_2629_);
v___x_2612_ = v_a_2597_;
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_dec(v_a_2597_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
v_val_2614_ = lean_ctor_get(v_fst_2598_, 0);
lean_inc(v_val_2614_);
lean_dec_ref(v_fst_2598_);
v___x_2615_ = lean_box(0);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 1);
lean_ctor_set(v___x_2612_, 1, v___x_2615_);
lean_ctor_set(v___x_2612_, 0, v_val_2614_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_val_2614_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2617_, v___y_2585_, v___y_2591_, v___y_2587_, v___y_2588_, v___y_2586_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_dec_ref(v___x_2618_);
v___y_2534_ = v___y_2589_;
v___y_2535_ = v_snd_2610_;
v___y_2536_ = v___y_2591_;
v___y_2537_ = v___y_2587_;
v___y_2538_ = v___y_2588_;
v___y_2539_ = v___y_2586_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_snd_2610_);
lean_dec(v___y_2589_);
lean_dec(v_tk_2532_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v___y_2589_);
lean_dec(v_tk_2532_);
v_a_2630_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2596_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2596_);
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
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___y_2592_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v_tk_2532_);
v_a_2638_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2593_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2593_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
v___jp_2646_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2661_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2648_, v___x_2516_, v___y_2649_, v___x_2516_, v___x_2660_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2648_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
if (lean_obj_tag(v___y_2650_) == 0)
{
lean_object* v_ctx_2663_; lean_object* v_simprocs_2664_; 
v_ctx_2663_ = lean_ctor_get(v_a_2662_, 0);
lean_inc_ref(v_ctx_2663_);
v_simprocs_2664_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_simprocs_2664_);
lean_dec(v_a_2662_);
v___y_2585_ = v___y_2653_;
v___y_2586_ = v___y_2659_;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___y_2658_;
v___y_2589_ = v_stxForSuggestion_2651_;
v___y_2590_ = v_simprocs_2664_;
v___y_2591_ = v___y_2656_;
v___y_2592_ = v_ctx_2663_;
goto v___jp_2584_;
}
else
{
lean_dec_ref(v___y_2650_);
if (v___y_2647_ == 0)
{
lean_object* v_ctx_2665_; lean_object* v_simprocs_2666_; 
v_ctx_2665_ = lean_ctor_get(v_a_2662_, 0);
lean_inc_ref(v_ctx_2665_);
v_simprocs_2666_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_simprocs_2666_);
lean_dec(v_a_2662_);
v___y_2585_ = v___y_2653_;
v___y_2586_ = v___y_2659_;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___y_2658_;
v___y_2589_ = v_stxForSuggestion_2651_;
v___y_2590_ = v_simprocs_2666_;
v___y_2591_ = v___y_2656_;
v___y_2592_ = v_ctx_2665_;
goto v___jp_2584_;
}
else
{
lean_object* v_ctx_2667_; lean_object* v_simprocs_2668_; lean_object* v___x_2669_; 
v_ctx_2667_ = lean_ctor_get(v_a_2662_, 0);
lean_inc_ref(v_ctx_2667_);
v_simprocs_2668_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_simprocs_2668_);
lean_dec(v_a_2662_);
v___x_2669_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2667_);
v___y_2585_ = v___y_2653_;
v___y_2586_ = v___y_2659_;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___y_2658_;
v___y_2589_ = v_stxForSuggestion_2651_;
v___y_2590_ = v_simprocs_2668_;
v___y_2591_ = v___y_2656_;
v___y_2592_ = v___x_2669_;
goto v___jp_2584_;
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_stxForSuggestion_2651_);
lean_dec(v___y_2650_);
lean_dec(v_tk_2532_);
v_a_2670_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2661_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_inc_ref_n(v___y_2684_, 2);
v___x_2699_ = l_Array_append___redArg(v___y_2684_, v___y_2698_);
lean_dec_ref(v___y_2698_);
lean_inc_n(v___y_2696_, 2);
lean_inc_n(v___y_2690_, 2);
v___x_2700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___y_2690_);
lean_ctor_set(v___x_2700_, 1, v___y_2696_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2690_);
lean_ctor_set(v___x_2701_, 1, v___y_2696_);
lean_ctor_set(v___x_2701_, 2, v___y_2684_);
v___x_2702_ = l_Lean_Syntax_node5(v___y_2690_, v___y_2681_, v___y_2692_, v___y_2683_, v___y_2679_, v___x_2700_, v___x_2701_);
v___y_2647_ = v___y_2689_;
v___y_2648_ = v___y_2688_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v___y_2695_;
v_stxForSuggestion_2651_ = v___x_2702_;
v___y_2652_ = v___y_2685_;
v___y_2653_ = v___y_2686_;
v___y_2654_ = v___y_2682_;
v___y_2655_ = v___y_2694_;
v___y_2656_ = v___y_2687_;
v___y_2657_ = v___y_2697_;
v___y_2658_ = v___y_2691_;
v___y_2659_ = v___y_2693_;
goto v___jp_2646_;
}
v___jp_2703_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_inc_ref(v___y_2708_);
v___x_2724_ = l_Array_append___redArg(v___y_2708_, v___y_2723_);
lean_dec_ref(v___y_2723_);
lean_inc(v___y_2721_);
lean_inc(v___y_2714_);
v___x_2725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2714_);
lean_ctor_set(v___x_2725_, 1, v___y_2721_);
lean_ctor_set(v___x_2725_, 2, v___x_2724_);
if (lean_obj_tag(v___y_2719_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_val_2726_ = lean_ctor_get(v___y_2719_, 0);
lean_inc(v_val_2726_);
lean_dec_ref(v___y_2719_);
v___x_2727_ = l_Lean_SourceInfo_fromRef(v_val_2726_, v___x_2516_);
lean_dec(v_val_2726_);
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = l_Array_mkArray1___redArg(v___x_2729_);
v___y_2679_ = v___x_2725_;
v___y_2680_ = v___y_2704_;
v___y_2681_ = v___y_2705_;
v___y_2682_ = v___y_2706_;
v___y_2683_ = v___y_2707_;
v___y_2684_ = v___y_2708_;
v___y_2685_ = v___y_2709_;
v___y_2686_ = v___y_2710_;
v___y_2687_ = v___y_2711_;
v___y_2688_ = v___y_2712_;
v___y_2689_ = v___y_2713_;
v___y_2690_ = v___y_2714_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2715_;
v___y_2693_ = v___y_2718_;
v___y_2694_ = v___y_2717_;
v___y_2695_ = v___y_2720_;
v___y_2696_ = v___y_2721_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___x_2730_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v___y_2719_);
v___x_2731_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2679_ = v___x_2725_;
v___y_2680_ = v___y_2704_;
v___y_2681_ = v___y_2705_;
v___y_2682_ = v___y_2706_;
v___y_2683_ = v___y_2707_;
v___y_2684_ = v___y_2708_;
v___y_2685_ = v___y_2709_;
v___y_2686_ = v___y_2710_;
v___y_2687_ = v___y_2711_;
v___y_2688_ = v___y_2712_;
v___y_2689_ = v___y_2713_;
v___y_2690_ = v___y_2714_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2715_;
v___y_2693_ = v___y_2718_;
v___y_2694_ = v___y_2717_;
v___y_2695_ = v___y_2720_;
v___y_2696_ = v___y_2721_;
v___y_2697_ = v___y_2722_;
v___y_2698_ = v___x_2731_;
goto v___jp_2678_;
}
}
v___jp_2732_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_inc_ref_n(v___y_2747_, 2);
v___x_2754_ = l_Array_append___redArg(v___y_2747_, v___y_2753_);
lean_dec_ref(v___y_2753_);
lean_inc_n(v___y_2734_, 3);
lean_inc_n(v___y_2736_, 5);
v___x_2755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___y_2736_);
lean_ctor_set(v___x_2755_, 1, v___y_2734_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2736_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2759_ = l_Lean_Syntax_SepArray_ofElems(v___x_2758_, v___y_2743_);
lean_dec_ref(v___y_2743_);
v___x_2760_ = l_Array_append___redArg(v___y_2747_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___y_2736_);
lean_ctor_set(v___x_2761_, 1, v___y_2734_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2736_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_Syntax_node3(v___y_2736_, v___y_2734_, v___x_2757_, v___x_2761_, v___x_2763_);
v___x_2765_ = l_Lean_Syntax_node5(v___y_2736_, v___y_2745_, v___y_2752_, v___y_2737_, v___y_2744_, v___x_2755_, v___x_2764_);
v___y_2647_ = v___y_2742_;
v___y_2648_ = v___y_2741_;
v___y_2649_ = v___y_2733_;
v___y_2650_ = v___y_2750_;
v_stxForSuggestion_2651_ = v___x_2765_;
v___y_2652_ = v___y_2738_;
v___y_2653_ = v___y_2739_;
v___y_2654_ = v___y_2735_;
v___y_2655_ = v___y_2749_;
v___y_2656_ = v___y_2740_;
v___y_2657_ = v___y_2751_;
v___y_2658_ = v___y_2746_;
v___y_2659_ = v___y_2748_;
goto v___jp_2646_;
}
v___jp_2766_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc_ref(v___y_2780_);
v___x_2788_ = l_Array_append___redArg(v___y_2780_, v___y_2787_);
lean_dec_ref(v___y_2787_);
lean_inc(v___y_2767_);
lean_inc(v___y_2770_);
v___x_2789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2789_, 0, v___y_2770_);
lean_ctor_set(v___x_2789_, 1, v___y_2767_);
lean_ctor_set(v___x_2789_, 2, v___x_2788_);
if (lean_obj_tag(v___y_2783_) == 1)
{
lean_object* v_val_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_val_2790_ = lean_ctor_get(v___y_2783_, 0);
lean_inc(v_val_2790_);
lean_dec_ref(v___y_2783_);
v___x_2791_ = l_Lean_SourceInfo_fromRef(v_val_2790_, v___x_2516_);
lean_dec(v_val_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Array_mkArray1___redArg(v___x_2793_);
v___y_2733_ = v___y_2768_;
v___y_2734_ = v___y_2767_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2771_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___x_2789_;
v___y_2745_ = v___y_2778_;
v___y_2746_ = v___y_2779_;
v___y_2747_ = v___y_2780_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2781_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2786_;
v___y_2752_ = v___y_2785_;
v___y_2753_ = v___x_2794_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2795_; 
lean_dec(v___y_2783_);
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2733_ = v___y_2768_;
v___y_2734_ = v___y_2767_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2771_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2773_;
v___y_2740_ = v___y_2774_;
v___y_2741_ = v___y_2775_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___x_2789_;
v___y_2745_ = v___y_2778_;
v___y_2746_ = v___y_2779_;
v___y_2747_ = v___y_2780_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2781_;
v___y_2750_ = v___y_2784_;
v___y_2751_ = v___y_2786_;
v___y_2752_ = v___y_2785_;
v___y_2753_ = v___x_2795_;
goto v___jp_2732_;
}
}
v___jp_2796_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_inc_ref_n(v___y_2813_, 2);
v___x_2818_ = l_Array_append___redArg(v___y_2813_, v___y_2817_);
lean_dec_ref(v___y_2817_);
lean_inc_n(v___y_2810_, 3);
lean_inc_n(v___y_2804_, 5);
v___x_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___y_2804_);
lean_ctor_set(v___x_2819_, 1, v___y_2810_);
lean_ctor_set(v___x_2819_, 2, v___x_2818_);
v___x_2820_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___y_2804_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2823_ = l_Lean_Syntax_SepArray_ofElems(v___x_2822_, v___y_2808_);
lean_dec_ref(v___y_2808_);
v___x_2824_ = l_Array_append___redArg(v___y_2813_, v___x_2823_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2825_, 0, v___y_2804_);
lean_ctor_set(v___x_2825_, 1, v___y_2810_);
lean_ctor_set(v___x_2825_, 2, v___x_2824_);
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___y_2804_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_Syntax_node3(v___y_2804_, v___y_2810_, v___x_2821_, v___x_2825_, v___x_2827_);
v___x_2829_ = l_Lean_Syntax_node5(v___y_2804_, v___y_2809_, v___y_2801_, v___y_2800_, v___y_2797_, v___x_2819_, v___x_2828_);
v___y_2647_ = v___y_2807_;
v___y_2648_ = v___y_2806_;
v___y_2649_ = v___y_2798_;
v___y_2650_ = v___y_2815_;
v_stxForSuggestion_2651_ = v___x_2829_;
v___y_2652_ = v___y_2802_;
v___y_2653_ = v___y_2803_;
v___y_2654_ = v___y_2799_;
v___y_2655_ = v___y_2814_;
v___y_2656_ = v___y_2805_;
v___y_2657_ = v___y_2816_;
v___y_2658_ = v___y_2811_;
v___y_2659_ = v___y_2812_;
goto v___jp_2646_;
}
v___jp_2830_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_inc_ref(v___y_2847_);
v___x_2852_ = l_Array_append___redArg(v___y_2847_, v___y_2851_);
lean_dec_ref(v___y_2851_);
lean_inc(v___y_2843_);
lean_inc(v___y_2837_);
v___x_2853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2853_, 0, v___y_2837_);
lean_ctor_set(v___x_2853_, 1, v___y_2843_);
lean_ctor_set(v___x_2853_, 2, v___x_2852_);
if (lean_obj_tag(v___y_2848_) == 1)
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_val_2854_ = lean_ctor_get(v___y_2848_, 0);
lean_inc(v_val_2854_);
lean_dec_ref(v___y_2848_);
v___x_2855_ = l_Lean_SourceInfo_fromRef(v_val_2854_, v___x_2516_);
lean_dec(v_val_2854_);
v___x_2856_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Array_mkArray1___redArg(v___x_2857_);
v___y_2797_ = v___x_2853_;
v___y_2798_ = v___y_2831_;
v___y_2799_ = v___y_2832_;
v___y_2800_ = v___y_2833_;
v___y_2801_ = v___y_2834_;
v___y_2802_ = v___y_2835_;
v___y_2803_ = v___y_2836_;
v___y_2804_ = v___y_2837_;
v___y_2805_ = v___y_2838_;
v___y_2806_ = v___y_2839_;
v___y_2807_ = v___y_2840_;
v___y_2808_ = v___y_2841_;
v___y_2809_ = v___y_2842_;
v___y_2810_ = v___y_2843_;
v___y_2811_ = v___y_2844_;
v___y_2812_ = v___y_2846_;
v___y_2813_ = v___y_2847_;
v___y_2814_ = v___y_2845_;
v___y_2815_ = v___y_2849_;
v___y_2816_ = v___y_2850_;
v___y_2817_ = v___x_2858_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v___y_2848_);
v___x_2859_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2797_ = v___x_2853_;
v___y_2798_ = v___y_2831_;
v___y_2799_ = v___y_2832_;
v___y_2800_ = v___y_2833_;
v___y_2801_ = v___y_2834_;
v___y_2802_ = v___y_2835_;
v___y_2803_ = v___y_2836_;
v___y_2804_ = v___y_2837_;
v___y_2805_ = v___y_2838_;
v___y_2806_ = v___y_2839_;
v___y_2807_ = v___y_2840_;
v___y_2808_ = v___y_2841_;
v___y_2809_ = v___y_2842_;
v___y_2810_ = v___y_2843_;
v___y_2811_ = v___y_2844_;
v___y_2812_ = v___y_2846_;
v___y_2813_ = v___y_2847_;
v___y_2814_ = v___y_2845_;
v___y_2815_ = v___y_2849_;
v___y_2816_ = v___y_2850_;
v___y_2817_ = v___x_2859_;
goto v___jp_2796_;
}
}
v___jp_2860_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref_n(v___y_2876_, 2);
v___x_2881_ = l_Array_append___redArg(v___y_2876_, v___y_2880_);
lean_dec_ref(v___y_2880_);
lean_inc_n(v___y_2877_, 2);
lean_inc_n(v___y_2861_, 2);
v___x_2882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2882_, 0, v___y_2861_);
lean_ctor_set(v___x_2882_, 1, v___y_2877_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2883_, 0, v___y_2861_);
lean_ctor_set(v___x_2883_, 1, v___y_2877_);
lean_ctor_set(v___x_2883_, 2, v___y_2876_);
v___x_2884_ = l_Lean_Syntax_node5(v___y_2861_, v___y_2868_, v___y_2874_, v___y_2864_, v___y_2866_, v___x_2882_, v___x_2883_);
v___y_2647_ = v___y_2871_;
v___y_2648_ = v___y_2870_;
v___y_2649_ = v___y_2862_;
v___y_2650_ = v___y_2878_;
v_stxForSuggestion_2651_ = v___x_2884_;
v___y_2652_ = v___y_2865_;
v___y_2653_ = v___y_2867_;
v___y_2654_ = v___y_2863_;
v___y_2655_ = v___y_2875_;
v___y_2656_ = v___y_2869_;
v___y_2657_ = v___y_2879_;
v___y_2658_ = v___y_2872_;
v___y_2659_ = v___y_2873_;
goto v___jp_2646_;
}
v___jp_2885_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_inc_ref(v___y_2900_);
v___x_2906_ = l_Array_append___redArg(v___y_2900_, v___y_2905_);
lean_dec_ref(v___y_2905_);
lean_inc(v___y_2901_);
lean_inc(v___y_2886_);
v___x_2907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2907_, 0, v___y_2886_);
lean_ctor_set(v___x_2907_, 1, v___y_2901_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
if (lean_obj_tag(v___y_2902_) == 1)
{
lean_object* v_val_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_val_2908_ = lean_ctor_get(v___y_2902_, 0);
lean_inc(v_val_2908_);
lean_dec_ref(v___y_2902_);
v___x_2909_ = l_Lean_SourceInfo_fromRef(v_val_2908_, v___x_2516_);
lean_dec(v_val_2908_);
v___x_2910_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Array_mkArray1___redArg(v___x_2911_);
v___y_2861_ = v___y_2886_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___y_2888_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2890_;
v___y_2866_ = v___x_2907_;
v___y_2867_ = v___y_2891_;
v___y_2868_ = v___y_2892_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2894_;
v___y_2871_ = v___y_2895_;
v___y_2872_ = v___y_2896_;
v___y_2873_ = v___y_2899_;
v___y_2874_ = v___y_2898_;
v___y_2875_ = v___y_2897_;
v___y_2876_ = v___y_2900_;
v___y_2877_ = v___y_2901_;
v___y_2878_ = v___y_2903_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___x_2912_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v___y_2902_);
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2861_ = v___y_2886_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___y_2888_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2890_;
v___y_2866_ = v___x_2907_;
v___y_2867_ = v___y_2891_;
v___y_2868_ = v___y_2892_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2894_;
v___y_2871_ = v___y_2895_;
v___y_2872_ = v___y_2896_;
v___y_2873_ = v___y_2899_;
v___y_2874_ = v___y_2898_;
v___y_2875_ = v___y_2897_;
v___y_2876_ = v___y_2900_;
v___y_2877_ = v___y_2901_;
v___y_2878_ = v___y_2903_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___x_2913_;
goto v___jp_2860_;
}
}
v___jp_2914_:
{
lean_object* v_ref_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_ref_2931_ = lean_ctor_get(v___y_2924_, 5);
v___x_2932_ = l_Lean_SourceInfo_fromRef(v_ref_2931_, v___y_2930_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2934_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2933_);
v___x_2935_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_2936_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2939_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2920_) == 1)
{
lean_object* v_val_2940_; lean_object* v___x_2941_; 
v_val_2940_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_val_2940_);
lean_dec_ref(v___y_2920_);
v___x_2941_ = l_Array_mkArray1___redArg(v_val_2940_);
v___y_2704_ = v___y_2915_;
v___y_2705_ = v___x_2934_;
v___y_2706_ = v___y_2916_;
v___y_2707_ = v___y_2917_;
v___y_2708_ = v___x_2939_;
v___y_2709_ = v___y_2918_;
v___y_2710_ = v___y_2919_;
v___y_2711_ = v___y_2921_;
v___y_2712_ = v___y_2922_;
v___y_2713_ = v___y_2923_;
v___y_2714_ = v___x_2932_;
v___y_2715_ = v___x_2937_;
v___y_2716_ = v___y_2924_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___y_2928_;
v___y_2720_ = v___y_2927_;
v___y_2721_ = v___x_2938_;
v___y_2722_ = v___y_2929_;
v___y_2723_ = v___x_2941_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2942_; 
lean_dec(v___y_2920_);
v___x_2942_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2704_ = v___y_2915_;
v___y_2705_ = v___x_2934_;
v___y_2706_ = v___y_2916_;
v___y_2707_ = v___y_2917_;
v___y_2708_ = v___x_2939_;
v___y_2709_ = v___y_2918_;
v___y_2710_ = v___y_2919_;
v___y_2711_ = v___y_2921_;
v___y_2712_ = v___y_2922_;
v___y_2713_ = v___y_2923_;
v___y_2714_ = v___x_2932_;
v___y_2715_ = v___x_2937_;
v___y_2716_ = v___y_2924_;
v___y_2717_ = v___y_2925_;
v___y_2718_ = v___y_2926_;
v___y_2719_ = v___y_2928_;
v___y_2720_ = v___y_2927_;
v___y_2721_ = v___x_2938_;
v___y_2722_ = v___y_2929_;
v___y_2723_ = v___x_2942_;
goto v___jp_2703_;
}
}
v___jp_2943_:
{
if (v___y_2961_ == 0)
{
lean_object* v_ref_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_ref_2962_ = lean_ctor_get(v___y_2955_, 5);
v___x_2963_ = l_Lean_SourceInfo_fromRef(v_ref_2962_, v___y_2961_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2965_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2964_);
v___x_2966_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2970_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2950_) == 1)
{
lean_object* v_val_2971_; lean_object* v___x_2972_; 
v_val_2971_ = lean_ctor_get(v___y_2950_, 0);
lean_inc(v_val_2971_);
lean_dec_ref(v___y_2950_);
v___x_2972_ = l_Array_mkArray1___redArg(v_val_2971_);
v___y_2767_ = v___x_2969_;
v___y_2768_ = v___y_2944_;
v___y_2769_ = v___y_2945_;
v___y_2770_ = v___x_2963_;
v___y_2771_ = v___y_2946_;
v___y_2772_ = v___y_2947_;
v___y_2773_ = v___y_2948_;
v___y_2774_ = v___y_2951_;
v___y_2775_ = v___y_2952_;
v___y_2776_ = v___y_2953_;
v___y_2777_ = v___y_2954_;
v___y_2778_ = v___x_2965_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___x_2970_;
v___y_2781_ = v___y_2956_;
v___y_2782_ = v___y_2957_;
v___y_2783_ = v___y_2959_;
v___y_2784_ = v___y_2958_;
v___y_2785_ = v___x_2968_;
v___y_2786_ = v___y_2960_;
v___y_2787_ = v___x_2972_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2973_; 
lean_dec(v___y_2950_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2767_ = v___x_2969_;
v___y_2768_ = v___y_2944_;
v___y_2769_ = v___y_2945_;
v___y_2770_ = v___x_2963_;
v___y_2771_ = v___y_2946_;
v___y_2772_ = v___y_2947_;
v___y_2773_ = v___y_2948_;
v___y_2774_ = v___y_2951_;
v___y_2775_ = v___y_2952_;
v___y_2776_ = v___y_2953_;
v___y_2777_ = v___y_2954_;
v___y_2778_ = v___x_2965_;
v___y_2779_ = v___y_2955_;
v___y_2780_ = v___x_2970_;
v___y_2781_ = v___y_2956_;
v___y_2782_ = v___y_2957_;
v___y_2783_ = v___y_2959_;
v___y_2784_ = v___y_2958_;
v___y_2785_ = v___x_2968_;
v___y_2786_ = v___y_2960_;
v___y_2787_ = v___x_2973_;
goto v___jp_2766_;
}
}
else
{
lean_object* v_ref_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_ref_2974_ = lean_ctor_get(v___y_2955_, 5);
v___x_2975_ = l_Lean_SourceInfo_fromRef(v_ref_2974_, v___y_2949_);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2977_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2976_);
v___x_2978_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_2980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2982_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2950_) == 1)
{
lean_object* v_val_2983_; lean_object* v___x_2984_; 
v_val_2983_ = lean_ctor_get(v___y_2950_, 0);
lean_inc(v_val_2983_);
lean_dec_ref(v___y_2950_);
v___x_2984_ = l_Array_mkArray1___redArg(v_val_2983_);
v___y_2831_ = v___y_2944_;
v___y_2832_ = v___y_2945_;
v___y_2833_ = v___y_2946_;
v___y_2834_ = v___x_2980_;
v___y_2835_ = v___y_2947_;
v___y_2836_ = v___y_2948_;
v___y_2837_ = v___x_2975_;
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___y_2953_;
v___y_2841_ = v___y_2954_;
v___y_2842_ = v___x_2977_;
v___y_2843_ = v___x_2981_;
v___y_2844_ = v___y_2955_;
v___y_2845_ = v___y_2956_;
v___y_2846_ = v___y_2957_;
v___y_2847_ = v___x_2982_;
v___y_2848_ = v___y_2959_;
v___y_2849_ = v___y_2958_;
v___y_2850_ = v___y_2960_;
v___y_2851_ = v___x_2984_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2985_; 
lean_dec(v___y_2950_);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2831_ = v___y_2944_;
v___y_2832_ = v___y_2945_;
v___y_2833_ = v___y_2946_;
v___y_2834_ = v___x_2980_;
v___y_2835_ = v___y_2947_;
v___y_2836_ = v___y_2948_;
v___y_2837_ = v___x_2975_;
v___y_2838_ = v___y_2951_;
v___y_2839_ = v___y_2952_;
v___y_2840_ = v___y_2953_;
v___y_2841_ = v___y_2954_;
v___y_2842_ = v___x_2977_;
v___y_2843_ = v___x_2981_;
v___y_2844_ = v___y_2955_;
v___y_2845_ = v___y_2956_;
v___y_2846_ = v___y_2957_;
v___y_2847_ = v___x_2982_;
v___y_2848_ = v___y_2959_;
v___y_2849_ = v___y_2958_;
v___y_2850_ = v___y_2960_;
v___y_2851_ = v___x_2985_;
goto v___jp_2830_;
}
}
}
v___jp_2986_:
{
lean_object* v___x_3003_; lean_object* v_a_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3003_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2990_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = lean_array_get_size(v___y_2988_);
v___x_3006_ = lean_nat_dec_eq(v___x_3005_, v___x_2531_);
if (v___x_3006_ == 0)
{
if (lean_obj_tag(v___y_2993_) == 0)
{
v___y_2944_ = v___y_2989_;
v___y_2945_ = v___y_2997_;
v___y_2946_ = v_a_3004_;
v___y_2947_ = v___y_2995_;
v___y_2948_ = v___y_2996_;
v___y_2949_ = v___x_3006_;
v___y_2950_ = v___y_2991_;
v___y_2951_ = v___y_2999_;
v___y_2952_ = v_stxForExecution_2994_;
v___y_2953_ = v___y_2987_;
v___y_2954_ = v___y_2988_;
v___y_2955_ = v___y_3001_;
v___y_2956_ = v___y_2998_;
v___y_2957_ = v___y_3002_;
v___y_2958_ = v___y_2993_;
v___y_2959_ = v___y_2992_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___x_3006_;
goto v___jp_2943_;
}
else
{
v___y_2944_ = v___y_2989_;
v___y_2945_ = v___y_2997_;
v___y_2946_ = v_a_3004_;
v___y_2947_ = v___y_2995_;
v___y_2948_ = v___y_2996_;
v___y_2949_ = v___x_3006_;
v___y_2950_ = v___y_2991_;
v___y_2951_ = v___y_2999_;
v___y_2952_ = v_stxForExecution_2994_;
v___y_2953_ = v___y_2987_;
v___y_2954_ = v___y_2988_;
v___y_2955_ = v___y_3001_;
v___y_2956_ = v___y_2998_;
v___y_2957_ = v___y_3002_;
v___y_2958_ = v___y_2993_;
v___y_2959_ = v___y_2992_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___y_2987_;
goto v___jp_2943_;
}
}
else
{
lean_dec_ref(v___y_2988_);
if (lean_obj_tag(v___y_2993_) == 0)
{
uint8_t v___x_3007_; 
v___x_3007_ = 0;
v___y_2915_ = v___y_2989_;
v___y_2916_ = v___y_2997_;
v___y_2917_ = v_a_3004_;
v___y_2918_ = v___y_2995_;
v___y_2919_ = v___y_2996_;
v___y_2920_ = v___y_2991_;
v___y_2921_ = v___y_2999_;
v___y_2922_ = v_stxForExecution_2994_;
v___y_2923_ = v___y_2987_;
v___y_2924_ = v___y_3001_;
v___y_2925_ = v___y_2998_;
v___y_2926_ = v___y_3002_;
v___y_2927_ = v___y_2993_;
v___y_2928_ = v___y_2992_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___x_3007_;
goto v___jp_2914_;
}
else
{
if (v___y_2987_ == 0)
{
v___y_2915_ = v___y_2989_;
v___y_2916_ = v___y_2997_;
v___y_2917_ = v_a_3004_;
v___y_2918_ = v___y_2995_;
v___y_2919_ = v___y_2996_;
v___y_2920_ = v___y_2991_;
v___y_2921_ = v___y_2999_;
v___y_2922_ = v_stxForExecution_2994_;
v___y_2923_ = v___y_2987_;
v___y_2924_ = v___y_3001_;
v___y_2925_ = v___y_2998_;
v___y_2926_ = v___y_3002_;
v___y_2927_ = v___y_2993_;
v___y_2928_ = v___y_2992_;
v___y_2929_ = v___y_3000_;
v___y_2930_ = v___y_2987_;
goto v___jp_2914_;
}
else
{
lean_object* v_ref_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_ref_3008_ = lean_ctor_get(v___y_3001_, 5);
v___x_3009_ = 0;
v___x_3010_ = l_Lean_SourceInfo_fromRef(v_ref_3008_, v___x_3009_);
v___x_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3012_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3011_);
v___x_3013_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3017_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2991_) == 1)
{
lean_object* v_val_3018_; lean_object* v___x_3019_; 
v_val_3018_ = lean_ctor_get(v___y_2991_, 0);
lean_inc(v_val_3018_);
lean_dec_ref(v___y_2991_);
v___x_3019_ = l_Array_mkArray1___redArg(v_val_3018_);
v___y_2886_ = v___x_3010_;
v___y_2887_ = v___y_2989_;
v___y_2888_ = v___y_2997_;
v___y_2889_ = v_a_3004_;
v___y_2890_ = v___y_2995_;
v___y_2891_ = v___y_2996_;
v___y_2892_ = v___x_3012_;
v___y_2893_ = v___y_2999_;
v___y_2894_ = v_stxForExecution_2994_;
v___y_2895_ = v___y_2987_;
v___y_2896_ = v___y_3001_;
v___y_2897_ = v___y_2998_;
v___y_2898_ = v___x_3015_;
v___y_2899_ = v___y_3002_;
v___y_2900_ = v___x_3017_;
v___y_2901_ = v___x_3016_;
v___y_2902_ = v___y_2992_;
v___y_2903_ = v___y_2993_;
v___y_2904_ = v___y_3000_;
v___y_2905_ = v___x_3019_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_3020_; 
lean_dec(v___y_2991_);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2886_ = v___x_3010_;
v___y_2887_ = v___y_2989_;
v___y_2888_ = v___y_2997_;
v___y_2889_ = v_a_3004_;
v___y_2890_ = v___y_2995_;
v___y_2891_ = v___y_2996_;
v___y_2892_ = v___x_3012_;
v___y_2893_ = v___y_2999_;
v___y_2894_ = v_stxForExecution_2994_;
v___y_2895_ = v___y_2987_;
v___y_2896_ = v___y_3001_;
v___y_2897_ = v___y_2998_;
v___y_2898_ = v___x_3015_;
v___y_2899_ = v___y_3002_;
v___y_2900_ = v___x_3017_;
v___y_2901_ = v___x_3016_;
v___y_2902_ = v___y_2992_;
v___y_2903_ = v___y_2993_;
v___y_2904_ = v___y_3000_;
v___y_2905_ = v___x_3020_;
goto v___jp_2885_;
}
}
}
}
}
v___jp_3021_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_inc_ref_n(v___y_3031_, 2);
v___x_3044_ = l_Array_append___redArg(v___y_3031_, v___y_3043_);
lean_dec_ref(v___y_3043_);
lean_inc_n(v___y_3039_, 2);
lean_inc_n(v___y_3041_, 2);
v___x_3045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___y_3041_);
lean_ctor_set(v___x_3045_, 1, v___y_3039_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3041_);
lean_ctor_set(v___x_3046_, 1, v___y_3039_);
lean_ctor_set(v___x_3046_, 2, v___y_3031_);
lean_inc(v___y_3027_);
v___x_3047_ = l_Lean_Syntax_node5(v___y_3041_, v___y_3023_, v___y_3026_, v___y_3027_, v___y_3028_, v___x_3045_, v___x_3046_);
v___y_2987_ = v___y_3032_;
v___y_2988_ = v___y_3033_;
v___y_2989_ = v___y_3025_;
v___y_2990_ = v___y_3027_;
v___y_2991_ = v___y_3030_;
v___y_2992_ = v___y_3038_;
v___y_2993_ = v___y_3037_;
v_stxForExecution_2994_ = v___x_3047_;
v___y_2995_ = v___y_3042_;
v___y_2996_ = v___y_3036_;
v___y_2997_ = v___y_3024_;
v___y_2998_ = v___y_3040_;
v___y_2999_ = v___y_3029_;
v___y_3000_ = v___y_3034_;
v___y_3001_ = v___y_3022_;
v___y_3002_ = v___y_3035_;
goto v___jp_2986_;
}
v___jp_3048_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_inc_ref(v___y_3057_);
v___x_3070_ = l_Array_append___redArg(v___y_3057_, v___y_3069_);
lean_dec_ref(v___y_3069_);
lean_inc(v___y_3066_);
lean_inc(v___y_3068_);
v___x_3071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3068_);
lean_ctor_set(v___x_3071_, 1, v___y_3066_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
if (lean_obj_tag(v___y_3064_) == 1)
{
lean_object* v_val_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v_val_3072_ = lean_ctor_get(v___y_3064_, 0);
v___x_3073_ = l_Lean_SourceInfo_fromRef(v_val_3072_, v___x_2516_);
v___x_3074_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Array_mkArray1___redArg(v___x_3075_);
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___y_3050_;
v___y_3024_ = v___y_3051_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___y_3054_;
v___y_3028_ = v___x_3071_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3059_;
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3065_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3066_;
v___y_3040_ = v___y_3063_;
v___y_3041_ = v___y_3068_;
v___y_3042_ = v___y_3067_;
v___y_3043_ = v___x_3076_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3022_ = v___y_3049_;
v___y_3023_ = v___y_3050_;
v___y_3024_ = v___y_3051_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___y_3054_;
v___y_3028_ = v___x_3071_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3059_;
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3065_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3066_;
v___y_3040_ = v___y_3063_;
v___y_3041_ = v___y_3068_;
v___y_3042_ = v___y_3067_;
v___y_3043_ = v___x_3077_;
goto v___jp_3021_;
}
}
v___jp_3078_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_inc_ref_n(v___y_3083_, 2);
v___x_3101_ = l_Array_append___redArg(v___y_3083_, v___y_3100_);
lean_dec_ref(v___y_3100_);
lean_inc_n(v___y_3092_, 3);
lean_inc_n(v___y_3094_, 5);
v___x_3102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3102_, 0, v___y_3094_);
lean_ctor_set(v___x_3102_, 1, v___y_3092_);
lean_ctor_set(v___x_3102_, 2, v___x_3101_);
v___x_3103_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3094_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3106_ = l_Lean_Syntax_SepArray_ofElems(v___x_3105_, v___y_3090_);
v___x_3107_ = l_Array_append___redArg(v___y_3083_, v___x_3106_);
lean_dec_ref(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___y_3094_);
lean_ctor_set(v___x_3108_, 1, v___y_3092_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
v___x_3109_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3094_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Lean_Syntax_node3(v___y_3094_, v___y_3092_, v___x_3104_, v___x_3108_, v___x_3110_);
lean_inc(v___y_3082_);
v___x_3112_ = l_Lean_Syntax_node5(v___y_3094_, v___y_3095_, v___y_3084_, v___y_3082_, v___y_3088_, v___x_3102_, v___x_3111_);
v___y_2987_ = v___y_3087_;
v___y_2988_ = v___y_3090_;
v___y_2989_ = v___y_3081_;
v___y_2990_ = v___y_3082_;
v___y_2991_ = v___y_3086_;
v___y_2992_ = v___y_3097_;
v___y_2993_ = v___y_3096_;
v_stxForExecution_2994_ = v___x_3112_;
v___y_2995_ = v___y_3099_;
v___y_2996_ = v___y_3093_;
v___y_2997_ = v___y_3080_;
v___y_2998_ = v___y_3098_;
v___y_2999_ = v___y_3085_;
v___y_3000_ = v___y_3089_;
v___y_3001_ = v___y_3079_;
v___y_3002_ = v___y_3091_;
goto v___jp_2986_;
}
v___jp_3113_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_inc_ref(v___y_3118_);
v___x_3135_ = l_Array_append___redArg(v___y_3118_, v___y_3134_);
lean_dec_ref(v___y_3134_);
lean_inc(v___y_3127_);
lean_inc(v___y_3129_);
v___x_3136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3136_, 0, v___y_3129_);
lean_ctor_set(v___x_3136_, 1, v___y_3127_);
lean_ctor_set(v___x_3136_, 2, v___x_3135_);
if (lean_obj_tag(v___y_3131_) == 1)
{
lean_object* v_val_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_val_3137_ = lean_ctor_get(v___y_3131_, 0);
v___x_3138_ = l_Lean_SourceInfo_fromRef(v_val_3137_, v___x_2516_);
v___x_3139_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Array_mkArray1___redArg(v___x_3140_);
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___x_3136_;
v___y_3089_ = v___y_3124_;
v___y_3090_ = v___y_3123_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3127_;
v___y_3093_ = v___y_3126_;
v___y_3094_ = v___y_3129_;
v___y_3095_ = v___y_3128_;
v___y_3096_ = v___y_3132_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3130_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___x_3141_;
goto v___jp_3078_;
}
else
{
lean_object* v___x_3142_; 
v___x_3142_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3079_ = v___y_3114_;
v___y_3080_ = v___y_3115_;
v___y_3081_ = v___y_3116_;
v___y_3082_ = v___y_3117_;
v___y_3083_ = v___y_3118_;
v___y_3084_ = v___y_3119_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___y_3121_;
v___y_3087_ = v___y_3122_;
v___y_3088_ = v___x_3136_;
v___y_3089_ = v___y_3124_;
v___y_3090_ = v___y_3123_;
v___y_3091_ = v___y_3125_;
v___y_3092_ = v___y_3127_;
v___y_3093_ = v___y_3126_;
v___y_3094_ = v___y_3129_;
v___y_3095_ = v___y_3128_;
v___y_3096_ = v___y_3132_;
v___y_3097_ = v___y_3131_;
v___y_3098_ = v___y_3130_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___x_3142_;
goto v___jp_3078_;
}
}
v___jp_3143_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_inc_ref_n(v___y_3147_, 2);
v___x_3166_ = l_Array_append___redArg(v___y_3147_, v___y_3165_);
lean_dec_ref(v___y_3165_);
lean_inc_n(v___y_3160_, 3);
lean_inc_n(v___y_3151_, 5);
v___x_3167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3151_);
lean_ctor_set(v___x_3167_, 1, v___y_3160_);
lean_ctor_set(v___x_3167_, 2, v___x_3166_);
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___y_3151_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3171_ = l_Lean_Syntax_SepArray_ofElems(v___x_3170_, v___y_3155_);
v___x_3172_ = l_Array_append___redArg(v___y_3147_, v___x_3171_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___y_3151_);
lean_ctor_set(v___x_3173_, 1, v___y_3160_);
lean_ctor_set(v___x_3173_, 2, v___x_3172_);
v___x_3174_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___y_3151_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_Syntax_node3(v___y_3151_, v___y_3160_, v___x_3169_, v___x_3173_, v___x_3175_);
lean_inc(v___y_3149_);
v___x_3177_ = l_Lean_Syntax_node5(v___y_3151_, v___y_3146_, v___y_3159_, v___y_3149_, v___y_3157_, v___x_3167_, v___x_3176_);
v___y_2987_ = v___y_3153_;
v___y_2988_ = v___y_3155_;
v___y_2989_ = v___y_3148_;
v___y_2990_ = v___y_3149_;
v___y_2991_ = v___y_3152_;
v___y_2992_ = v___y_3162_;
v___y_2993_ = v___y_3161_;
v_stxForExecution_2994_ = v___x_3177_;
v___y_2995_ = v___y_3164_;
v___y_2996_ = v___y_3158_;
v___y_2997_ = v___y_3145_;
v___y_2998_ = v___y_3163_;
v___y_2999_ = v___y_3150_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3144_;
v___y_3002_ = v___y_3156_;
goto v___jp_2986_;
}
v___jp_3178_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_inc_ref(v___y_3182_);
v___x_3200_ = l_Array_append___redArg(v___y_3182_, v___y_3199_);
lean_dec_ref(v___y_3199_);
lean_inc(v___y_3194_);
lean_inc(v___y_3186_);
v___x_3201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3186_);
lean_ctor_set(v___x_3201_, 1, v___y_3194_);
lean_ctor_set(v___x_3201_, 2, v___x_3200_);
if (lean_obj_tag(v___y_3196_) == 1)
{
lean_object* v_val_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_val_3202_ = lean_ctor_get(v___y_3196_, 0);
v___x_3203_ = l_Lean_SourceInfo_fromRef(v_val_3202_, v___x_2516_);
v___x_3204_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = l_Array_mkArray1___redArg(v___x_3205_);
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3182_;
v___y_3148_ = v___y_3183_;
v___y_3149_ = v___y_3184_;
v___y_3150_ = v___y_3185_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3190_;
v___y_3155_ = v___y_3189_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___x_3201_;
v___y_3158_ = v___y_3192_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3194_;
v___y_3161_ = v___y_3197_;
v___y_3162_ = v___y_3196_;
v___y_3163_ = v___y_3195_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___x_3206_;
goto v___jp_3143_;
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3182_;
v___y_3148_ = v___y_3183_;
v___y_3149_ = v___y_3184_;
v___y_3150_ = v___y_3185_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3187_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3190_;
v___y_3155_ = v___y_3189_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___x_3201_;
v___y_3158_ = v___y_3192_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3194_;
v___y_3161_ = v___y_3197_;
v___y_3162_ = v___y_3196_;
v___y_3163_ = v___y_3195_;
v___y_3164_ = v___y_3198_;
v___y_3165_ = v___x_3207_;
goto v___jp_3143_;
}
}
v___jp_3208_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_inc_ref_n(v___y_3224_, 2);
v___x_3231_ = l_Array_append___redArg(v___y_3224_, v___y_3230_);
lean_dec_ref(v___y_3230_);
lean_inc_n(v___y_3225_, 2);
lean_inc_n(v___y_3212_, 2);
v___x_3232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3232_, 0, v___y_3212_);
lean_ctor_set(v___x_3232_, 1, v___y_3225_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3233_, 0, v___y_3212_);
lean_ctor_set(v___x_3233_, 1, v___y_3225_);
lean_ctor_set(v___x_3233_, 2, v___y_3224_);
lean_inc(v___y_3213_);
v___x_3234_ = l_Lean_Syntax_node5(v___y_3212_, v___y_3220_, v___y_3216_, v___y_3213_, v___y_3217_, v___x_3232_, v___x_3233_);
v___y_2987_ = v___y_3218_;
v___y_2988_ = v___y_3219_;
v___y_2989_ = v___y_3211_;
v___y_2990_ = v___y_3213_;
v___y_2991_ = v___y_3215_;
v___y_2992_ = v___y_3227_;
v___y_2993_ = v___y_3226_;
v_stxForExecution_2994_ = v___x_3234_;
v___y_2995_ = v___y_3229_;
v___y_2996_ = v___y_3223_;
v___y_2997_ = v___y_3210_;
v___y_2998_ = v___y_3228_;
v___y_2999_ = v___y_3214_;
v___y_3000_ = v___y_3221_;
v___y_3001_ = v___y_3209_;
v___y_3002_ = v___y_3222_;
goto v___jp_2986_;
}
v___jp_3235_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_inc_ref(v___y_3250_);
v___x_3257_ = l_Array_append___redArg(v___y_3250_, v___y_3256_);
lean_dec_ref(v___y_3256_);
lean_inc(v___y_3251_);
lean_inc(v___y_3239_);
v___x_3258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3258_, 0, v___y_3239_);
lean_ctor_set(v___x_3258_, 1, v___y_3251_);
lean_ctor_set(v___x_3258_, 2, v___x_3257_);
if (lean_obj_tag(v___y_3253_) == 1)
{
lean_object* v_val_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_val_3259_ = lean_ctor_get(v___y_3253_, 0);
v___x_3260_ = l_Lean_SourceInfo_fromRef(v_val_3259_, v___x_2516_);
v___x_3261_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l_Array_mkArray1___redArg(v___x_3262_);
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___x_3258_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3245_;
v___y_3222_ = v___y_3248_;
v___y_3223_ = v___y_3249_;
v___y_3224_ = v___y_3250_;
v___y_3225_ = v___y_3251_;
v___y_3226_ = v___y_3254_;
v___y_3227_ = v___y_3253_;
v___y_3228_ = v___y_3252_;
v___y_3229_ = v___y_3255_;
v___y_3230_ = v___x_3263_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3264_; 
v___x_3264_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___x_3258_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3245_;
v___y_3222_ = v___y_3248_;
v___y_3223_ = v___y_3249_;
v___y_3224_ = v___y_3250_;
v___y_3225_ = v___y_3251_;
v___y_3226_ = v___y_3254_;
v___y_3227_ = v___y_3253_;
v___y_3228_ = v___y_3252_;
v___y_3229_ = v___y_3255_;
v___y_3230_ = v___x_3264_;
goto v___jp_3208_;
}
}
v___jp_3265_:
{
lean_object* v_ref_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_ref_3282_ = lean_ctor_get(v___y_3266_, 5);
v___x_3283_ = l_Lean_SourceInfo_fromRef(v_ref_3282_, v___y_3281_);
v___x_3284_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3285_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3284_);
v___x_3286_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3287_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3290_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3271_) == 1)
{
lean_object* v_val_3291_; lean_object* v___x_3292_; 
v_val_3291_ = lean_ctor_get(v___y_3271_, 0);
lean_inc(v_val_3291_);
v___x_3292_ = l_Array_mkArray1___redArg(v_val_3291_);
v___y_3049_ = v___y_3266_;
v___y_3050_ = v___x_3285_;
v___y_3051_ = v___y_3267_;
v___y_3052_ = v___y_3268_;
v___y_3053_ = v___x_3288_;
v___y_3054_ = v___y_3269_;
v___y_3055_ = v___y_3270_;
v___y_3056_ = v___y_3271_;
v___y_3057_ = v___x_3290_;
v___y_3058_ = v___y_3272_;
v___y_3059_ = v___y_3273_;
v___y_3060_ = v___y_3274_;
v___y_3061_ = v___y_3275_;
v___y_3062_ = v___y_3276_;
v___y_3063_ = v___y_3279_;
v___y_3064_ = v___y_3278_;
v___y_3065_ = v___y_3277_;
v___y_3066_ = v___x_3289_;
v___y_3067_ = v___y_3280_;
v___y_3068_ = v___x_3283_;
v___y_3069_ = v___x_3292_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3293_; 
v___x_3293_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3049_ = v___y_3266_;
v___y_3050_ = v___x_3285_;
v___y_3051_ = v___y_3267_;
v___y_3052_ = v___y_3268_;
v___y_3053_ = v___x_3288_;
v___y_3054_ = v___y_3269_;
v___y_3055_ = v___y_3270_;
v___y_3056_ = v___y_3271_;
v___y_3057_ = v___x_3290_;
v___y_3058_ = v___y_3272_;
v___y_3059_ = v___y_3273_;
v___y_3060_ = v___y_3274_;
v___y_3061_ = v___y_3275_;
v___y_3062_ = v___y_3276_;
v___y_3063_ = v___y_3279_;
v___y_3064_ = v___y_3278_;
v___y_3065_ = v___y_3277_;
v___y_3066_ = v___x_3289_;
v___y_3067_ = v___y_3280_;
v___y_3068_ = v___x_3283_;
v___y_3069_ = v___x_3293_;
goto v___jp_3048_;
}
}
v___jp_3294_:
{
if (v___y_3311_ == 0)
{
lean_object* v_ref_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_ref_3312_ = lean_ctor_get(v___y_3295_, 5);
v___x_3313_ = l_Lean_SourceInfo_fromRef(v_ref_3312_, v___y_3311_);
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3315_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3314_);
v___x_3316_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_3318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3320_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3300_) == 1)
{
lean_object* v_val_3321_; lean_object* v___x_3322_; 
v_val_3321_ = lean_ctor_get(v___y_3300_, 0);
lean_inc(v_val_3321_);
v___x_3322_ = l_Array_mkArray1___redArg(v_val_3321_);
v___y_3114_ = v___y_3295_;
v___y_3115_ = v___y_3296_;
v___y_3116_ = v___y_3297_;
v___y_3117_ = v___y_3298_;
v___y_3118_ = v___x_3320_;
v___y_3119_ = v___x_3318_;
v___y_3120_ = v___y_3299_;
v___y_3121_ = v___y_3300_;
v___y_3122_ = v___y_3302_;
v___y_3123_ = v___y_3303_;
v___y_3124_ = v___y_3304_;
v___y_3125_ = v___y_3305_;
v___y_3126_ = v___y_3306_;
v___y_3127_ = v___x_3319_;
v___y_3128_ = v___x_3315_;
v___y_3129_ = v___x_3313_;
v___y_3130_ = v___y_3309_;
v___y_3131_ = v___y_3308_;
v___y_3132_ = v___y_3307_;
v___y_3133_ = v___y_3310_;
v___y_3134_ = v___x_3322_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3114_ = v___y_3295_;
v___y_3115_ = v___y_3296_;
v___y_3116_ = v___y_3297_;
v___y_3117_ = v___y_3298_;
v___y_3118_ = v___x_3320_;
v___y_3119_ = v___x_3318_;
v___y_3120_ = v___y_3299_;
v___y_3121_ = v___y_3300_;
v___y_3122_ = v___y_3302_;
v___y_3123_ = v___y_3303_;
v___y_3124_ = v___y_3304_;
v___y_3125_ = v___y_3305_;
v___y_3126_ = v___y_3306_;
v___y_3127_ = v___x_3319_;
v___y_3128_ = v___x_3315_;
v___y_3129_ = v___x_3313_;
v___y_3130_ = v___y_3309_;
v___y_3131_ = v___y_3308_;
v___y_3132_ = v___y_3307_;
v___y_3133_ = v___y_3310_;
v___y_3134_ = v___x_3323_;
goto v___jp_3113_;
}
}
else
{
lean_object* v_ref_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_ref_3324_ = lean_ctor_get(v___y_3295_, 5);
v___x_3325_ = l_Lean_SourceInfo_fromRef(v_ref_3324_, v___y_3301_);
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3327_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3326_);
v___x_3328_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3332_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3300_) == 1)
{
lean_object* v_val_3333_; lean_object* v___x_3334_; 
v_val_3333_ = lean_ctor_get(v___y_3300_, 0);
lean_inc(v_val_3333_);
v___x_3334_ = l_Array_mkArray1___redArg(v_val_3333_);
v___y_3179_ = v___y_3295_;
v___y_3180_ = v___y_3296_;
v___y_3181_ = v___x_3327_;
v___y_3182_ = v___x_3332_;
v___y_3183_ = v___y_3297_;
v___y_3184_ = v___y_3298_;
v___y_3185_ = v___y_3299_;
v___y_3186_ = v___x_3325_;
v___y_3187_ = v___y_3300_;
v___y_3188_ = v___y_3302_;
v___y_3189_ = v___y_3303_;
v___y_3190_ = v___y_3304_;
v___y_3191_ = v___y_3305_;
v___y_3192_ = v___y_3306_;
v___y_3193_ = v___x_3330_;
v___y_3194_ = v___x_3331_;
v___y_3195_ = v___y_3309_;
v___y_3196_ = v___y_3308_;
v___y_3197_ = v___y_3307_;
v___y_3198_ = v___y_3310_;
v___y_3199_ = v___x_3334_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3179_ = v___y_3295_;
v___y_3180_ = v___y_3296_;
v___y_3181_ = v___x_3327_;
v___y_3182_ = v___x_3332_;
v___y_3183_ = v___y_3297_;
v___y_3184_ = v___y_3298_;
v___y_3185_ = v___y_3299_;
v___y_3186_ = v___x_3325_;
v___y_3187_ = v___y_3300_;
v___y_3188_ = v___y_3302_;
v___y_3189_ = v___y_3303_;
v___y_3190_ = v___y_3304_;
v___y_3191_ = v___y_3305_;
v___y_3192_ = v___y_3306_;
v___y_3193_ = v___x_3330_;
v___y_3194_ = v___x_3331_;
v___y_3195_ = v___y_3309_;
v___y_3196_ = v___y_3308_;
v___y_3197_ = v___y_3307_;
v___y_3198_ = v___y_3310_;
v___y_3199_ = v___x_3335_;
goto v___jp_3178_;
}
}
}
v___jp_3336_:
{
lean_object* v___x_3352_; uint8_t v___x_3353_; 
v___x_3352_ = lean_array_get_size(v_argsArray_3343_);
v___x_3353_ = lean_nat_dec_eq(v___x_3352_, v___x_2531_);
if (v___x_3353_ == 0)
{
if (lean_obj_tag(v___y_3341_) == 0)
{
v___y_3295_ = v___y_3350_;
v___y_3296_ = v___y_3346_;
v___y_3297_ = v___y_3338_;
v___y_3298_ = v___y_3339_;
v___y_3299_ = v___y_3348_;
v___y_3300_ = v___y_3340_;
v___y_3301_ = v___x_3353_;
v___y_3302_ = v___y_3337_;
v___y_3303_ = v_argsArray_3343_;
v___y_3304_ = v___y_3349_;
v___y_3305_ = v___y_3351_;
v___y_3306_ = v___y_3345_;
v___y_3307_ = v___y_3341_;
v___y_3308_ = v___y_3342_;
v___y_3309_ = v___y_3347_;
v___y_3310_ = v___y_3344_;
v___y_3311_ = v___x_3353_;
goto v___jp_3294_;
}
else
{
v___y_3295_ = v___y_3350_;
v___y_3296_ = v___y_3346_;
v___y_3297_ = v___y_3338_;
v___y_3298_ = v___y_3339_;
v___y_3299_ = v___y_3348_;
v___y_3300_ = v___y_3340_;
v___y_3301_ = v___x_3353_;
v___y_3302_ = v___y_3337_;
v___y_3303_ = v_argsArray_3343_;
v___y_3304_ = v___y_3349_;
v___y_3305_ = v___y_3351_;
v___y_3306_ = v___y_3345_;
v___y_3307_ = v___y_3341_;
v___y_3308_ = v___y_3342_;
v___y_3309_ = v___y_3347_;
v___y_3310_ = v___y_3344_;
v___y_3311_ = v___y_3337_;
goto v___jp_3294_;
}
}
else
{
if (lean_obj_tag(v___y_3341_) == 0)
{
uint8_t v___x_3354_; 
v___x_3354_ = 0;
v___y_3266_ = v___y_3350_;
v___y_3267_ = v___y_3346_;
v___y_3268_ = v___y_3338_;
v___y_3269_ = v___y_3339_;
v___y_3270_ = v___y_3348_;
v___y_3271_ = v___y_3340_;
v___y_3272_ = v___y_3337_;
v___y_3273_ = v___y_3349_;
v___y_3274_ = v_argsArray_3343_;
v___y_3275_ = v___y_3351_;
v___y_3276_ = v___y_3345_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3342_;
v___y_3279_ = v___y_3347_;
v___y_3280_ = v___y_3344_;
v___y_3281_ = v___x_3354_;
goto v___jp_3265_;
}
else
{
if (v___y_3337_ == 0)
{
v___y_3266_ = v___y_3350_;
v___y_3267_ = v___y_3346_;
v___y_3268_ = v___y_3338_;
v___y_3269_ = v___y_3339_;
v___y_3270_ = v___y_3348_;
v___y_3271_ = v___y_3340_;
v___y_3272_ = v___y_3337_;
v___y_3273_ = v___y_3349_;
v___y_3274_ = v_argsArray_3343_;
v___y_3275_ = v___y_3351_;
v___y_3276_ = v___y_3345_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3342_;
v___y_3279_ = v___y_3347_;
v___y_3280_ = v___y_3344_;
v___y_3281_ = v___y_3337_;
goto v___jp_3265_;
}
else
{
lean_object* v_ref_3355_; uint8_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v_ref_3355_ = lean_ctor_get(v___y_3350_, 5);
v___x_3356_ = 0;
v___x_3357_ = l_Lean_SourceInfo_fromRef(v_ref_3355_, v___x_3356_);
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3359_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3358_);
v___x_3360_ = l_Lean_SourceInfo_fromRef(v_tk_2532_, v___x_2516_);
v___x_3361_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3364_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3340_) == 1)
{
lean_object* v_val_3365_; lean_object* v___x_3366_; 
v_val_3365_ = lean_ctor_get(v___y_3340_, 0);
lean_inc(v_val_3365_);
v___x_3366_ = l_Array_mkArray1___redArg(v_val_3365_);
v___y_3236_ = v___y_3350_;
v___y_3237_ = v___y_3346_;
v___y_3238_ = v___y_3338_;
v___y_3239_ = v___x_3357_;
v___y_3240_ = v___y_3339_;
v___y_3241_ = v___y_3348_;
v___y_3242_ = v___y_3340_;
v___y_3243_ = v___x_3362_;
v___y_3244_ = v___y_3337_;
v___y_3245_ = v___y_3349_;
v___y_3246_ = v___x_3359_;
v___y_3247_ = v_argsArray_3343_;
v___y_3248_ = v___y_3351_;
v___y_3249_ = v___y_3345_;
v___y_3250_ = v___x_3364_;
v___y_3251_ = v___x_3363_;
v___y_3252_ = v___y_3347_;
v___y_3253_ = v___y_3342_;
v___y_3254_ = v___y_3341_;
v___y_3255_ = v___y_3344_;
v___y_3256_ = v___x_3366_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3367_; 
v___x_3367_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3236_ = v___y_3350_;
v___y_3237_ = v___y_3346_;
v___y_3238_ = v___y_3338_;
v___y_3239_ = v___x_3357_;
v___y_3240_ = v___y_3339_;
v___y_3241_ = v___y_3348_;
v___y_3242_ = v___y_3340_;
v___y_3243_ = v___x_3362_;
v___y_3244_ = v___y_3337_;
v___y_3245_ = v___y_3349_;
v___y_3246_ = v___x_3359_;
v___y_3247_ = v_argsArray_3343_;
v___y_3248_ = v___y_3351_;
v___y_3249_ = v___y_3345_;
v___y_3250_ = v___x_3364_;
v___y_3251_ = v___x_3363_;
v___y_3252_ = v___y_3347_;
v___y_3253_ = v___y_3342_;
v___y_3254_ = v___y_3341_;
v___y_3255_ = v___y_3344_;
v___y_3256_ = v___x_3367_;
goto v___jp_3235_;
}
}
}
}
}
v___jp_3368_:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3376_, v___y_3370_, v___y_3379_, v___y_3381_, v___y_3377_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = l_Lean_LibrarySuggestions_select(v_a_3386_, v___y_3384_, v___y_3370_, v___y_3379_, v___y_3381_, v___y_3377_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; size_t v_sz_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v_sz_3389_ = lean_array_size(v_a_3388_);
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3388_, v_sz_3389_, v___x_3390_, v___y_3369_, v___y_3374_, v___y_3376_, v___y_3371_, v___y_3380_, v___y_3370_, v___y_3379_, v___y_3381_, v___y_3377_);
lean_dec(v_a_3388_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref(v___x_3391_);
v___y_3337_ = v___y_3378_;
v___y_3338_ = v___y_3372_;
v___y_3339_ = v___y_3373_;
v___y_3340_ = v___y_3375_;
v___y_3341_ = v___y_3383_;
v___y_3342_ = v___y_3382_;
v_argsArray_3343_ = v_a_3392_;
v___y_3344_ = v___y_3374_;
v___y_3345_ = v___y_3376_;
v___y_3346_ = v___y_3371_;
v___y_3347_ = v___y_3380_;
v___y_3348_ = v___y_3370_;
v___y_3349_ = v___y_3379_;
v___y_3350_ = v___y_3381_;
v___y_3351_ = v___y_3377_;
goto v___jp_3336_;
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3375_);
lean_dec(v___y_3373_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3393_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3391_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3391_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3375_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3369_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3401_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3387_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3387_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3375_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3369_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3409_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3385_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3385_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
v___jp_3417_:
{
uint8_t v_suggestions_3434_; 
v_suggestions_3434_ = lean_ctor_get_uint8(v___y_3428_, sizeof(void*)*3 + 26);
if (v_suggestions_3434_ == 0)
{
lean_dec_ref(v___y_3428_);
lean_dec_ref(v___f_2520_);
v___y_3337_ = v___y_3426_;
v___y_3338_ = v___y_3420_;
v___y_3339_ = v___y_3421_;
v___y_3340_ = v___y_3423_;
v___y_3341_ = v___y_3431_;
v___y_3342_ = v___y_3432_;
v_argsArray_3343_ = v___y_3433_;
v___y_3344_ = v___y_3422_;
v___y_3345_ = v___y_3424_;
v___y_3346_ = v___y_3419_;
v___y_3347_ = v___y_3429_;
v___y_3348_ = v___y_3418_;
v___y_3349_ = v___y_3427_;
v___y_3350_ = v___y_3430_;
v___y_3351_ = v___y_3425_;
goto v___jp_3336_;
}
else
{
lean_object* v_maxSuggestions_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_maxSuggestions_3435_ = lean_ctor_get(v___y_3428_, 2);
lean_inc(v_maxSuggestions_3435_);
lean_dec_ref(v___y_3428_);
v___x_3436_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
v___x_3437_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3435_) == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_unsigned_to_nat(100u);
v___x_3439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
lean_ctor_set(v___x_3439_, 1, v___x_3436_);
lean_ctor_set(v___x_3439_, 2, v___f_2520_);
lean_ctor_set(v___x_3439_, 3, v___x_3437_);
v___y_3369_ = v___y_3433_;
v___y_3370_ = v___y_3418_;
v___y_3371_ = v___y_3419_;
v___y_3372_ = v___y_3420_;
v___y_3373_ = v___y_3421_;
v___y_3374_ = v___y_3422_;
v___y_3375_ = v___y_3423_;
v___y_3376_ = v___y_3424_;
v___y_3377_ = v___y_3425_;
v___y_3378_ = v___y_3426_;
v___y_3379_ = v___y_3427_;
v___y_3380_ = v___y_3429_;
v___y_3381_ = v___y_3430_;
v___y_3382_ = v___y_3432_;
v___y_3383_ = v___y_3431_;
v___y_3384_ = v___x_3439_;
goto v___jp_3368_;
}
else
{
lean_object* v_val_3440_; lean_object* v___x_3441_; 
v_val_3440_ = lean_ctor_get(v_maxSuggestions_3435_, 0);
lean_inc(v_val_3440_);
lean_dec_ref(v_maxSuggestions_3435_);
v___x_3441_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3441_, 0, v_val_3440_);
lean_ctor_set(v___x_3441_, 1, v___x_3436_);
lean_ctor_set(v___x_3441_, 2, v___f_2520_);
lean_ctor_set(v___x_3441_, 3, v___x_3437_);
v___y_3369_ = v___y_3433_;
v___y_3370_ = v___y_3418_;
v___y_3371_ = v___y_3419_;
v___y_3372_ = v___y_3420_;
v___y_3373_ = v___y_3421_;
v___y_3374_ = v___y_3422_;
v___y_3375_ = v___y_3423_;
v___y_3376_ = v___y_3424_;
v___y_3377_ = v___y_3425_;
v___y_3378_ = v___y_3426_;
v___y_3379_ = v___y_3427_;
v___y_3380_ = v___y_3429_;
v___y_3381_ = v___y_3430_;
v___y_3382_ = v___y_3432_;
v___y_3383_ = v___y_3431_;
v___y_3384_ = v___x_3441_;
goto v___jp_3368_;
}
}
}
v___jp_3442_:
{
uint8_t v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = 1;
lean_inc(v___y_3445_);
v___x_3458_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3445_, v___x_3457_, v___y_3446_, v___y_3444_, v___y_3451_, v___y_3443_, v___y_3450_, v___y_3453_, v___y_3449_);
if (lean_obj_tag(v___x_3458_) == 0)
{
if (lean_obj_tag(v___y_3452_) == 1)
{
lean_object* v_a_3459_; lean_object* v_val_3460_; lean_object* v___x_3461_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref(v___x_3458_);
v_val_3460_ = lean_ctor_get(v___y_3452_, 0);
lean_inc(v_val_3460_);
lean_dec_ref(v___y_3452_);
v___x_3461_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3460_);
lean_dec(v_val_3460_);
v___y_3418_ = v___y_3443_;
v___y_3419_ = v___y_3444_;
v___y_3420_ = v___x_3457_;
v___y_3421_ = v___y_3445_;
v___y_3422_ = v___y_3446_;
v___y_3423_ = v___y_3456_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3449_;
v___y_3426_ = v___y_3448_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v_a_3459_;
v___y_3429_ = v___y_3451_;
v___y_3430_ = v___y_3453_;
v___y_3431_ = v___y_3454_;
v___y_3432_ = v___y_3455_;
v___y_3433_ = v___x_3461_;
goto v___jp_3417_;
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3463_; 
lean_dec(v___y_3452_);
v_a_3462_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3458_);
v___x_3463_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3418_ = v___y_3443_;
v___y_3419_ = v___y_3444_;
v___y_3420_ = v___x_3457_;
v___y_3421_ = v___y_3445_;
v___y_3422_ = v___y_3446_;
v___y_3423_ = v___y_3456_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___y_3449_;
v___y_3426_ = v___y_3448_;
v___y_3427_ = v___y_3450_;
v___y_3428_ = v_a_3462_;
v___y_3429_ = v___y_3451_;
v___y_3430_ = v___y_3453_;
v___y_3431_ = v___y_3454_;
v___y_3432_ = v___y_3455_;
v___y_3433_ = v___x_3463_;
goto v___jp_3417_;
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3452_);
lean_dec(v___y_3445_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v_a_3464_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3458_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3458_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
v___jp_3472_:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Syntax_getOptional_x3f(v___y_3474_);
lean_dec(v___y_3474_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_box(0);
v___y_3443_ = v___y_3483_;
v___y_3444_ = v___y_3481_;
v___y_3445_ = v___y_3475_;
v___y_3446_ = v___y_3479_;
v___y_3447_ = v___y_3480_;
v___y_3448_ = v___y_3473_;
v___y_3449_ = v___y_3486_;
v___y_3450_ = v___y_3484_;
v___y_3451_ = v___y_3482_;
v___y_3452_ = v_args_3478_;
v___y_3453_ = v___y_3485_;
v___y_3454_ = v___y_3477_;
v___y_3455_ = v___y_3476_;
v___y_3456_ = v___x_3488_;
goto v___jp_3442_;
}
else
{
lean_object* v_val_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
v_val_3489_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3487_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_val_3489_);
lean_dec(v___x_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_val_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
v___y_3443_ = v___y_3483_;
v___y_3444_ = v___y_3481_;
v___y_3445_ = v___y_3475_;
v___y_3446_ = v___y_3479_;
v___y_3447_ = v___y_3480_;
v___y_3448_ = v___y_3473_;
v___y_3449_ = v___y_3486_;
v___y_3450_ = v___y_3484_;
v___y_3451_ = v___y_3482_;
v___y_3452_ = v_args_3478_;
v___y_3453_ = v___y_3485_;
v___y_3454_ = v___y_3477_;
v___y_3455_ = v___y_3476_;
v___y_3456_ = v___x_3494_;
goto v___jp_3442_;
}
}
}
}
v___jp_3498_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3513_ = lean_unsigned_to_nat(3u);
v___x_3514_ = l_Lean_Syntax_getArg(v___y_3500_, v___x_3513_);
lean_dec(v___y_3500_);
v___x_3515_ = l_Lean_Syntax_isNone(v___x_3514_);
if (v___x_3515_ == 0)
{
uint8_t v___x_3516_; 
lean_inc(v___x_3514_);
v___x_3516_ = l_Lean_Syntax_matchesNull(v___x_3514_, v___x_3497_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v___x_3514_);
lean_dec(v_o_3504_);
lean_dec(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3517_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3518_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_2531_);
lean_dec(v___x_3514_);
v___x_3519_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3520_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3519_);
lean_inc(v___x_3518_);
v___x_3521_ = l_Lean_Syntax_isOfKind(v___x_3518_, v___x_3520_);
lean_dec(v___x_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_dec(v___x_3518_);
lean_dec(v_o_3504_);
lean_dec(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v_args_3524_; lean_object* v___x_3525_; 
v___x_3523_ = l_Lean_Syntax_getArg(v___x_3518_, v___x_3497_);
lean_dec(v___x_3518_);
v_args_3524_ = l_Lean_Syntax_getArgs(v___x_3523_);
lean_dec(v___x_3523_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_args_3524_);
v___y_3473_ = v___y_3499_;
v___y_3474_ = v___y_3501_;
v___y_3475_ = v___y_3502_;
v___y_3476_ = v_o_3504_;
v___y_3477_ = v___y_3503_;
v_args_3478_ = v___x_3525_;
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v___y_3508_;
v___y_3483_ = v___y_3509_;
v___y_3484_ = v___y_3510_;
v___y_3485_ = v___y_3511_;
v___y_3486_ = v___y_3512_;
goto v___jp_3472_;
}
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3514_);
v___x_3526_ = lean_box(0);
v___y_3473_ = v___y_3499_;
v___y_3474_ = v___y_3501_;
v___y_3475_ = v___y_3502_;
v___y_3476_ = v_o_3504_;
v___y_3477_ = v___y_3503_;
v_args_3478_ = v___x_3526_;
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3506_;
v___y_3481_ = v___y_3507_;
v___y_3482_ = v___y_3508_;
v___y_3483_ = v___y_3509_;
v___y_3484_ = v___y_3510_;
v___y_3485_ = v___y_3511_;
v___y_3486_ = v___y_3512_;
goto v___jp_3472_;
}
}
v___jp_3527_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3537_ = lean_unsigned_to_nat(2u);
v___x_3538_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_3537_);
v___x_3539_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3540_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3539_);
lean_inc(v___x_3538_);
v___x_3541_ = l_Lean_Syntax_isOfKind(v___x_3538_, v___x_3540_);
lean_dec(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec(v___x_3538_);
lean_dec(v_bang_3528_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3542_;
}
else
{
lean_object* v_cfg_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; 
v_cfg_3543_ = l_Lean_Syntax_getArg(v___x_3538_, v___x_2531_);
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_3545_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_3544_);
lean_inc(v_cfg_3543_);
v___x_3546_ = l_Lean_Syntax_isOfKind(v_cfg_3543_, v___x_3545_);
lean_dec(v___x_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec(v_cfg_3543_);
lean_dec(v___x_3538_);
lean_dec(v_bang_3528_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3547_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3548_ = l_Lean_Syntax_getArg(v___x_3538_, v___x_3497_);
v___x_3549_ = l_Lean_Syntax_getArg(v___x_3538_, v___x_3537_);
v___x_3550_ = l_Lean_Syntax_isNone(v___x_3549_);
if (v___x_3550_ == 0)
{
uint8_t v___x_3551_; 
lean_inc(v___x_3549_);
v___x_3551_ = l_Lean_Syntax_matchesNull(v___x_3549_, v___x_3497_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
lean_dec(v___x_3549_);
lean_dec(v___x_3548_);
lean_dec(v_cfg_3543_);
lean_dec(v___x_3538_);
lean_dec(v_bang_3528_);
lean_dec(v_tk_2532_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
v___x_3552_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3552_;
}
else
{
lean_object* v_o_3553_; lean_object* v___x_3554_; 
v_o_3553_ = l_Lean_Syntax_getArg(v___x_3549_, v___x_2531_);
lean_dec(v___x_3549_);
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_o_3553_);
v___y_3499_ = v___x_3546_;
v___y_3500_ = v___x_3538_;
v___y_3501_ = v___x_3548_;
v___y_3502_ = v_cfg_3543_;
v___y_3503_ = v_bang_3528_;
v_o_3504_ = v___x_3554_;
v___y_3505_ = v___y_3529_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v___y_3532_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3534_;
v___y_3511_ = v___y_3535_;
v___y_3512_ = v___y_3536_;
goto v___jp_3498_;
}
}
else
{
lean_object* v___x_3555_; 
lean_dec(v___x_3549_);
v___x_3555_ = lean_box(0);
v___y_3499_ = v___x_3546_;
v___y_3500_ = v___x_3538_;
v___y_3501_ = v___x_3548_;
v___y_3502_ = v_cfg_3543_;
v___y_3503_ = v_bang_3528_;
v_o_3504_ = v___x_3555_;
v___y_3505_ = v___y_3529_;
v___y_3506_ = v___y_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v___y_3532_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3534_;
v___y_3511_ = v___y_3535_;
v___y_3512_ = v___y_3536_;
goto v___jp_3498_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3563_, lean_object* v_stx_3564_, lean_object* v___x_3565_, lean_object* v___x_3566_, lean_object* v___x_3567_, lean_object* v___x_3568_, lean_object* v___f_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
uint8_t v___x_39070__boxed_3579_; uint8_t v___x_39071__boxed_3580_; lean_object* v_res_3581_; 
v___x_39070__boxed_3579_ = lean_unbox(v___x_3563_);
v___x_39071__boxed_3580_ = lean_unbox(v___x_3565_);
v_res_3581_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_39070__boxed_3579_, v_stx_3564_, v___x_39071__boxed_3580_, v___x_3566_, v___x_3567_, v___x_3568_, v___f_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v_stx_3564_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; uint8_t v___x_3603_; lean_object* v___f_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___y_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3601_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3588_);
v___x_3602_ = l_Lean_Syntax_isOfKind(v_stx_3588_, v___x_3601_);
v___x_3603_ = 1;
v___f_3604_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3605_ = lean_box(v___x_3602_);
v___x_3606_ = lean_box(v___x_3603_);
v___y_3607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3607_, 0, v___x_3605_);
lean_closure_set(v___y_3607_, 1, v_stx_3588_);
lean_closure_set(v___y_3607_, 2, v___x_3606_);
lean_closure_set(v___y_3607_, 3, v___x_3598_);
lean_closure_set(v___y_3607_, 4, v___x_3599_);
lean_closure_set(v___y_3607_, 5, v___x_3600_);
lean_closure_set(v___y_3607_, 6, v___f_3604_);
v___x_3608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3608_, 0, v___y_3607_);
v___x_3609_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3608_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3621_, lean_object* v_as_3622_, lean_object* v_as_x27_3623_, lean_object* v_b_3624_, lean_object* v_a_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3621_, v_as_x27_3623_, v_b_3624_, v___y_3632_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3636_, lean_object* v_as_3637_, lean_object* v_as_x27_3638_, lean_object* v_b_3639_, lean_object* v_a_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3636_, v_as_3637_, v_as_x27_3638_, v_b_3639_, v_a_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v_as_x27_3638_);
lean_dec(v_as_3637_);
lean_dec(v___x_3636_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3658_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3659_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3662_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3658_, v___x_3659_, v___x_3660_, v___x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3692_ = l_Lean_addBuiltinDeclarationRanges(v___x_3690_, v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3695_, lean_object* v_simprocs_3696_, lean_object* v_fvarIdsToSimp_3697_, uint8_t v_simplifyTarget_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
v___x_3707_ = lean_unsigned_to_nat(32u);
v___x_3708_ = lean_mk_empty_array_with_capacity(v___x_3707_);
lean_dec_ref(v___x_3708_);
v___x_3709_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6);
v___x_3710_ = l_Lean_Meta_dsimpGoal(v_a_3706_, v_ctx_3695_, v_simprocs_3696_, v_simplifyTarget_3698_, v_fvarIdsToSimp_3697_, v___x_3709_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v_fst_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref(v___x_3710_);
v_fst_3712_ = lean_ctor_get(v_a_3711_, 0);
if (lean_obj_tag(v_fst_3712_) == 0)
{
lean_object* v_snd_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_snd_3713_ = lean_ctor_get(v_a_3711_, 1);
lean_inc(v_snd_3713_);
lean_dec(v_a_3711_);
v___x_3714_ = lean_box(0);
v___x_3715_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3714_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; 
v_unused_3723_ = lean_ctor_get(v___x_3715_, 0);
lean_dec(v_unused_3723_);
v___x_3717_ = v___x_3715_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v___x_3715_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v_snd_3713_);
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_snd_3713_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_snd_3713_);
v_a_3724_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3715_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3715_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_snd_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3758_; 
lean_inc_ref(v_fst_3712_);
v_snd_3732_ = lean_ctor_get(v_a_3711_, 1);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3711_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v_a_3711_, 0);
lean_dec(v_unused_3759_);
v___x_3734_ = v_a_3711_;
v_isShared_3735_ = v_isSharedCheck_3758_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_snd_3732_);
lean_dec(v_a_3711_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3758_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_val_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v_val_3736_ = lean_ctor_get(v_fst_3712_, 0);
lean_inc(v_val_3736_);
lean_dec_ref(v_fst_3712_);
v___x_3737_ = lean_box(0);
if (v_isShared_3735_ == 0)
{
lean_ctor_set_tag(v___x_3734_, 1);
lean_ctor_set(v___x_3734_, 1, v___x_3737_);
lean_ctor_set(v___x_3734_, 0, v_val_3736_);
v___x_3739_ = v___x_3734_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_val_3736_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3739_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; 
v_unused_3748_ = lean_ctor_get(v___x_3740_, 0);
lean_dec(v_unused_3748_);
v___x_3742_ = v___x_3740_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_dec(v___x_3740_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v_snd_3732_);
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_snd_3732_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_snd_3732_);
v_a_3749_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3740_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3740_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3710_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3710_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_fvarIdsToSimp_3697_);
lean_dec_ref(v_simprocs_3696_);
lean_dec_ref(v_ctx_3695_);
v_a_3768_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3705_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3705_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3776_, lean_object* v_simprocs_3777_, lean_object* v_fvarIdsToSimp_3778_, lean_object* v_simplifyTarget_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
uint8_t v_simplifyTarget_boxed_3786_; lean_object* v_res_3787_; 
v_simplifyTarget_boxed_3786_ = lean_unbox(v_simplifyTarget_3779_);
v_res_3787_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3776_, v_simprocs_3777_, v_fvarIdsToSimp_3778_, v_simplifyTarget_boxed_3786_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3788_, lean_object* v_simprocs_3789_, lean_object* v_fvarIdsToSimp_3790_, uint8_t v_simplifyTarget_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3788_, v_simprocs_3789_, v_fvarIdsToSimp_3790_, v_simplifyTarget_3791_, v_a_3793_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3802_, lean_object* v_simprocs_3803_, lean_object* v_fvarIdsToSimp_3804_, lean_object* v_simplifyTarget_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
uint8_t v_simplifyTarget_boxed_3815_; lean_object* v_res_3816_; 
v_simplifyTarget_boxed_3815_ = lean_unbox(v_simplifyTarget_3805_);
v_res_3816_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3802_, v_simprocs_3803_, v_fvarIdsToSimp_3804_, v_simplifyTarget_boxed_3815_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3817_, lean_object* v_simprocs_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3820_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = l_Lean_MVarId_getNondepPropHyps(v_a_3829_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; uint8_t v___x_3832_; lean_object* v___x_3833_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
v___x_3832_ = 1;
v___x_3833_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3817_, v_simprocs_3818_, v_a_3831_, v___x_3832_, v___y_3820_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3833_;
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v_simprocs_3818_);
lean_dec_ref(v_ctx_3817_);
v_a_3834_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3830_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3830_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v_simprocs_3818_);
lean_dec_ref(v_ctx_3817_);
v_a_3842_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3828_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3828_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3850_, lean_object* v_simprocs_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3850_, v_simprocs_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3862_, lean_object* v_ctx_3863_, lean_object* v_simprocs_3864_, uint8_t v_type_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3862_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref(v___x_3875_);
v___x_3877_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3863_, v_simprocs_3864_, v_a_3876_, v_type_3865_, v___y_3867_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_simprocs_3864_);
lean_dec_ref(v_ctx_3863_);
v_a_3878_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3875_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3875_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3886_, lean_object* v_ctx_3887_, lean_object* v_simprocs_3888_, lean_object* v_type_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v_type_635__boxed_3899_; lean_object* v_res_3900_; 
v_type_635__boxed_3899_ = lean_unbox(v_type_3889_);
v_res_3900_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3886_, v_ctx_3887_, v_simprocs_3888_, v_type_635__boxed_3899_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3901_, lean_object* v_simprocs_3902_, lean_object* v_loc_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
if (lean_obj_tag(v_loc_3903_) == 0)
{
lean_object* v___f_3913_; lean_object* v___x_3914_; 
v___f_3913_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3913_, 0, v_ctx_3901_);
lean_closure_set(v___f_3913_, 1, v_simprocs_3902_);
v___x_3914_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3913_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
return v___x_3914_;
}
else
{
lean_object* v_hypotheses_3915_; uint8_t v_type_3916_; lean_object* v___x_3917_; lean_object* v___f_3918_; lean_object* v___x_3919_; 
v_hypotheses_3915_ = lean_ctor_get(v_loc_3903_, 0);
lean_inc_ref(v_hypotheses_3915_);
v_type_3916_ = lean_ctor_get_uint8(v_loc_3903_, sizeof(void*)*1);
lean_dec_ref(v_loc_3903_);
v___x_3917_ = lean_box(v_type_3916_);
v___f_3918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3918_, 0, v_hypotheses_3915_);
lean_closure_set(v___f_3918_, 1, v_ctx_3901_);
lean_closure_set(v___f_3918_, 2, v_simprocs_3902_);
lean_closure_set(v___f_3918_, 3, v___x_3917_);
v___x_3919_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3918_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
return v___x_3919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3920_, lean_object* v_simprocs_3921_, lean_object* v_loc_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3920_, v_simprocs_3921_, v_loc_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3937_, lean_object* v_stx_3938_, uint8_t v___x_3939_, lean_object* v___x_3940_, lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
if (v___x_3937_ == 0)
{
lean_object* v___x_3952_; 
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_3952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3952_;
}
else
{
lean_object* v___x_3953_; lean_object* v_tk_3954_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v_stx_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4077_; uint8_t v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4102_; uint8_t v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4129_; uint8_t v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; uint8_t v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; uint8_t v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4245_; uint8_t v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; uint8_t v___y_4259_; lean_object* v___y_4276_; uint8_t v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4309_; lean_object* v___y_4310_; uint8_t v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v_args_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___x_4335_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; uint8_t v___y_4340_; lean_object* v___y_4341_; lean_object* v_o_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v_bang_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_3953_ = lean_unsigned_to_nat(0u);
v_tk_3954_ = l_Lean_Syntax_getArg(v_stx_3938_, v___x_3953_);
v___x_4335_ = lean_unsigned_to_nat(1u);
v___x_4392_ = l_Lean_Syntax_getArg(v_stx_3938_, v___x_4335_);
v___x_4393_ = l_Lean_Syntax_isNone(v___x_4392_);
if (v___x_4393_ == 0)
{
uint8_t v___x_4394_; 
lean_inc(v___x_4392_);
v___x_4394_ = l_Lean_Syntax_matchesNull(v___x_4392_, v___x_4335_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; 
lean_dec(v___x_4392_);
lean_dec(v_tk_3954_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_4395_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4395_;
}
else
{
lean_object* v_bang_4396_; lean_object* v___x_4397_; 
v_bang_4396_ = l_Lean_Syntax_getArg(v___x_4392_, v___x_3953_);
lean_dec(v___x_4392_);
v___x_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4397_, 0, v_bang_4396_);
v_bang_4365_ = v___x_4397_;
v___y_4366_ = v___y_3943_;
v___y_4367_ = v___y_3944_;
v___y_4368_ = v___y_3945_;
v___y_4369_ = v___y_3946_;
v___y_4370_ = v___y_3947_;
v___y_4371_ = v___y_3948_;
v___y_4372_ = v___y_3949_;
v___y_4373_ = v___y_3950_;
goto v___jp_4364_;
}
}
else
{
lean_object* v___x_4398_; 
lean_dec(v___x_4392_);
v___x_4398_ = lean_box(0);
v_bang_4365_ = v___x_4398_;
v___y_4366_ = v___y_3943_;
v___y_4367_ = v___y_3944_;
v___y_4368_ = v___y_3945_;
v___y_4369_ = v___y_3946_;
v___y_4370_ = v___y_3947_;
v___y_4371_ = v___y_3948_;
v___y_4372_ = v___y_3949_;
v___y_4373_ = v___y_3950_;
goto v___jp_4364_;
}
v___jp_3955_:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3962_, v___y_3964_, v___y_3967_, v___y_3958_, v___y_3963_, v___y_3961_, v___y_3956_, v___y_3960_, v___y_3959_, v___y_3957_, v___y_3966_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v_usedTheorems_3970_; lean_object* v_diag_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_4013_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v_usedTheorems_3970_ = lean_ctor_get(v_a_3969_, 0);
v_diag_3971_ = lean_ctor_get(v_a_3969_, 1);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_a_3969_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3973_ = v_a_3969_;
v_isShared_3974_ = v_isSharedCheck_4013_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_diag_3971_);
lean_inc(v_usedTheorems_3970_);
lean_dec(v_a_3969_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_4013_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3965_, v_usedTheorems_3970_, v___y_3960_, v___y_3959_, v___y_3957_, v___y_3966_);
lean_dec_ref(v_usedTheorems_3970_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v_ref_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref(v___x_3975_);
v_ref_3977_ = lean_ctor_get(v___y_3957_, 5);
v___x_3978_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 1, v_a_3976_);
lean_ctor_set(v___x_3973_, 0, v___x_3978_);
v___x_3980_ = v___x_3973_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_a_3976_);
v___x_3980_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3981_ = lean_box(0);
v___x_3982_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
lean_ctor_set(v___x_3982_, 2, v___x_3981_);
lean_ctor_set(v___x_3982_, 3, v___x_3981_);
lean_ctor_set(v___x_3982_, 4, v___x_3981_);
lean_ctor_set(v___x_3982_, 5, v___x_3981_);
lean_inc(v_ref_3977_);
v___x_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3983_, 0, v_ref_3977_);
v___x_3984_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3985_ = 4;
v___x_3986_ = l_Lean_MessageData_nil;
v___x_3987_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3954_, v___x_3982_, v___x_3983_, v___x_3984_, v___x_3981_, v___x_3985_, v___x_3986_, v___y_3957_, v___y_3966_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; 
v_unused_3995_ = lean_ctor_get(v___x_3987_, 0);
lean_dec(v_unused_3995_);
v___x_3989_ = v___x_3987_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v___x_3987_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v_diag_3971_);
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_diag_3971_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v_diag_3971_);
v_a_3996_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3987_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3987_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_del_object(v___x_3973_);
lean_dec_ref(v_diag_3971_);
lean_dec(v_tk_3954_);
v_a_4005_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3975_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3975_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v___y_3965_);
lean_dec(v_tk_3954_);
v_a_4014_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3968_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3968_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
v___jp_4022_:
{
if (lean_obj_tag(v___y_4026_) == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_4036_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*1, v___x_3939_);
v___y_3956_ = v___y_4023_;
v___y_3957_ = v___y_4024_;
v___y_3958_ = v___y_4025_;
v___y_3959_ = v___y_4028_;
v___y_3960_ = v___y_4027_;
v___y_3961_ = v___y_4029_;
v___y_3962_ = v___y_4034_;
v___y_3963_ = v___y_4030_;
v___y_3964_ = v___y_4031_;
v___y_3965_ = v___y_4033_;
v___y_3966_ = v___y_4032_;
v___y_3967_ = v___x_4036_;
goto v___jp_3955_;
}
else
{
lean_object* v_val_4037_; lean_object* v___x_4038_; 
v_val_4037_ = lean_ctor_get(v___y_4026_, 0);
lean_inc(v_val_4037_);
lean_dec_ref(v___y_4026_);
v___x_4038_ = l_Lean_Elab_Tactic_expandLocation(v_val_4037_);
lean_dec(v_val_4037_);
v___y_3956_ = v___y_4023_;
v___y_3957_ = v___y_4024_;
v___y_3958_ = v___y_4025_;
v___y_3959_ = v___y_4028_;
v___y_3960_ = v___y_4027_;
v___y_3961_ = v___y_4029_;
v___y_3962_ = v___y_4034_;
v___y_3963_ = v___y_4030_;
v___y_3964_ = v___y_4031_;
v___y_3965_ = v___y_4033_;
v___y_3966_ = v___y_4032_;
v___y_3967_ = v___x_4038_;
goto v___jp_3955_;
}
}
v___jp_4039_:
{
uint8_t v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4052_ = 0;
v___x_4053_ = 2;
v___x_4054_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4055_ = lean_box(v___x_4052_);
v___x_4056_ = lean_box(v___x_4053_);
v___x_4057_ = lean_box(v___x_4052_);
lean_inc(v_stx_4043_);
v___x_4058_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4058_, 0, v_stx_4043_);
lean_closure_set(v___x_4058_, 1, v___x_4055_);
lean_closure_set(v___x_4058_, 2, v___x_4056_);
lean_closure_set(v___x_4058_, 3, v___x_4057_);
lean_closure_set(v___x_4058_, 4, v___x_4054_);
v___x_4059_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4058_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref(v___x_4059_);
if (lean_obj_tag(v___y_4041_) == 0)
{
lean_object* v_ctx_4061_; lean_object* v_simprocs_4062_; 
v_ctx_4061_ = lean_ctor_get(v_a_4060_, 0);
lean_inc_ref(v_ctx_4061_);
v_simprocs_4062_ = lean_ctor_get(v_a_4060_, 1);
lean_inc_ref(v_simprocs_4062_);
lean_dec(v_a_4060_);
v___y_4023_ = v___y_4047_;
v___y_4024_ = v___y_4050_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v___y_4040_;
v___y_4027_ = v___y_4048_;
v___y_4028_ = v___y_4049_;
v___y_4029_ = v___y_4046_;
v___y_4030_ = v___y_4045_;
v___y_4031_ = v_simprocs_4062_;
v___y_4032_ = v___y_4051_;
v___y_4033_ = v_stx_4043_;
v___y_4034_ = v_ctx_4061_;
goto v___jp_4022_;
}
else
{
lean_dec_ref(v___y_4041_);
if (v___y_4042_ == 0)
{
lean_object* v_ctx_4063_; lean_object* v_simprocs_4064_; 
v_ctx_4063_ = lean_ctor_get(v_a_4060_, 0);
lean_inc_ref(v_ctx_4063_);
v_simprocs_4064_ = lean_ctor_get(v_a_4060_, 1);
lean_inc_ref(v_simprocs_4064_);
lean_dec(v_a_4060_);
v___y_4023_ = v___y_4047_;
v___y_4024_ = v___y_4050_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v___y_4040_;
v___y_4027_ = v___y_4048_;
v___y_4028_ = v___y_4049_;
v___y_4029_ = v___y_4046_;
v___y_4030_ = v___y_4045_;
v___y_4031_ = v_simprocs_4064_;
v___y_4032_ = v___y_4051_;
v___y_4033_ = v_stx_4043_;
v___y_4034_ = v_ctx_4063_;
goto v___jp_4022_;
}
else
{
lean_object* v_ctx_4065_; lean_object* v_simprocs_4066_; lean_object* v___x_4067_; 
v_ctx_4065_ = lean_ctor_get(v_a_4060_, 0);
lean_inc_ref(v_ctx_4065_);
v_simprocs_4066_ = lean_ctor_get(v_a_4060_, 1);
lean_inc_ref(v_simprocs_4066_);
lean_dec(v_a_4060_);
v___x_4067_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4065_);
v___y_4023_ = v___y_4047_;
v___y_4024_ = v___y_4050_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v___y_4040_;
v___y_4027_ = v___y_4048_;
v___y_4028_ = v___y_4049_;
v___y_4029_ = v___y_4046_;
v___y_4030_ = v___y_4045_;
v___y_4031_ = v_simprocs_4066_;
v___y_4032_ = v___y_4051_;
v___y_4033_ = v_stx_4043_;
v___y_4034_ = v___x_4067_;
goto v___jp_4022_;
}
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec(v_stx_4043_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v_tk_3954_);
v_a_4068_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4059_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4059_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
v___jp_4076_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_inc_ref(v___y_4082_);
v___x_4098_ = l_Array_append___redArg(v___y_4082_, v___y_4097_);
lean_dec_ref(v___y_4097_);
lean_inc(v___y_4092_);
lean_inc(v___y_4087_);
v___x_4099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4087_);
lean_ctor_set(v___x_4099_, 1, v___y_4092_);
lean_ctor_set(v___x_4099_, 2, v___x_4098_);
v___x_4100_ = l_Lean_Syntax_node6(v___y_4087_, v___y_4089_, v___y_4083_, v___y_4085_, v___y_4093_, v___y_4079_, v___y_4094_, v___x_4099_);
v___y_4040_ = v___y_4086_;
v___y_4041_ = v___y_4088_;
v___y_4042_ = v___y_4078_;
v_stx_4043_ = v___x_4100_;
v___y_4044_ = v___y_4090_;
v___y_4045_ = v___y_4077_;
v___y_4046_ = v___y_4080_;
v___y_4047_ = v___y_4084_;
v___y_4048_ = v___y_4096_;
v___y_4049_ = v___y_4081_;
v___y_4050_ = v___y_4095_;
v___y_4051_ = v___y_4091_;
goto v___jp_4039_;
}
v___jp_4101_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_inc_ref(v___y_4106_);
v___x_4122_ = l_Array_append___redArg(v___y_4106_, v___y_4121_);
lean_dec_ref(v___y_4121_);
lean_inc(v___y_4117_);
lean_inc(v___y_4111_);
v___x_4123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4123_, 0, v___y_4111_);
lean_ctor_set(v___x_4123_, 1, v___y_4117_);
lean_ctor_set(v___x_4123_, 2, v___x_4122_);
if (lean_obj_tag(v___y_4112_) == 0)
{
lean_object* v___x_4124_; 
v___x_4124_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4107_;
v___y_4082_ = v___y_4106_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4112_;
v___y_4087_ = v___y_4111_;
v___y_4088_ = v___y_4115_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4113_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4118_;
v___y_4094_ = v___x_4123_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4120_;
v___y_4097_ = v___x_4124_;
goto v___jp_4076_;
}
else
{
lean_object* v_val_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_val_4125_ = lean_ctor_get(v___y_4112_, 0);
v___x_4126_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4125_);
v___x_4127_ = lean_array_push(v___x_4126_, v_val_4125_);
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4103_;
v___y_4079_ = v___y_4104_;
v___y_4080_ = v___y_4105_;
v___y_4081_ = v___y_4107_;
v___y_4082_ = v___y_4106_;
v___y_4083_ = v___y_4108_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4112_;
v___y_4087_ = v___y_4111_;
v___y_4088_ = v___y_4115_;
v___y_4089_ = v___y_4114_;
v___y_4090_ = v___y_4113_;
v___y_4091_ = v___y_4116_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4118_;
v___y_4094_ = v___x_4123_;
v___y_4095_ = v___y_4119_;
v___y_4096_ = v___y_4120_;
v___y_4097_ = v___x_4127_;
goto v___jp_4076_;
}
}
v___jp_4128_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_inc_ref(v___y_4132_);
v___x_4149_ = l_Array_append___redArg(v___y_4132_, v___y_4148_);
lean_dec_ref(v___y_4148_);
lean_inc(v___y_4143_);
lean_inc(v___y_4137_);
v___x_4150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4150_, 0, v___y_4137_);
lean_ctor_set(v___x_4150_, 1, v___y_4143_);
lean_ctor_set(v___x_4150_, 2, v___x_4149_);
if (lean_obj_tag(v___y_4147_) == 1)
{
lean_object* v_val_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_val_4151_ = lean_ctor_get(v___y_4147_, 0);
lean_inc(v_val_4151_);
lean_dec_ref(v___y_4147_);
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4137_, 3);
v___x_4153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___y_4137_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
lean_inc_ref(v___y_4132_);
v___x_4154_ = l_Array_append___redArg(v___y_4132_, v_val_4151_);
lean_dec(v_val_4151_);
lean_inc(v___y_4143_);
v___x_4155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4155_, 0, v___y_4137_);
lean_ctor_set(v___x_4155_, 1, v___y_4143_);
lean_ctor_set(v___x_4155_, 2, v___x_4154_);
v___x_4156_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___y_4137_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Array_mkArray3___redArg(v___x_4153_, v___x_4155_, v___x_4157_);
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___x_4150_;
v___y_4105_ = v___y_4131_;
v___y_4106_ = v___y_4132_;
v___y_4107_ = v___y_4133_;
v___y_4108_ = v___y_4134_;
v___y_4109_ = v___y_4135_;
v___y_4110_ = v___y_4136_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4138_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___y_4139_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4144_;
v___y_4119_ = v___y_4145_;
v___y_4120_ = v___y_4146_;
v___y_4121_ = v___x_4158_;
goto v___jp_4101_;
}
else
{
lean_object* v___x_4159_; 
lean_dec(v___y_4147_);
v___x_4159_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___x_4150_;
v___y_4105_ = v___y_4131_;
v___y_4106_ = v___y_4132_;
v___y_4107_ = v___y_4133_;
v___y_4108_ = v___y_4134_;
v___y_4109_ = v___y_4135_;
v___y_4110_ = v___y_4136_;
v___y_4111_ = v___y_4137_;
v___y_4112_ = v___y_4138_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4140_;
v___y_4115_ = v___y_4139_;
v___y_4116_ = v___y_4142_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4144_;
v___y_4119_ = v___y_4145_;
v___y_4120_ = v___y_4146_;
v___y_4121_ = v___x_4159_;
goto v___jp_4101_;
}
}
v___jp_4160_:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_inc_ref(v___y_4162_);
v___x_4182_ = l_Array_append___redArg(v___y_4162_, v___y_4181_);
lean_dec_ref(v___y_4181_);
lean_inc(v___y_4171_);
lean_inc(v___y_4161_);
v___x_4183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4183_, 0, v___y_4161_);
lean_ctor_set(v___x_4183_, 1, v___y_4171_);
lean_ctor_set(v___x_4183_, 2, v___x_4182_);
v___x_4184_ = l_Lean_Syntax_node6(v___y_4161_, v___y_4163_, v___y_4169_, v___y_4172_, v___y_4178_, v___y_4164_, v___y_4180_, v___x_4183_);
v___y_4040_ = v___y_4173_;
v___y_4041_ = v___y_4174_;
v___y_4042_ = v___y_4166_;
v_stx_4043_ = v___x_4184_;
v___y_4044_ = v___y_4175_;
v___y_4045_ = v___y_4165_;
v___y_4046_ = v___y_4167_;
v___y_4047_ = v___y_4170_;
v___y_4048_ = v___y_4179_;
v___y_4049_ = v___y_4168_;
v___y_4050_ = v___y_4177_;
v___y_4051_ = v___y_4176_;
goto v___jp_4039_;
}
v___jp_4185_:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_inc_ref(v___y_4187_);
v___x_4206_ = l_Array_append___redArg(v___y_4187_, v___y_4205_);
lean_dec_ref(v___y_4205_);
lean_inc(v___y_4196_);
lean_inc(v___y_4186_);
v___x_4207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4207_, 0, v___y_4186_);
lean_ctor_set(v___x_4207_, 1, v___y_4196_);
lean_ctor_set(v___x_4207_, 2, v___x_4206_);
if (lean_obj_tag(v___y_4198_) == 0)
{
lean_object* v___x_4208_; 
v___x_4208_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___y_4189_;
v___y_4165_ = v___y_4190_;
v___y_4166_ = v___y_4191_;
v___y_4167_ = v___y_4192_;
v___y_4168_ = v___y_4193_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4195_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4197_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4200_;
v___y_4175_ = v___y_4199_;
v___y_4176_ = v___y_4201_;
v___y_4177_ = v___y_4203_;
v___y_4178_ = v___y_4202_;
v___y_4179_ = v___y_4204_;
v___y_4180_ = v___x_4207_;
v___y_4181_ = v___x_4208_;
goto v___jp_4160_;
}
else
{
lean_object* v_val_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v_val_4209_ = lean_ctor_get(v___y_4198_, 0);
v___x_4210_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4209_);
v___x_4211_ = lean_array_push(v___x_4210_, v_val_4209_);
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4188_;
v___y_4164_ = v___y_4189_;
v___y_4165_ = v___y_4190_;
v___y_4166_ = v___y_4191_;
v___y_4167_ = v___y_4192_;
v___y_4168_ = v___y_4193_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4195_;
v___y_4171_ = v___y_4196_;
v___y_4172_ = v___y_4197_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4200_;
v___y_4175_ = v___y_4199_;
v___y_4176_ = v___y_4201_;
v___y_4177_ = v___y_4203_;
v___y_4178_ = v___y_4202_;
v___y_4179_ = v___y_4204_;
v___y_4180_ = v___x_4207_;
v___y_4181_ = v___x_4211_;
goto v___jp_4160_;
}
}
v___jp_4212_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_inc_ref(v___y_4214_);
v___x_4233_ = l_Array_append___redArg(v___y_4214_, v___y_4232_);
lean_dec_ref(v___y_4232_);
lean_inc(v___y_4222_);
lean_inc(v___y_4213_);
v___x_4234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4234_, 0, v___y_4213_);
lean_ctor_set(v___x_4234_, 1, v___y_4222_);
lean_ctor_set(v___x_4234_, 2, v___x_4233_);
if (lean_obj_tag(v___y_4231_) == 1)
{
lean_object* v_val_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_val_4235_ = lean_ctor_get(v___y_4231_, 0);
lean_inc(v_val_4235_);
lean_dec_ref(v___y_4231_);
v___x_4236_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4213_, 3);
v___x_4237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___y_4213_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
lean_inc_ref(v___y_4214_);
v___x_4238_ = l_Array_append___redArg(v___y_4214_, v_val_4235_);
lean_dec(v_val_4235_);
lean_inc(v___y_4222_);
v___x_4239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4239_, 0, v___y_4213_);
lean_ctor_set(v___x_4239_, 1, v___y_4222_);
lean_ctor_set(v___x_4239_, 2, v___x_4238_);
v___x_4240_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___y_4213_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = l_Array_mkArray3___redArg(v___x_4237_, v___x_4239_, v___x_4241_);
v___y_4186_ = v___y_4213_;
v___y_4187_ = v___y_4214_;
v___y_4188_ = v___y_4215_;
v___y_4189_ = v___x_4234_;
v___y_4190_ = v___y_4216_;
v___y_4191_ = v___y_4217_;
v___y_4192_ = v___y_4218_;
v___y_4193_ = v___y_4219_;
v___y_4194_ = v___y_4220_;
v___y_4195_ = v___y_4221_;
v___y_4196_ = v___y_4222_;
v___y_4197_ = v___y_4223_;
v___y_4198_ = v___y_4224_;
v___y_4199_ = v___y_4226_;
v___y_4200_ = v___y_4225_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4228_;
v___y_4204_ = v___y_4230_;
v___y_4205_ = v___x_4242_;
goto v___jp_4185_;
}
else
{
lean_object* v___x_4243_; 
lean_dec(v___y_4231_);
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4186_ = v___y_4213_;
v___y_4187_ = v___y_4214_;
v___y_4188_ = v___y_4215_;
v___y_4189_ = v___x_4234_;
v___y_4190_ = v___y_4216_;
v___y_4191_ = v___y_4217_;
v___y_4192_ = v___y_4218_;
v___y_4193_ = v___y_4219_;
v___y_4194_ = v___y_4220_;
v___y_4195_ = v___y_4221_;
v___y_4196_ = v___y_4222_;
v___y_4197_ = v___y_4223_;
v___y_4198_ = v___y_4224_;
v___y_4199_ = v___y_4226_;
v___y_4200_ = v___y_4225_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4228_;
v___y_4204_ = v___y_4230_;
v___y_4205_ = v___x_4243_;
goto v___jp_4185_;
}
}
v___jp_4244_:
{
lean_object* v_ref_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v_ref_4260_ = lean_ctor_get(v___y_4255_, 5);
v___x_4261_ = l_Lean_SourceInfo_fromRef(v_ref_4260_, v___y_4259_);
v___x_4262_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4263_ = l_Lean_Name_mkStr4(v___x_3940_, v___x_3941_, v___x_3942_, v___x_4262_);
v___x_4264_ = l_Lean_SourceInfo_fromRef(v_tk_3954_, v___x_3939_);
v___x_4265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
lean_ctor_set(v___x_4265_, 1, v___x_4262_);
v___x_4266_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4267_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4261_);
v___x_4268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4261_);
lean_ctor_set(v___x_4268_, 1, v___x_4266_);
lean_ctor_set(v___x_4268_, 2, v___x_4267_);
if (lean_obj_tag(v___y_4258_) == 1)
{
lean_object* v_val_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_val_4269_ = lean_ctor_get(v___y_4258_, 0);
lean_inc(v_val_4269_);
lean_dec_ref(v___y_4258_);
v___x_4270_ = l_Lean_SourceInfo_fromRef(v_val_4269_, v___x_3939_);
lean_dec(v_val_4269_);
v___x_4271_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = l_Array_mkArray1___redArg(v___x_4272_);
v___y_4129_ = v___y_4245_;
v___y_4130_ = v___y_4246_;
v___y_4131_ = v___y_4247_;
v___y_4132_ = v___x_4267_;
v___y_4133_ = v___y_4248_;
v___y_4134_ = v___x_4265_;
v___y_4135_ = v___y_4249_;
v___y_4136_ = v___y_4250_;
v___y_4137_ = v___x_4261_;
v___y_4138_ = v___y_4251_;
v___y_4139_ = v___y_4252_;
v___y_4140_ = v___x_4263_;
v___y_4141_ = v___y_4253_;
v___y_4142_ = v___y_4254_;
v___y_4143_ = v___x_4266_;
v___y_4144_ = v___x_4268_;
v___y_4145_ = v___y_4255_;
v___y_4146_ = v___y_4256_;
v___y_4147_ = v___y_4257_;
v___y_4148_ = v___x_4273_;
goto v___jp_4128_;
}
else
{
lean_object* v___x_4274_; 
lean_dec(v___y_4258_);
v___x_4274_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4129_ = v___y_4245_;
v___y_4130_ = v___y_4246_;
v___y_4131_ = v___y_4247_;
v___y_4132_ = v___x_4267_;
v___y_4133_ = v___y_4248_;
v___y_4134_ = v___x_4265_;
v___y_4135_ = v___y_4249_;
v___y_4136_ = v___y_4250_;
v___y_4137_ = v___x_4261_;
v___y_4138_ = v___y_4251_;
v___y_4139_ = v___y_4252_;
v___y_4140_ = v___x_4263_;
v___y_4141_ = v___y_4253_;
v___y_4142_ = v___y_4254_;
v___y_4143_ = v___x_4266_;
v___y_4144_ = v___x_4268_;
v___y_4145_ = v___y_4255_;
v___y_4146_ = v___y_4256_;
v___y_4147_ = v___y_4257_;
v___y_4148_ = v___x_4274_;
goto v___jp_4128_;
}
}
v___jp_4275_:
{
if (lean_obj_tag(v___y_4282_) == 0)
{
uint8_t v___x_4290_; 
v___x_4290_ = 0;
v___y_4245_ = v___y_4276_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4278_;
v___y_4248_ = v___y_4279_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v___y_4281_;
v___y_4251_ = v___y_4289_;
v___y_4252_ = v___y_4282_;
v___y_4253_ = v___y_4283_;
v___y_4254_ = v___y_4284_;
v___y_4255_ = v___y_4285_;
v___y_4256_ = v___y_4286_;
v___y_4257_ = v___y_4287_;
v___y_4258_ = v___y_4288_;
v___y_4259_ = v___x_4290_;
goto v___jp_4244_;
}
else
{
if (v___y_4277_ == 0)
{
v___y_4245_ = v___y_4276_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4278_;
v___y_4248_ = v___y_4279_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v___y_4281_;
v___y_4251_ = v___y_4289_;
v___y_4252_ = v___y_4282_;
v___y_4253_ = v___y_4283_;
v___y_4254_ = v___y_4284_;
v___y_4255_ = v___y_4285_;
v___y_4256_ = v___y_4286_;
v___y_4257_ = v___y_4287_;
v___y_4258_ = v___y_4288_;
v___y_4259_ = v___y_4277_;
goto v___jp_4244_;
}
else
{
lean_object* v_ref_4291_; uint8_t v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_ref_4291_ = lean_ctor_get(v___y_4285_, 5);
v___x_4292_ = 0;
v___x_4293_ = l_Lean_SourceInfo_fromRef(v_ref_4291_, v___x_4292_);
v___x_4294_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4295_ = l_Lean_Name_mkStr4(v___x_3940_, v___x_3941_, v___x_3942_, v___x_4294_);
v___x_4296_ = l_Lean_SourceInfo_fromRef(v_tk_3954_, v___x_3939_);
v___x_4297_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4300_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4293_);
v___x_4301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4293_);
lean_ctor_set(v___x_4301_, 1, v___x_4299_);
lean_ctor_set(v___x_4301_, 2, v___x_4300_);
if (lean_obj_tag(v___y_4288_) == 1)
{
lean_object* v_val_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_val_4302_ = lean_ctor_get(v___y_4288_, 0);
lean_inc(v_val_4302_);
lean_dec_ref(v___y_4288_);
v___x_4303_ = l_Lean_SourceInfo_fromRef(v_val_4302_, v___x_3939_);
lean_dec(v_val_4302_);
v___x_4304_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = l_Array_mkArray1___redArg(v___x_4305_);
v___y_4213_ = v___x_4293_;
v___y_4214_ = v___x_4300_;
v___y_4215_ = v___x_4295_;
v___y_4216_ = v___y_4276_;
v___y_4217_ = v___y_4277_;
v___y_4218_ = v___y_4278_;
v___y_4219_ = v___y_4279_;
v___y_4220_ = v___x_4298_;
v___y_4221_ = v___y_4280_;
v___y_4222_ = v___x_4299_;
v___y_4223_ = v___y_4281_;
v___y_4224_ = v___y_4289_;
v___y_4225_ = v___y_4282_;
v___y_4226_ = v___y_4283_;
v___y_4227_ = v___y_4284_;
v___y_4228_ = v___y_4285_;
v___y_4229_ = v___x_4301_;
v___y_4230_ = v___y_4286_;
v___y_4231_ = v___y_4287_;
v___y_4232_ = v___x_4306_;
goto v___jp_4212_;
}
else
{
lean_object* v___x_4307_; 
lean_dec(v___y_4288_);
v___x_4307_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4213_ = v___x_4293_;
v___y_4214_ = v___x_4300_;
v___y_4215_ = v___x_4295_;
v___y_4216_ = v___y_4276_;
v___y_4217_ = v___y_4277_;
v___y_4218_ = v___y_4278_;
v___y_4219_ = v___y_4279_;
v___y_4220_ = v___x_4298_;
v___y_4221_ = v___y_4280_;
v___y_4222_ = v___x_4299_;
v___y_4223_ = v___y_4281_;
v___y_4224_ = v___y_4289_;
v___y_4225_ = v___y_4282_;
v___y_4226_ = v___y_4283_;
v___y_4227_ = v___y_4284_;
v___y_4228_ = v___y_4285_;
v___y_4229_ = v___x_4301_;
v___y_4230_ = v___y_4286_;
v___y_4231_ = v___y_4287_;
v___y_4232_ = v___x_4307_;
goto v___jp_4212_;
}
}
}
}
v___jp_4308_:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4323_ = lean_unsigned_to_nat(3u);
v___x_4324_ = l_Lean_Syntax_getArg(v___y_4312_, v___x_4323_);
lean_dec(v___y_4312_);
v___x_4325_ = l_Lean_Syntax_getOptional_x3f(v___x_4324_);
lean_dec(v___x_4324_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_box(0);
v___y_4276_ = v___y_4316_;
v___y_4277_ = v___y_4311_;
v___y_4278_ = v___y_4317_;
v___y_4279_ = v___y_4320_;
v___y_4280_ = v___y_4318_;
v___y_4281_ = v___y_4309_;
v___y_4282_ = v___y_4310_;
v___y_4283_ = v___y_4315_;
v___y_4284_ = v___y_4322_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4319_;
v___y_4287_ = v_args_4314_;
v___y_4288_ = v___y_4313_;
v___y_4289_ = v___x_4326_;
goto v___jp_4275_;
}
else
{
lean_object* v_val_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
v_val_4327_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4325_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_val_4327_);
lean_dec(v___x_4325_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_val_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
v___y_4276_ = v___y_4316_;
v___y_4277_ = v___y_4311_;
v___y_4278_ = v___y_4317_;
v___y_4279_ = v___y_4320_;
v___y_4280_ = v___y_4318_;
v___y_4281_ = v___y_4309_;
v___y_4282_ = v___y_4310_;
v___y_4283_ = v___y_4315_;
v___y_4284_ = v___y_4322_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4319_;
v___y_4287_ = v_args_4314_;
v___y_4288_ = v___y_4313_;
v___y_4289_ = v___x_4332_;
goto v___jp_4275_;
}
}
}
}
v___jp_4336_:
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = l_Lean_Syntax_getArg(v___y_4341_, v___y_4337_);
v___x_4352_ = l_Lean_Syntax_isNone(v___x_4351_);
if (v___x_4352_ == 0)
{
uint8_t v___x_4353_; 
lean_inc(v___x_4351_);
v___x_4353_ = l_Lean_Syntax_matchesNull(v___x_4351_, v___x_4335_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
lean_dec(v___x_4351_);
lean_dec(v_o_4342_);
lean_dec(v___y_4341_);
lean_dec(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec(v_tk_3954_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_4354_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4354_;
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4355_ = l_Lean_Syntax_getArg(v___x_4351_, v___x_3953_);
lean_dec(v___x_4351_);
v___x_4356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3941_);
lean_inc_ref(v___x_3940_);
v___x_4357_ = l_Lean_Name_mkStr4(v___x_3940_, v___x_3941_, v___x_3942_, v___x_4356_);
lean_inc(v___x_4355_);
v___x_4358_ = l_Lean_Syntax_isOfKind(v___x_4355_, v___x_4357_);
lean_dec(v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; 
lean_dec(v___x_4355_);
lean_dec(v_o_4342_);
lean_dec(v___y_4341_);
lean_dec(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec(v_tk_3954_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_4359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4359_;
}
else
{
lean_object* v___x_4360_; lean_object* v_args_4361_; lean_object* v___x_4362_; 
v___x_4360_ = l_Lean_Syntax_getArg(v___x_4355_, v___x_4335_);
lean_dec(v___x_4355_);
v_args_4361_ = l_Lean_Syntax_getArgs(v___x_4360_);
lean_dec(v___x_4360_);
v___x_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_args_4361_);
v___y_4309_ = v___y_4338_;
v___y_4310_ = v___y_4339_;
v___y_4311_ = v___y_4340_;
v___y_4312_ = v___y_4341_;
v___y_4313_ = v_o_4342_;
v_args_4314_ = v___x_4362_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___y_4348_;
v___y_4321_ = v___y_4349_;
v___y_4322_ = v___y_4350_;
goto v___jp_4308_;
}
}
}
else
{
lean_object* v___x_4363_; 
lean_dec(v___x_4351_);
v___x_4363_ = lean_box(0);
v___y_4309_ = v___y_4338_;
v___y_4310_ = v___y_4339_;
v___y_4311_ = v___y_4340_;
v___y_4312_ = v___y_4341_;
v___y_4313_ = v_o_4342_;
v_args_4314_ = v___x_4363_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4345_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___y_4348_;
v___y_4321_ = v___y_4349_;
v___y_4322_ = v___y_4350_;
goto v___jp_4308_;
}
}
v___jp_4364_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4374_ = lean_unsigned_to_nat(2u);
v___x_4375_ = l_Lean_Syntax_getArg(v_stx_3938_, v___x_4374_);
v___x_4376_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3941_);
lean_inc_ref(v___x_3940_);
v___x_4377_ = l_Lean_Name_mkStr4(v___x_3940_, v___x_3941_, v___x_3942_, v___x_4376_);
lean_inc(v___x_4375_);
v___x_4378_ = l_Lean_Syntax_isOfKind(v___x_4375_, v___x_4377_);
lean_dec(v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; 
lean_dec(v___x_4375_);
lean_dec(v_bang_4365_);
lean_dec(v_tk_3954_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_4379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4379_;
}
else
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; 
v___x_4380_ = l_Lean_Syntax_getArg(v___x_4375_, v___x_3953_);
v___x_4381_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3941_);
lean_inc_ref(v___x_3940_);
v___x_4382_ = l_Lean_Name_mkStr4(v___x_3940_, v___x_3941_, v___x_3942_, v___x_4381_);
lean_inc(v___x_4380_);
v___x_4383_ = l_Lean_Syntax_isOfKind(v___x_4380_, v___x_4382_);
lean_dec(v___x_4382_);
if (v___x_4383_ == 0)
{
lean_object* v___x_4384_; 
lean_dec(v___x_4380_);
lean_dec(v___x_4375_);
lean_dec(v_bang_4365_);
lean_dec(v_tk_3954_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_4384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4384_;
}
else
{
lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4385_ = l_Lean_Syntax_getArg(v___x_4375_, v___x_4335_);
v___x_4386_ = l_Lean_Syntax_isNone(v___x_4385_);
if (v___x_4386_ == 0)
{
uint8_t v___x_4387_; 
lean_inc(v___x_4385_);
v___x_4387_ = l_Lean_Syntax_matchesNull(v___x_4385_, v___x_4335_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_dec(v___x_4385_);
lean_dec(v___x_4380_);
lean_dec(v___x_4375_);
lean_dec(v_bang_4365_);
lean_dec(v_tk_3954_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec_ref(v___x_3940_);
v___x_4388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4388_;
}
else
{
lean_object* v_o_4389_; lean_object* v___x_4390_; 
v_o_4389_ = l_Lean_Syntax_getArg(v___x_4385_, v___x_3953_);
lean_dec(v___x_4385_);
v___x_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4390_, 0, v_o_4389_);
v___y_4337_ = v___x_4374_;
v___y_4338_ = v___x_4380_;
v___y_4339_ = v_bang_4365_;
v___y_4340_ = v___x_4383_;
v___y_4341_ = v___x_4375_;
v_o_4342_ = v___x_4390_;
v___y_4343_ = v___y_4366_;
v___y_4344_ = v___y_4367_;
v___y_4345_ = v___y_4368_;
v___y_4346_ = v___y_4369_;
v___y_4347_ = v___y_4370_;
v___y_4348_ = v___y_4371_;
v___y_4349_ = v___y_4372_;
v___y_4350_ = v___y_4373_;
goto v___jp_4336_;
}
}
else
{
lean_object* v___x_4391_; 
lean_dec(v___x_4385_);
v___x_4391_ = lean_box(0);
v___y_4337_ = v___x_4374_;
v___y_4338_ = v___x_4380_;
v___y_4339_ = v_bang_4365_;
v___y_4340_ = v___x_4383_;
v___y_4341_ = v___x_4375_;
v_o_4342_ = v___x_4391_;
v___y_4343_ = v___y_4366_;
v___y_4344_ = v___y_4367_;
v___y_4345_ = v___y_4368_;
v___y_4346_ = v___y_4369_;
v___y_4347_ = v___y_4370_;
v___y_4348_ = v___y_4371_;
v___y_4349_ = v___y_4372_;
v___y_4350_ = v___y_4373_;
goto v___jp_4336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4399_, lean_object* v_stx_4400_, lean_object* v___x_4401_, lean_object* v___x_4402_, lean_object* v___x_4403_, lean_object* v___x_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v___x_10548__boxed_4414_; uint8_t v___x_10549__boxed_4415_; lean_object* v_res_4416_; 
v___x_10548__boxed_4414_ = lean_unbox(v___x_4399_);
v___x_10549__boxed_4415_ = lean_unbox(v___x_4401_);
v_res_4416_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_10548__boxed_4414_, v_stx_4400_, v___x_10549__boxed_4415_, v___x_4402_, v___x_4403_, v___x_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v_stx_4400_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; uint8_t v___x_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___y_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4436_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4423_);
v___x_4437_ = l_Lean_Syntax_isOfKind(v_stx_4423_, v___x_4436_);
v___x_4438_ = 1;
v___x_4439_ = lean_box(v___x_4437_);
v___x_4440_ = lean_box(v___x_4438_);
v___y_4441_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4441_, 0, v___x_4439_);
lean_closure_set(v___y_4441_, 1, v_stx_4423_);
lean_closure_set(v___y_4441_, 2, v___x_4440_);
lean_closure_set(v___y_4441_, 3, v___x_4433_);
lean_closure_set(v___y_4441_, 4, v___x_4434_);
lean_closure_set(v___y_4441_, 5, v___x_4435_);
v___x_4442_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4442_, 0, v___y_4441_);
v___x_4443_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4442_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4462_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4463_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4465_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4466_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4462_, v___x_4463_, v___x_4464_, v___x_4465_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4497_ = l_Lean_addBuiltinDeclarationRanges(v___x_4495_, v___x_4496_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4499_;
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
