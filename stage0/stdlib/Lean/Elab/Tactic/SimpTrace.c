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
uint8_t v___x_33437__boxed_208_; lean_object* v_res_209_; 
v___x_33437__boxed_208_ = lean_unbox(v___x_201_);
v_res_209_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(v___x_33437__boxed_208_, v_x_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
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
uint8_t v___x_33464__boxed_246_; lean_object* v_res_247_; 
v___x_33464__boxed_246_ = lean_unbox(v___x_233_);
v_res_247_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(v___y_231_, v___x_232_, v___x_33464__boxed_246_, v___y_234_, v_simprocs_235_, v_discharge_x3f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
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
uint8_t v_suppressElabErrors_boxed_381_; uint8_t v___y_33663__boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_suppressElabErrors_boxed_381_ = lean_unbox(v_suppressElabErrors_378_);
v___y_33663__boxed_382_ = lean_unbox(v___y_379_);
v_res_383_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_381_, v___y_33663__boxed_382_, v_x_380_);
lean_dec(v_x_380_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(lean_object* v_ref_386_, lean_object* v_msgData_387_, uint8_t v_severity_388_, uint8_t v_isSilent_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; uint8_t v___y_399_; lean_object* v___y_400_; uint8_t v___y_401_; lean_object* v___y_402_; lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v___y_405_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; uint8_t v___y_439_; lean_object* v___y_440_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; uint8_t v___y_463_; lean_object* v___y_464_; uint8_t v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; uint8_t v___y_477_; uint8_t v___y_478_; uint8_t v___y_479_; uint8_t v___x_484_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; uint8_t v___y_493_; uint8_t v___y_494_; uint8_t v___y_496_; uint8_t v___x_514_; 
v___x_484_ = 2;
v___x_514_ = l_Lean_instBEqMessageSeverity_beq(v_severity_388_, v___x_484_);
if (v___x_514_ == 0)
{
v___y_496_ = v___x_514_;
goto v___jp_495_;
}
else
{
uint8_t v___x_515_; 
lean_inc_ref(v_msgData_387_);
v___x_515_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_387_);
v___y_496_ = v___x_515_;
goto v___jp_495_;
}
v___jp_395_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_traceState_414_; lean_object* v_cache_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_currNamespace_403_);
lean_ctor_set(v___x_406_, 1, v_openDecls_404_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___y_398_);
lean_inc_ref(v___y_396_);
lean_inc_ref(v___y_397_);
v___x_408_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_408_, 0, v___y_397_);
lean_ctor_set(v___x_408_, 1, v___y_400_);
lean_ctor_set(v___x_408_, 2, v___y_402_);
lean_ctor_set(v___x_408_, 3, v___y_396_);
lean_ctor_set(v___x_408_, 4, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*5, v___y_401_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*5 + 1, v___y_399_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*5 + 2, v_isSilent_389_);
v___x_409_ = lean_st_ref_take(v___y_405_);
v_env_410_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_409_, 1);
v_ngen_412_ = lean_ctor_get(v___x_409_, 2);
v_auxDeclNGen_413_ = lean_ctor_get(v___x_409_, 3);
v_traceState_414_ = lean_ctor_get(v___x_409_, 4);
v_cache_415_ = lean_ctor_get(v___x_409_, 5);
v_messages_416_ = lean_ctor_get(v___x_409_, 6);
v_infoState_417_ = lean_ctor_get(v___x_409_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_409_, 8);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_429_ == 0)
{
v___x_420_ = v___x_409_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_ngen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_409_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_MessageLog_add(v___x_408_, v_messages_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 6, v___x_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_env_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_traceState_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_snapshotTasks_418_);
v___x_425_ = v_reuseFailAlloc_428_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_st_ref_put(v___y_405_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_422_);
return v___x_427_;
}
}
}
v___jp_430_:
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
if (v___y_439_ == 0)
{
lean_del_object(v___x_445_);
lean_dec_ref(v___y_431_);
v___y_396_ = v___x_450_;
v___y_397_ = v___y_434_;
v___y_398_ = v_a_443_;
v___y_399_ = v___y_436_;
v___y_400_ = v___x_447_;
v___y_401_ = v___y_437_;
v___y_402_ = v___x_449_;
v_currNamespace_403_ = v___y_432_;
v_openDecls_404_ = v___y_433_;
v___y_405_ = v___y_393_;
goto v___jp_395_;
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
v___y_396_ = v___x_450_;
v___y_397_ = v___y_434_;
v___y_398_ = v_a_443_;
v___y_399_ = v___y_436_;
v___y_400_ = v___x_447_;
v___y_401_ = v___y_437_;
v___y_402_ = v___x_449_;
v_currNamespace_403_ = v___y_432_;
v_openDecls_404_ = v___y_433_;
v___y_405_ = v___y_393_;
goto v___jp_395_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Syntax_getTailPos_x3f(v___y_464_, v___y_465_);
lean_dec(v___y_464_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_inc(v___y_467_);
v___y_431_ = v___y_459_;
v___y_432_ = v___y_458_;
v___y_433_ = v___y_460_;
v___y_434_ = v___y_461_;
v___y_435_ = v___y_462_;
v___y_436_ = v___y_463_;
v___y_437_ = v___y_465_;
v___y_438_ = v___y_467_;
v___y_439_ = v___y_466_;
v___y_440_ = v___y_467_;
goto v___jp_430_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v___y_431_ = v___y_459_;
v___y_432_ = v___y_458_;
v___y_433_ = v___y_460_;
v___y_434_ = v___y_461_;
v___y_435_ = v___y_462_;
v___y_436_ = v___y_463_;
v___y_437_ = v___y_465_;
v___y_438_ = v___y_467_;
v___y_439_ = v___y_466_;
v___y_440_ = v_val_469_;
goto v___jp_430_;
}
}
v___jp_470_:
{
lean_object* v_ref_480_; lean_object* v___x_481_; 
v_ref_480_ = l_Lean_replaceRef(v_ref_386_, v___y_476_);
v___x_481_ = l_Lean_Syntax_getPos_x3f(v_ref_480_, v___y_477_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___y_458_ = v___y_472_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_473_;
v___y_461_ = v___y_474_;
v___y_462_ = v___y_475_;
v___y_463_ = v___y_479_;
v___y_464_ = v_ref_480_;
v___y_465_ = v___y_477_;
v___y_466_ = v___y_478_;
v___y_467_ = v___x_482_;
goto v___jp_457_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_481_, 1);
v___y_458_ = v___y_472_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_473_;
v___y_461_ = v___y_474_;
v___y_462_ = v___y_475_;
v___y_463_ = v___y_479_;
v___y_464_ = v_ref_480_;
v___y_465_ = v___y_477_;
v___y_466_ = v___y_478_;
v___y_467_ = v_val_483_;
goto v___jp_457_;
}
}
v___jp_485_:
{
if (v___y_494_ == 0)
{
v___y_471_ = v___y_489_;
v___y_472_ = v___y_488_;
v___y_473_ = v___y_490_;
v___y_474_ = v___y_486_;
v___y_475_ = v___y_487_;
v___y_476_ = v___y_491_;
v___y_477_ = v___y_492_;
v___y_478_ = v___y_493_;
v___y_479_ = v_severity_388_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___y_489_;
v___y_472_ = v___y_488_;
v___y_473_ = v___y_490_;
v___y_474_ = v___y_486_;
v___y_475_ = v___y_487_;
v___y_476_ = v___y_491_;
v___y_477_ = v___y_492_;
v___y_478_ = v___y_493_;
v___y_479_ = v___x_484_;
goto v___jp_470_;
}
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
lean_object* v_toCold_497_; lean_object* v_ref_498_; uint8_t v_suppressElabErrors_499_; lean_object* v_fileName_500_; lean_object* v_fileMap_501_; lean_object* v_options_502_; lean_object* v_currNamespace_503_; lean_object* v_openDecls_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___f_507_; uint8_t v___x_508_; uint8_t v___x_509_; 
v_toCold_497_ = lean_ctor_get(v___y_392_, 0);
v_ref_498_ = lean_ctor_get(v___y_392_, 2);
v_suppressElabErrors_499_ = lean_ctor_get_uint8(v___y_392_, sizeof(void*)*3 + 1);
v_fileName_500_ = lean_ctor_get(v_toCold_497_, 0);
v_fileMap_501_ = lean_ctor_get(v_toCold_497_, 1);
v_options_502_ = lean_ctor_get(v_toCold_497_, 2);
v_currNamespace_503_ = lean_ctor_get(v_toCold_497_, 4);
v_openDecls_504_ = lean_ctor_get(v_toCold_497_, 5);
v___x_505_ = lean_box(v_suppressElabErrors_499_);
v___x_506_ = lean_box(v___y_496_);
v___f_507_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_507_, 0, v___x_505_);
lean_closure_set(v___f_507_, 1, v___x_506_);
v___x_508_ = 1;
v___x_509_ = l_Lean_instBEqMessageSeverity_beq(v_severity_388_, v___x_508_);
if (v___x_509_ == 0)
{
v___y_486_ = v_fileName_500_;
v___y_487_ = v_fileMap_501_;
v___y_488_ = v_currNamespace_503_;
v___y_489_ = v___f_507_;
v___y_490_ = v_openDecls_504_;
v___y_491_ = v_ref_498_;
v___y_492_ = v___y_496_;
v___y_493_ = v_suppressElabErrors_499_;
v___y_494_ = v___x_509_;
goto v___jp_485_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = l_Lean_warningAsError;
v___x_511_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_502_, v___x_510_);
v___y_486_ = v_fileName_500_;
v___y_487_ = v_fileMap_501_;
v___y_488_ = v_currNamespace_503_;
v___y_489_ = v___f_507_;
v___y_490_ = v_openDecls_504_;
v___y_491_ = v_ref_498_;
v___y_492_ = v___y_496_;
v___y_493_ = v_suppressElabErrors_499_;
v___y_494_ = v___x_511_;
goto v___jp_485_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v_msgData_387_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_ref_516_, lean_object* v_msgData_517_, lean_object* v_severity_518_, lean_object* v_isSilent_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_severity_boxed_525_; uint8_t v_isSilent_boxed_526_; lean_object* v_res_527_; 
v_severity_boxed_525_ = lean_unbox(v_severity_518_);
v_isSilent_boxed_526_ = lean_unbox(v_isSilent_519_);
v_res_527_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_516_, v_msgData_517_, v_severity_boxed_525_, v_isSilent_boxed_526_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v_ref_516_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(lean_object* v_msgData_528_, uint8_t v_severity_529_, uint8_t v_isSilent_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_540_; lean_object* v___x_541_; 
v_ref_540_ = lean_ctor_get(v___y_537_, 2);
v___x_541_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_540_, v_msgData_528_, v_severity_529_, v_isSilent_530_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(lean_object* v_msgData_542_, lean_object* v_severity_543_, lean_object* v_isSilent_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v_severity_boxed_554_; uint8_t v_isSilent_boxed_555_; lean_object* v_res_556_; 
v_severity_boxed_554_ = lean_unbox(v_severity_543_);
v_isSilent_boxed_555_ = lean_unbox(v_isSilent_544_);
v_res_556_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_542_, v_severity_boxed_554_, v_isSilent_boxed_555_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = 1;
v___x_568_ = 0;
v___x_569_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_557_, v___x_567_, v___x_568_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_569_;
}
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
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(lean_object* v_id_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
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
v_isExporting_610_ = lean_ctor_get_uint8(v_env_598_, sizeof(void*)*8);
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
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_id_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(lean_object* v_id_632_, uint8_t v_enableLog_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_toCold_644_; lean_object* v_env_645_; lean_object* v_options_646_; lean_object* v_currNamespace_647_; lean_object* v_openDecls_648_; lean_object* v_res_649_; lean_object* v___x_650_; 
v___x_643_ = lean_st_ref_get(v___y_641_);
v_toCold_644_ = lean_ctor_get(v___y_640_, 0);
v_env_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_env_645_);
lean_dec(v___x_643_);
v_options_646_ = lean_ctor_get(v_toCold_644_, 2);
v_currNamespace_647_ = lean_ctor_get(v_toCold_644_, 4);
v_openDecls_648_ = lean_ctor_get(v_toCold_644_, 5);
lean_inc(v_openDecls_648_);
lean_inc(v_currNamespace_647_);
v_res_649_ = l_Lean_ResolveName_resolveGlobalName(v_env_645_, v_options_646_, v_currNamespace_647_, v_openDecls_648_, v_id_632_);
v___x_650_ = lean_st_ref_get(v___y_641_);
if (v_enableLog_633_ == 0)
{
lean_object* v___x_651_; 
lean_dec(v___x_650_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v_res_649_);
return v___x_651_;
}
else
{
lean_object* v_env_652_; uint8_t v_isExporting_653_; 
v_env_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_env_652_);
lean_dec(v___x_650_);
v_isExporting_653_ = lean_ctor_get_uint8(v_env_652_, sizeof(void*)*8);
lean_dec_ref(v_env_652_);
if (v_isExporting_653_ == 0)
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_res_649_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_649_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; lean_object* v_fst_657_; lean_object* v___x_658_; 
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v___x_655_, 1);
v_fst_657_ = lean_ctor_get(v_val_656_, 0);
lean_inc(v_fst_657_);
lean_dec(v_val_656_);
v___x_658_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_657_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v___x_658_, 0);
lean_dec(v_unused_666_);
v___x_660_ = v___x_658_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_dec(v___x_658_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_res_649_);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_res_649_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_res_649_);
v_a_667_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_658_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_658_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v___x_675_; 
lean_dec(v___x_655_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v_res_649_);
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(lean_object* v_id_676_, lean_object* v_enableLog_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v_enableLog_boxed_687_; lean_object* v_res_688_; 
v_enableLog_boxed_687_ = lean_unbox(v_enableLog_677_);
v_res_688_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_676_, v_enableLog_boxed_687_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(lean_object* v_a_689_, lean_object* v_a_690_){
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
lean_object* v_head_692_; lean_object* v_tail_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_704_; 
v_head_692_ = lean_ctor_get(v_a_689_, 0);
v_tail_693_ = lean_ctor_get(v_a_689_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_704_ == 0)
{
v___x_695_ = v_a_689_;
v_isShared_696_ = v_isSharedCheck_704_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_tail_693_);
lean_inc(v_head_692_);
lean_dec(v_a_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_704_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_snd_697_; uint8_t v___x_698_; 
v_snd_697_ = lean_ctor_get(v_head_692_, 1);
v___x_698_ = l_List_isEmpty___redArg(v_snd_697_);
if (v___x_698_ == 0)
{
lean_del_object(v___x_695_);
lean_dec(v_head_692_);
v_a_689_ = v_tail_693_;
goto _start;
}
else
{
lean_object* v___x_701_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_a_690_);
v___x_701_ = v___x_695_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_head_692_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_a_690_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_a_689_ = v_tail_693_;
v_a_690_ = v___x_701_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
if (lean_obj_tag(v_a_705_) == 0)
{
lean_object* v___x_707_; 
v___x_707_ = l_List_reverse___redArg(v_a_706_);
return v___x_707_;
}
else
{
lean_object* v_head_708_; lean_object* v_tail_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
v_head_708_ = lean_ctor_get(v_a_705_, 0);
v_tail_709_ = lean_ctor_get(v_a_705_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v_a_705_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_tail_709_);
lean_inc(v_head_708_);
lean_dec(v_a_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_fst_713_; lean_object* v___x_715_; 
v_fst_713_ = lean_ctor_get(v_head_708_, 0);
lean_inc(v_fst_713_);
lean_dec(v_head_708_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v_a_706_);
lean_ctor_set(v___x_711_, 0, v_fst_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fst_713_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_a_706_);
v___x_715_ = v_reuseFailAlloc_717_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
v_a_705_ = v_tail_709_;
v_a_706_ = v___x_715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_ref_725_; lean_object* v___x_726_; lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_735_; 
v_ref_725_ = lean_ctor_get(v___y_722_, 2);
v___x_726_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_735_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_inc(v_ref_725_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_ref_725_);
lean_ctor_set(v___x_731_, 1, v_a_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(lean_object* v_ref_743_, lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_toCold_754_; lean_object* v_currRecDepth_755_; lean_object* v_ref_756_; uint8_t v_diag_757_; uint8_t v_suppressElabErrors_758_; lean_object* v_ref_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_toCold_754_ = lean_ctor_get(v___y_751_, 0);
v_currRecDepth_755_ = lean_ctor_get(v___y_751_, 1);
v_ref_756_ = lean_ctor_get(v___y_751_, 2);
v_diag_757_ = lean_ctor_get_uint8(v___y_751_, sizeof(void*)*3);
v_suppressElabErrors_758_ = lean_ctor_get_uint8(v___y_751_, sizeof(void*)*3 + 1);
v_ref_759_ = l_Lean_replaceRef(v_ref_743_, v_ref_756_);
lean_inc(v_currRecDepth_755_);
lean_inc_ref(v_toCold_754_);
v___x_760_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_760_, 0, v_toCold_754_);
lean_ctor_set(v___x_760_, 1, v_currRecDepth_755_);
lean_ctor_set(v___x_760_, 2, v_ref_759_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*3, v_diag_757_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*3 + 1, v_suppressElabErrors_758_);
v___x_761_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_744_, v___y_749_, v___y_750_, v___x_760_, v___y_752_);
lean_dec_ref_known(v___x_760_, 3);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_ref_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_762_, v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v_ref_762_);
return v_res_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
lean_ctor_set(v___x_779_, 3, v___x_778_);
lean_ctor_set(v___x_779_, 4, v___x_777_);
lean_ctor_set(v___x_779_, 5, v___x_777_);
lean_ctor_set(v___x_779_, 6, v___x_777_);
lean_ctor_set(v___x_779_, 7, v___x_777_);
lean_ctor_set(v___x_779_, 8, v___x_777_);
lean_ctor_set(v___x_779_, 9, v___x_777_);
lean_ctor_set(v___x_779_, 10, v___x_777_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_unsigned_to_nat(32u);
v___x_781_ = lean_mk_empty_array_with_capacity(v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4(void){
_start:
{
size_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_783_ = ((size_t)5ULL);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_unsigned_to_nat(32u);
v___x_786_ = lean_mk_empty_array_with_capacity(v___x_785_);
v___x_787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
v___x_788_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
lean_ctor_set(v___x_788_, 2, v___x_784_);
lean_ctor_set(v___x_788_, 3, v___x_784_);
lean_ctor_set_usize(v___x_788_, 4, v___x_783_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_box(1);
v___x_790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
v___x_791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_789_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(lean_object* v_msg_814_, lean_object* v_declHint_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_env_820_; uint8_t v___x_821_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_st_ref_get(v___y_816_);
v_env_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_env_820_);
lean_dec(v___x_819_);
v___x_821_ = l_Lean_Name_isAnonymous(v_declHint_815_);
if (v___x_821_ == 0)
{
uint8_t v_isExporting_822_; 
v_isExporting_822_ = lean_ctor_get_uint8(v_env_820_, sizeof(void*)*8);
if (v_isExporting_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v_msg_814_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
lean_inc_ref(v_env_820_);
v___x_824_ = l_Lean_Environment_setExporting(v_env_820_, v___x_821_);
lean_inc(v_declHint_815_);
lean_inc_ref(v___x_824_);
v___x_825_ = l_Lean_Environment_contains(v___x_824_, v_declHint_815_, v_isExporting_822_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v___x_824_);
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_msg_814_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_c_832_; lean_object* v___x_833_; 
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
v___x_828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
v___x_829_ = l_Lean_Options_empty;
v___x_830_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_830_, 0, v___x_824_);
lean_ctor_set(v___x_830_, 1, v___x_827_);
lean_ctor_set(v___x_830_, 2, v___x_828_);
lean_ctor_set(v___x_830_, 3, v___x_829_);
lean_inc(v_declHint_815_);
v___x_831_ = l_Lean_MessageData_ofConstName(v_declHint_815_, v___x_821_);
v_c_832_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_832_, 0, v___x_830_);
lean_ctor_set(v_c_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_820_, v_declHint_815_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_c_832_);
v___x_836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_MessageData_note(v___x_837_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v_msg_814_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_875_; 
v_val_841_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_875_ == 0)
{
v___x_843_ = v___x_833_;
v_isShared_844_ = v_isSharedCheck_875_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_val_841_);
lean_dec(v___x_833_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_875_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_mod_847_; uint8_t v___x_848_; 
v___x_845_ = l_Lean_Environment_header(v_env_820_);
lean_dec_ref(v_env_820_);
v___x_846_ = l_Lean_EnvironmentHeader_moduleNames(v___x_845_);
v_mod_847_ = lean_array_get(v___x_818_, v___x_846_, v_val_841_);
lean_dec(v_val_841_);
lean_dec_ref(v___x_846_);
v___x_848_ = l_Lean_isPrivateName(v_declHint_815_);
lean_dec(v_declHint_815_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v_c_832_);
v___x_851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_MessageData_ofName(v_mod_847_);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_MessageData_note(v___x_856_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v_msg_814_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_858_);
v___x_860_ = v___x_843_;
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
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v_c_832_);
v___x_864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_MessageData_ofName(v_mod_847_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_MessageData_note(v___x_869_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v_msg_814_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_871_);
v___x_873_ = v___x_843_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_876_; 
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_msg_814_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(lean_object* v_msg_877_, lean_object* v_declHint_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_877_, v_declHint_878_, v___y_879_);
lean_dec(v___y_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(lean_object* v_msg_882_, lean_object* v_declHint_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_903_; 
v___x_893_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_882_, v_declHint_883_, v___y_891_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_903_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_903_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_898_ = l_Lean_unknownIdentifierMessageTag;
v___x_899_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_a_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(lean_object* v_msg_904_, lean_object* v_declHint_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_904_, v_declHint_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(lean_object* v_ref_916_, lean_object* v_msg_917_, lean_object* v_declHint_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_930_; 
v___x_928_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_917_, v_declHint_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_916_, v_a_929_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(lean_object* v_ref_931_, lean_object* v_msg_932_, lean_object* v_declHint_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_931_, v_msg_932_, v_declHint_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v_ref_931_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(lean_object* v_ref_950_, lean_object* v_constName_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_961_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
v___x_962_ = 0;
lean_inc(v_constName_951_);
v___x_963_ = l_Lean_MessageData_ofConstName(v_constName_951_, v___x_962_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_961_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_950_, v___x_966_, v_constName_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_ref_968_, lean_object* v_constName_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_968_, v_constName_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_ref_968_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(lean_object* v_n_980_, lean_object* v_cs_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; lean_object* v_cs_992_; uint8_t v___x_996_; 
v___x_991_ = lean_box(0);
v_cs_992_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_981_, v___x_991_);
v___x_996_ = l_List_isEmpty___redArg(v_cs_992_);
if (v___x_996_ == 0)
{
lean_dec(v_n_980_);
goto v___jp_993_;
}
else
{
lean_object* v_ref_997_; lean_object* v___x_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_cs_992_);
v_ref_997_ = lean_ctor_get(v___y_988_, 2);
v___x_998_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_997_, v_n_980_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
v___jp_993_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_992_, v___x_991_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(lean_object* v_n_1007_, lean_object* v_cs_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1007_, v_cs_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(lean_object* v_n_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
uint8_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = 1;
lean_inc(v_n_1019_);
v___x_1030_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_1019_, v___x_1029_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_1019_, v_a_1031_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1032_;
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_n_1019_);
v_a_1033_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1030_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1030_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(lean_object* v_n_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
if (lean_obj_tag(v_a_1052_) == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_array_to_list(v_a_1053_);
return v___x_1054_;
}
else
{
lean_object* v_head_1055_; 
v_head_1055_ = lean_ctor_get(v_a_1052_, 0);
if (lean_obj_tag(v_head_1055_) == 1)
{
lean_object* v_fields_1056_; 
v_fields_1056_ = lean_ctor_get(v_head_1055_, 1);
if (lean_obj_tag(v_fields_1056_) == 0)
{
lean_object* v_tail_1057_; lean_object* v_n_1058_; lean_object* v___x_1059_; 
lean_inc_ref(v_head_1055_);
v_tail_1057_ = lean_ctor_get(v_a_1052_, 1);
lean_inc(v_tail_1057_);
lean_dec_ref_known(v_a_1052_, 2);
v_n_1058_ = lean_ctor_get(v_head_1055_, 0);
lean_inc(v_n_1058_);
lean_dec_ref_known(v_head_1055_, 2);
v___x_1059_ = lean_array_push(v_a_1053_, v_n_1058_);
v_a_1052_ = v_tail_1057_;
v_a_1053_ = v___x_1059_;
goto _start;
}
else
{
lean_object* v_tail_1061_; 
v_tail_1061_ = lean_ctor_get(v_a_1052_, 1);
lean_inc(v_tail_1061_);
lean_dec_ref_known(v_a_1052_, 2);
v_a_1052_ = v_tail_1061_;
goto _start;
}
}
else
{
lean_object* v_tail_1063_; 
v_tail_1063_ = lean_ctor_get(v_a_1052_, 1);
lean_inc(v_tail_1063_);
lean_dec_ref_known(v_a_1052_, 2);
v_a_1052_ = v_tail_1063_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2));
v___x_1071_ = l_Lean_MessageData_ofFormat(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(lean_object* v_stx_1072_, lean_object* v_k_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
if (lean_obj_tag(v_stx_1072_) == 3)
{
lean_object* v_val_1083_; lean_object* v_preresolved_1084_; lean_object* v___x_1085_; lean_object* v_pre_1086_; uint8_t v___x_1087_; 
v_val_1083_ = lean_ctor_get(v_stx_1072_, 2);
lean_inc(v_val_1083_);
v_preresolved_1084_ = lean_ctor_get(v_stx_1072_, 3);
v___x_1085_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0));
lean_inc(v_preresolved_1084_);
v_pre_1086_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_1084_, v___x_1085_);
v___x_1087_ = l_List_isEmpty___redArg(v_pre_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec_ref_known(v_stx_1072_, 4);
lean_dec(v_val_1083_);
lean_dec_ref(v_k_1073_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_pre_1086_);
return v___x_1088_;
}
else
{
lean_object* v_toCold_1089_; lean_object* v_currRecDepth_1090_; lean_object* v_ref_1091_; uint8_t v_diag_1092_; uint8_t v_suppressElabErrors_1093_; lean_object* v_ref_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_pre_1086_);
v_toCold_1089_ = lean_ctor_get(v___y_1080_, 0);
v_currRecDepth_1090_ = lean_ctor_get(v___y_1080_, 1);
v_ref_1091_ = lean_ctor_get(v___y_1080_, 2);
v_diag_1092_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*3);
v_suppressElabErrors_1093_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*3 + 1);
v_ref_1094_ = l_Lean_replaceRef(v_stx_1072_, v_ref_1091_);
lean_dec_ref_known(v_stx_1072_, 4);
lean_inc(v_currRecDepth_1090_);
lean_inc_ref(v_toCold_1089_);
v___x_1095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1095_, 0, v_toCold_1089_);
lean_ctor_set(v___x_1095_, 1, v_currRecDepth_1090_);
lean_ctor_set(v___x_1095_, 2, v_ref_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3, v_diag_1092_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 1, v_suppressElabErrors_1093_);
lean_inc(v___y_1081_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1096_ = lean_apply_10(v_k_1073_, v_val_1083_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___x_1095_, v___y_1081_, lean_box(0));
return v___x_1096_;
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_k_1073_);
v___x_1097_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
v___x_1098_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_1072_, v___x_1097_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v_stx_1072_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(lean_object* v_stx_1099_, lean_object* v_k_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1099_, v_k_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(lean_object* v_stx_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0));
v___x_1123_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_1112_, v___x_1122_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(lean_object* v_stx_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v_stx_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_b_1138_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v_name_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1150_ = lean_array_uget_borrowed(v_as_1135_, v_i_1137_);
v_name_1151_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_name_1151_);
v___x_1152_ = l_Lean_mkIdent(v_name_1151_);
lean_inc(v___x_1152_);
v___x_1153_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_1152_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v___x_1155_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_1152_, v_a_1154_, v_b_1138_, v___y_1145_);
lean_dec(v_a_1154_);
lean_dec(v___x_1152_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; size_t v___x_1157_; size_t v___x_1158_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_add(v_i_1137_, v___x_1157_);
v_i_1137_ = v___x_1158_;
v_b_1138_ = v_a_1156_;
goto _start;
}
else
{
return v___x_1155_;
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v___x_1152_);
lean_dec_ref(v_b_1138_);
v_a_1160_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1153_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1153_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(lean_object* v_as_1168_, lean_object* v_sz_1169_, lean_object* v_i_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
size_t v_sz_boxed_1181_; size_t v_i_boxed_1182_; lean_object* v_res_1183_; 
v_sz_boxed_1181_ = lean_unbox_usize(v_sz_1169_);
lean_dec(v_sz_1169_);
v_i_boxed_1182_ = lean_unbox_usize(v_i_1170_);
lean_dec(v_i_1170_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_1168_, v_sz_boxed_1181_, v_i_boxed_1182_, v_b_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec_ref(v_as_1168_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t v___x_1203_, lean_object* v_stx_1204_, uint8_t v___x_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v___f_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
if (v___x_1203_ == 0)
{
lean_object* v___x_1219_; 
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_1219_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v_tk_1221_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; uint8_t v___y_1297_; lean_object* v_stxForSuggestion_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; uint8_t v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; uint8_t v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; uint8_t v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; uint8_t v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; uint8_t v___y_1541_; uint8_t v___y_1542_; lean_object* v___y_1555_; lean_object* v___y_1556_; uint8_t v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; uint8_t v___y_1563_; lean_object* v_stxForExecution_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; uint8_t v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; uint8_t v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; uint8_t v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; uint8_t v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; uint8_t v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; uint8_t v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; uint8_t v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; uint8_t v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; uint8_t v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v_argsArray_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; uint8_t v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; uint8_t v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; uint8_t v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; uint8_t v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v_args_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___x_2019_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v_o_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v_bang_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v_tk_1221_ = l_Lean_Syntax_getArg(v_stx_1204_, v___x_1220_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2078_ = l_Lean_Syntax_getArg(v_stx_1204_, v___x_2019_);
v___x_2079_ = l_Lean_Syntax_isNone(v___x_2078_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; 
lean_inc(v___x_2078_);
v___x_2080_ = l_Lean_Syntax_matchesNull(v___x_2078_, v___x_2019_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v___x_2078_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_2081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2081_;
}
else
{
lean_object* v_bang_2082_; lean_object* v___x_2083_; 
v_bang_2082_ = l_Lean_Syntax_getArg(v___x_2078_, v___x_1220_);
lean_dec(v___x_2078_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_bang_2082_);
v_bang_2050_ = v___x_2083_;
v___y_2051_ = v___y_1210_;
v___y_2052_ = v___y_1211_;
v___y_2053_ = v___y_1212_;
v___y_2054_ = v___y_1213_;
v___y_2055_ = v___y_1214_;
v___y_2056_ = v___y_1215_;
v___y_2057_ = v___y_1216_;
v___y_2058_ = v___y_1217_;
goto v___jp_2049_;
}
}
else
{
lean_object* v___x_2084_; 
lean_dec(v___x_2078_);
v___x_2084_ = lean_box(0);
v_bang_2050_ = v___x_2084_;
v___y_2051_ = v___y_1210_;
v___y_2052_ = v___y_1211_;
v___y_2053_ = v___y_1212_;
v___y_2054_ = v___y_1213_;
v___y_2055_ = v___y_1214_;
v___y_2056_ = v___y_1215_;
v___y_2057_ = v___y_1216_;
v___y_2058_ = v___y_1217_;
goto v___jp_2049_;
}
v___jp_1222_:
{
lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_box(v___x_1205_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(v___f_1237_, 0, v___y_1224_);
lean_closure_set(v___f_1237_, 1, v___x_1220_);
lean_closure_set(v___f_1237_, 2, v___x_1236_);
lean_closure_set(v___f_1237_, 3, v___y_1235_);
lean_closure_set(v___f_1237_, 4, v___y_1225_);
v___x_1238_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_1223_, v___f_1237_, v___y_1229_, v___y_1228_, v___y_1233_, v___y_1234_, v___y_1230_, v___y_1231_, v___y_1227_, v___y_1232_);
lean_dec(v___y_1223_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_usedTheorems_1240_; lean_object* v_diag_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1283_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v_usedTheorems_1240_ = lean_ctor_get(v_a_1239_, 0);
v_diag_1241_ = lean_ctor_get(v_a_1239_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1239_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1243_ = v_a_1239_;
v_isShared_1244_ = v_isSharedCheck_1283_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_diag_1241_);
lean_inc(v_usedTheorems_1240_);
lean_dec(v_a_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1283_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_1226_, v_usedTheorems_1240_, v___y_1230_, v___y_1231_, v___y_1227_, v___y_1232_);
lean_dec_ref(v_usedTheorems_1240_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_ref_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v_ref_1247_ = lean_ctor_get(v___y_1227_, 2);
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v_a_1246_);
lean_ctor_set(v___x_1243_, 0, v___x_1248_);
v___x_1250_ = v___x_1243_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_a_1246_);
v___x_1250_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
lean_ctor_set(v___x_1252_, 2, v___x_1251_);
lean_ctor_set(v___x_1252_, 3, v___x_1251_);
lean_ctor_set(v___x_1252_, 4, v___x_1251_);
lean_ctor_set(v___x_1252_, 5, v___x_1251_);
lean_inc(v_ref_1247_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_ref_1247_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_1255_ = 4;
v___x_1256_ = l_Lean_MessageData_nil;
v___x_1257_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1221_, v___x_1252_, v___x_1253_, v___x_1254_, v___x_1251_, v___x_1255_, v___x_1256_, v___y_1227_, v___y_1232_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1265_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v_diag_1241_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_diag_1241_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_diag_1241_);
v_a_1266_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_del_object(v___x_1243_);
lean_dec_ref(v_diag_1241_);
lean_dec(v_tk_1221_);
v_a_1275_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1245_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1245_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v___y_1226_);
lean_dec(v_tk_1221_);
v_a_1284_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1238_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1238_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
v___jp_1292_:
{
uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = 0;
v___x_1308_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_1309_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_1295_, v___x_1307_, v___y_1297_, v___x_1307_, v___x_1308_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1295_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
if (lean_obj_tag(v___y_1296_) == 0)
{
lean_object* v_ctx_1311_; lean_object* v_simprocs_1312_; lean_object* v_dischargeWrapper_1313_; 
v_ctx_1311_ = lean_ctor_get(v_a_1310_, 0);
lean_inc_ref(v_ctx_1311_);
v_simprocs_1312_ = lean_ctor_get(v_a_1310_, 1);
lean_inc_ref(v_simprocs_1312_);
v_dischargeWrapper_1313_ = lean_ctor_get(v_a_1310_, 2);
lean_inc(v_dischargeWrapper_1313_);
lean_dec(v_a_1310_);
v___y_1223_ = v_dischargeWrapper_1313_;
v___y_1224_ = v___y_1293_;
v___y_1225_ = v_simprocs_1312_;
v___y_1226_ = v_stxForSuggestion_1298_;
v___y_1227_ = v___y_1305_;
v___y_1228_ = v___y_1300_;
v___y_1229_ = v___y_1299_;
v___y_1230_ = v___y_1303_;
v___y_1231_ = v___y_1304_;
v___y_1232_ = v___y_1306_;
v___y_1233_ = v___y_1301_;
v___y_1234_ = v___y_1302_;
v___y_1235_ = v_ctx_1311_;
goto v___jp_1222_;
}
else
{
lean_dec_ref_known(v___y_1296_, 1);
if (v___y_1294_ == 0)
{
lean_object* v_ctx_1314_; lean_object* v_simprocs_1315_; lean_object* v_dischargeWrapper_1316_; 
v_ctx_1314_ = lean_ctor_get(v_a_1310_, 0);
lean_inc_ref(v_ctx_1314_);
v_simprocs_1315_ = lean_ctor_get(v_a_1310_, 1);
lean_inc_ref(v_simprocs_1315_);
v_dischargeWrapper_1316_ = lean_ctor_get(v_a_1310_, 2);
lean_inc(v_dischargeWrapper_1316_);
lean_dec(v_a_1310_);
v___y_1223_ = v_dischargeWrapper_1316_;
v___y_1224_ = v___y_1293_;
v___y_1225_ = v_simprocs_1315_;
v___y_1226_ = v_stxForSuggestion_1298_;
v___y_1227_ = v___y_1305_;
v___y_1228_ = v___y_1300_;
v___y_1229_ = v___y_1299_;
v___y_1230_ = v___y_1303_;
v___y_1231_ = v___y_1304_;
v___y_1232_ = v___y_1306_;
v___y_1233_ = v___y_1301_;
v___y_1234_ = v___y_1302_;
v___y_1235_ = v_ctx_1314_;
goto v___jp_1222_;
}
else
{
lean_object* v_ctx_1317_; lean_object* v_simprocs_1318_; lean_object* v_dischargeWrapper_1319_; lean_object* v___x_1320_; 
v_ctx_1317_ = lean_ctor_get(v_a_1310_, 0);
lean_inc_ref(v_ctx_1317_);
v_simprocs_1318_ = lean_ctor_get(v_a_1310_, 1);
lean_inc_ref(v_simprocs_1318_);
v_dischargeWrapper_1319_ = lean_ctor_get(v_a_1310_, 2);
lean_inc(v_dischargeWrapper_1319_);
lean_dec(v_a_1310_);
v___x_1320_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_1317_);
v___y_1223_ = v_dischargeWrapper_1319_;
v___y_1224_ = v___y_1293_;
v___y_1225_ = v_simprocs_1318_;
v___y_1226_ = v_stxForSuggestion_1298_;
v___y_1227_ = v___y_1305_;
v___y_1228_ = v___y_1300_;
v___y_1229_ = v___y_1299_;
v___y_1230_ = v___y_1303_;
v___y_1231_ = v___y_1304_;
v___y_1232_ = v___y_1306_;
v___y_1233_ = v___y_1301_;
v___y_1234_ = v___y_1302_;
v___y_1235_ = v___x_1320_;
goto v___jp_1222_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_stxForSuggestion_1298_);
lean_dec(v___y_1296_);
lean_dec(v___y_1293_);
lean_dec(v_tk_1221_);
v_a_1321_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1309_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1309_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
v___jp_1329_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_inc_ref(v___y_1331_);
v___x_1353_ = l_Array_append___redArg(v___y_1331_, v___y_1352_);
lean_dec_ref(v___y_1352_);
lean_inc(v___y_1336_);
lean_inc(v___y_1351_);
v___x_1354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1354_, 0, v___y_1351_);
lean_ctor_set(v___x_1354_, 1, v___y_1336_);
lean_ctor_set(v___x_1354_, 2, v___x_1353_);
v___x_1355_ = l_Lean_Syntax_node6(v___y_1351_, v___y_1340_, v___y_1339_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___x_1354_);
v___y_1293_ = v___y_1330_;
v___y_1294_ = v___y_1343_;
v___y_1295_ = v___y_1342_;
v___y_1296_ = v___y_1348_;
v___y_1297_ = v___y_1350_;
v_stxForSuggestion_1298_ = v___x_1355_;
v___y_1299_ = v___y_1347_;
v___y_1300_ = v___y_1345_;
v___y_1301_ = v___y_1341_;
v___y_1302_ = v___y_1346_;
v___y_1303_ = v___y_1349_;
v___y_1304_ = v___y_1344_;
v___y_1305_ = v___y_1337_;
v___y_1306_ = v___y_1338_;
goto v___jp_1292_;
}
v___jp_1356_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc_ref_n(v___y_1358_, 2);
v___x_1380_ = l_Array_append___redArg(v___y_1358_, v___y_1379_);
lean_dec_ref(v___y_1379_);
lean_inc_n(v___y_1362_, 3);
lean_inc_n(v___y_1378_, 5);
v___x_1381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1378_);
lean_ctor_set(v___x_1381_, 1, v___y_1362_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1378_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1385_ = l_Lean_Syntax_SepArray_ofElems(v___x_1384_, v___y_1374_);
lean_dec_ref(v___y_1374_);
v___x_1386_ = l_Array_append___redArg(v___y_1358_, v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1378_);
lean_ctor_set(v___x_1387_, 1, v___y_1362_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1378_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = l_Lean_Syntax_node3(v___y_1378_, v___y_1362_, v___x_1383_, v___x_1387_, v___x_1389_);
if (lean_obj_tag(v___y_1361_) == 1)
{
lean_object* v_val_1391_; lean_object* v___x_1392_; 
v_val_1391_ = lean_ctor_get(v___y_1361_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___y_1361_, 1);
v___x_1392_ = l_Array_mkArray1___redArg(v_val_1391_);
v___y_1330_ = v___y_1357_;
v___y_1331_ = v___y_1358_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___x_1381_;
v___y_1335_ = v___x_1390_;
v___y_1336_ = v___y_1362_;
v___y_1337_ = v___y_1363_;
v___y_1338_ = v___y_1364_;
v___y_1339_ = v___y_1365_;
v___y_1340_ = v___y_1366_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___y_1368_;
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1371_;
v___y_1347_ = v___y_1373_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1375_;
v___y_1350_ = v___y_1377_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___x_1392_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1393_; 
lean_dec(v___y_1361_);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1330_ = v___y_1357_;
v___y_1331_ = v___y_1358_;
v___y_1332_ = v___y_1359_;
v___y_1333_ = v___y_1360_;
v___y_1334_ = v___x_1381_;
v___y_1335_ = v___x_1390_;
v___y_1336_ = v___y_1362_;
v___y_1337_ = v___y_1363_;
v___y_1338_ = v___y_1364_;
v___y_1339_ = v___y_1365_;
v___y_1340_ = v___y_1366_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v___y_1370_;
v___y_1344_ = v___y_1368_;
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1371_;
v___y_1347_ = v___y_1373_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1375_;
v___y_1350_ = v___y_1377_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___x_1393_;
goto v___jp_1329_;
}
}
v___jp_1394_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_inc_ref(v___y_1396_);
v___x_1418_ = l_Array_append___redArg(v___y_1396_, v___y_1417_);
lean_dec_ref(v___y_1417_);
lean_inc(v___y_1399_);
lean_inc(v___y_1416_);
v___x_1419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1419_, 0, v___y_1416_);
lean_ctor_set(v___x_1419_, 1, v___y_1399_);
lean_ctor_set(v___x_1419_, 2, v___x_1418_);
if (lean_obj_tag(v___y_1403_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_val_1420_ = lean_ctor_get(v___y_1403_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v___y_1403_, 1);
v___x_1421_ = l_Lean_SourceInfo_fromRef(v_val_1420_, v___x_1205_);
lean_dec(v_val_1420_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Array_mkArray1___redArg(v___x_1423_);
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1396_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___x_1419_;
v___y_1361_ = v___y_1398_;
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1401_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1409_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1413_;
v___y_1377_ = v___y_1415_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___x_1424_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v___y_1403_);
v___x_1425_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1357_ = v___y_1395_;
v___y_1358_ = v___y_1396_;
v___y_1359_ = v___y_1397_;
v___y_1360_ = v___x_1419_;
v___y_1361_ = v___y_1398_;
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1400_;
v___y_1364_ = v___y_1401_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___y_1404_;
v___y_1367_ = v___y_1405_;
v___y_1368_ = v___y_1406_;
v___y_1369_ = v___y_1407_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1409_;
v___y_1373_ = v___y_1411_;
v___y_1374_ = v___y_1412_;
v___y_1375_ = v___y_1414_;
v___y_1376_ = v___y_1413_;
v___y_1377_ = v___y_1415_;
v___y_1378_ = v___y_1416_;
v___y_1379_ = v___x_1425_;
goto v___jp_1356_;
}
}
v___jp_1426_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_inc_ref(v___y_1448_);
v___x_1450_ = l_Array_append___redArg(v___y_1448_, v___y_1449_);
lean_dec_ref(v___y_1449_);
lean_inc(v___y_1433_);
lean_inc(v___y_1441_);
v___x_1451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1441_);
lean_ctor_set(v___x_1451_, 1, v___y_1433_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
v___x_1452_ = l_Lean_Syntax_node6(v___y_1441_, v___y_1438_, v___y_1434_, v___y_1428_, v___y_1444_, v___y_1442_, v___y_1431_, v___x_1451_);
v___y_1293_ = v___y_1427_;
v___y_1294_ = v___y_1436_;
v___y_1295_ = v___y_1435_;
v___y_1296_ = v___y_1445_;
v___y_1297_ = v___y_1447_;
v_stxForSuggestion_1298_ = v___x_1452_;
v___y_1299_ = v___y_1443_;
v___y_1300_ = v___y_1439_;
v___y_1301_ = v___y_1432_;
v___y_1302_ = v___y_1440_;
v___y_1303_ = v___y_1446_;
v___y_1304_ = v___y_1437_;
v___y_1305_ = v___y_1429_;
v___y_1306_ = v___y_1430_;
goto v___jp_1292_;
}
v___jp_1453_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_inc_ref_n(v___y_1475_, 2);
v___x_1477_ = l_Array_append___redArg(v___y_1475_, v___y_1476_);
lean_dec_ref(v___y_1476_);
lean_inc_n(v___y_1460_, 3);
lean_inc_n(v___y_1469_, 5);
v___x_1478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1469_);
lean_ctor_set(v___x_1478_, 1, v___y_1460_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___y_1469_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1482_ = l_Lean_Syntax_SepArray_ofElems(v___x_1481_, v___y_1470_);
lean_dec_ref(v___y_1470_);
v___x_1483_ = l_Array_append___redArg(v___y_1475_, v___x_1482_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1469_);
lean_ctor_set(v___x_1484_, 1, v___y_1460_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
v___x_1485_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1469_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node3(v___y_1469_, v___y_1460_, v___x_1480_, v___x_1484_, v___x_1486_);
if (lean_obj_tag(v___y_1456_) == 1)
{
lean_object* v_val_1488_; lean_object* v___x_1489_; 
v_val_1488_ = lean_ctor_get(v___y_1456_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___y_1456_, 1);
v___x_1489_ = l_Array_mkArray1___redArg(v_val_1488_);
v___y_1427_ = v___y_1454_;
v___y_1428_ = v___y_1455_;
v___y_1429_ = v___y_1457_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___x_1487_;
v___y_1432_ = v___y_1459_;
v___y_1433_ = v___y_1460_;
v___y_1434_ = v___y_1461_;
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___y_1463_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1467_;
v___y_1440_ = v___y_1466_;
v___y_1441_ = v___y_1469_;
v___y_1442_ = v___x_1478_;
v___y_1443_ = v___y_1468_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___y_1474_;
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___x_1489_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___y_1456_);
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1427_ = v___y_1454_;
v___y_1428_ = v___y_1455_;
v___y_1429_ = v___y_1457_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___x_1487_;
v___y_1432_ = v___y_1459_;
v___y_1433_ = v___y_1460_;
v___y_1434_ = v___y_1461_;
v___y_1435_ = v___y_1462_;
v___y_1436_ = v___y_1463_;
v___y_1437_ = v___y_1464_;
v___y_1438_ = v___y_1465_;
v___y_1439_ = v___y_1467_;
v___y_1440_ = v___y_1466_;
v___y_1441_ = v___y_1469_;
v___y_1442_ = v___x_1478_;
v___y_1443_ = v___y_1468_;
v___y_1444_ = v___y_1471_;
v___y_1445_ = v___y_1473_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___y_1474_;
v___y_1448_ = v___y_1475_;
v___y_1449_ = v___x_1490_;
goto v___jp_1426_;
}
}
v___jp_1491_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc_ref(v___y_1513_);
v___x_1515_ = l_Array_append___redArg(v___y_1513_, v___y_1514_);
lean_dec_ref(v___y_1514_);
lean_inc(v___y_1499_);
lean_inc(v___y_1508_);
v___x_1516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1508_);
lean_ctor_set(v___x_1516_, 1, v___y_1499_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
if (lean_obj_tag(v___y_1497_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_val_1517_ = lean_ctor_get(v___y_1497_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___y_1497_, 1);
v___x_1518_ = l_Lean_SourceInfo_fromRef(v_val_1517_, v___x_1205_);
lean_dec(v_val_1517_);
v___x_1519_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Array_mkArray1___redArg(v___x_1520_);
v___y_1454_ = v___y_1492_;
v___y_1455_ = v___y_1493_;
v___y_1456_ = v___y_1494_;
v___y_1457_ = v___y_1495_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___y_1498_;
v___y_1460_ = v___y_1499_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1501_;
v___y_1463_ = v___y_1502_;
v___y_1464_ = v___y_1503_;
v___y_1465_ = v___y_1504_;
v___y_1466_ = v___y_1506_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___y_1508_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___x_1516_;
v___y_1472_ = v___y_1511_;
v___y_1473_ = v___y_1510_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___x_1521_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v___y_1497_);
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1454_ = v___y_1492_;
v___y_1455_ = v___y_1493_;
v___y_1456_ = v___y_1494_;
v___y_1457_ = v___y_1495_;
v___y_1458_ = v___y_1496_;
v___y_1459_ = v___y_1498_;
v___y_1460_ = v___y_1499_;
v___y_1461_ = v___y_1500_;
v___y_1462_ = v___y_1501_;
v___y_1463_ = v___y_1502_;
v___y_1464_ = v___y_1503_;
v___y_1465_ = v___y_1504_;
v___y_1466_ = v___y_1506_;
v___y_1467_ = v___y_1505_;
v___y_1468_ = v___y_1507_;
v___y_1469_ = v___y_1508_;
v___y_1470_ = v___y_1509_;
v___y_1471_ = v___x_1516_;
v___y_1472_ = v___y_1511_;
v___y_1473_ = v___y_1510_;
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___x_1522_;
goto v___jp_1453_;
}
}
v___jp_1523_:
{
lean_object* v_ref_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_ref_1543_ = lean_ctor_get(v___y_1528_, 2);
v___x_1544_ = l_Lean_SourceInfo_fromRef(v_ref_1543_, v___y_1542_);
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
v___x_1546_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_1545_);
v___x_1547_ = l_Lean_SourceInfo_fromRef(v_tk_1221_, v___x_1205_);
v___x_1548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___x_1545_);
v___x_1549_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1550_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1526_) == 1)
{
lean_object* v_val_1551_; lean_object* v___x_1552_; 
v_val_1551_ = lean_ctor_get(v___y_1526_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v___y_1526_, 1);
v___x_1552_ = l_Array_mkArray1___redArg(v_val_1551_);
v___y_1492_ = v___y_1524_;
v___y_1493_ = v___y_1525_;
v___y_1494_ = v___y_1527_;
v___y_1495_ = v___y_1528_;
v___y_1496_ = v___y_1529_;
v___y_1497_ = v___y_1530_;
v___y_1498_ = v___y_1531_;
v___y_1499_ = v___x_1549_;
v___y_1500_ = v___x_1548_;
v___y_1501_ = v___y_1532_;
v___y_1502_ = v___y_1533_;
v___y_1503_ = v___y_1534_;
v___y_1504_ = v___x_1546_;
v___y_1505_ = v___y_1535_;
v___y_1506_ = v___y_1536_;
v___y_1507_ = v___y_1537_;
v___y_1508_ = v___x_1544_;
v___y_1509_ = v___y_1538_;
v___y_1510_ = v___y_1540_;
v___y_1511_ = v___y_1539_;
v___y_1512_ = v___y_1541_;
v___y_1513_ = v___x_1550_;
v___y_1514_ = v___x_1552_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1553_; 
lean_dec(v___y_1526_);
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1492_ = v___y_1524_;
v___y_1493_ = v___y_1525_;
v___y_1494_ = v___y_1527_;
v___y_1495_ = v___y_1528_;
v___y_1496_ = v___y_1529_;
v___y_1497_ = v___y_1530_;
v___y_1498_ = v___y_1531_;
v___y_1499_ = v___x_1549_;
v___y_1500_ = v___x_1548_;
v___y_1501_ = v___y_1532_;
v___y_1502_ = v___y_1533_;
v___y_1503_ = v___y_1534_;
v___y_1504_ = v___x_1546_;
v___y_1505_ = v___y_1535_;
v___y_1506_ = v___y_1536_;
v___y_1507_ = v___y_1537_;
v___y_1508_ = v___x_1544_;
v___y_1509_ = v___y_1538_;
v___y_1510_ = v___y_1540_;
v___y_1511_ = v___y_1539_;
v___y_1512_ = v___y_1541_;
v___y_1513_ = v___x_1550_;
v___y_1514_ = v___x_1553_;
goto v___jp_1491_;
}
}
v___jp_1554_:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_1556_);
if (lean_obj_tag(v___y_1562_) == 0)
{
lean_object* v_a_1574_; uint8_t v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = 0;
v___y_1524_ = v___y_1555_;
v___y_1525_ = v_a_1574_;
v___y_1526_ = v___y_1559_;
v___y_1527_ = v___y_1558_;
v___y_1528_ = v___y_1571_;
v___y_1529_ = v___y_1572_;
v___y_1530_ = v___y_1561_;
v___y_1531_ = v___y_1567_;
v___y_1532_ = v_stxForExecution_1564_;
v___y_1533_ = v___y_1557_;
v___y_1534_ = v___y_1570_;
v___y_1535_ = v___y_1566_;
v___y_1536_ = v___y_1568_;
v___y_1537_ = v___y_1565_;
v___y_1538_ = v___y_1560_;
v___y_1539_ = v___y_1569_;
v___y_1540_ = v___y_1562_;
v___y_1541_ = v___y_1563_;
v___y_1542_ = v___x_1575_;
goto v___jp_1523_;
}
else
{
if (v___y_1557_ == 0)
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1573_);
v___y_1524_ = v___y_1555_;
v___y_1525_ = v_a_1576_;
v___y_1526_ = v___y_1559_;
v___y_1527_ = v___y_1558_;
v___y_1528_ = v___y_1571_;
v___y_1529_ = v___y_1572_;
v___y_1530_ = v___y_1561_;
v___y_1531_ = v___y_1567_;
v___y_1532_ = v_stxForExecution_1564_;
v___y_1533_ = v___y_1557_;
v___y_1534_ = v___y_1570_;
v___y_1535_ = v___y_1566_;
v___y_1536_ = v___y_1568_;
v___y_1537_ = v___y_1565_;
v___y_1538_ = v___y_1560_;
v___y_1539_ = v___y_1569_;
v___y_1540_ = v___y_1562_;
v___y_1541_ = v___y_1563_;
v___y_1542_ = v___y_1557_;
goto v___jp_1523_;
}
else
{
lean_object* v_a_1577_; lean_object* v_ref_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1577_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1573_);
v_ref_1578_ = lean_ctor_get(v___y_1571_, 2);
v___x_1579_ = 0;
v___x_1580_ = l_Lean_SourceInfo_fromRef(v_ref_1578_, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
v___x_1582_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_1581_);
v___x_1583_ = l_Lean_SourceInfo_fromRef(v_tk_1221_, v___x_1205_);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1587_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1559_) == 1)
{
lean_object* v_val_1588_; lean_object* v___x_1589_; 
v_val_1588_ = lean_ctor_get(v___y_1559_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___y_1559_, 1);
v___x_1589_ = l_Array_mkArray1___redArg(v_val_1588_);
v___y_1395_ = v___y_1555_;
v___y_1396_ = v___x_1587_;
v___y_1397_ = v_a_1577_;
v___y_1398_ = v___y_1558_;
v___y_1399_ = v___x_1586_;
v___y_1400_ = v___y_1571_;
v___y_1401_ = v___y_1572_;
v___y_1402_ = v___x_1585_;
v___y_1403_ = v___y_1561_;
v___y_1404_ = v___x_1582_;
v___y_1405_ = v___y_1567_;
v___y_1406_ = v___y_1570_;
v___y_1407_ = v_stxForExecution_1564_;
v___y_1408_ = v___y_1557_;
v___y_1409_ = v___y_1566_;
v___y_1410_ = v___y_1568_;
v___y_1411_ = v___y_1565_;
v___y_1412_ = v___y_1560_;
v___y_1413_ = v___y_1562_;
v___y_1414_ = v___y_1569_;
v___y_1415_ = v___y_1563_;
v___y_1416_ = v___x_1580_;
v___y_1417_ = v___x_1589_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1590_; 
lean_dec(v___y_1559_);
v___x_1590_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1395_ = v___y_1555_;
v___y_1396_ = v___x_1587_;
v___y_1397_ = v_a_1577_;
v___y_1398_ = v___y_1558_;
v___y_1399_ = v___x_1586_;
v___y_1400_ = v___y_1571_;
v___y_1401_ = v___y_1572_;
v___y_1402_ = v___x_1585_;
v___y_1403_ = v___y_1561_;
v___y_1404_ = v___x_1582_;
v___y_1405_ = v___y_1567_;
v___y_1406_ = v___y_1570_;
v___y_1407_ = v_stxForExecution_1564_;
v___y_1408_ = v___y_1557_;
v___y_1409_ = v___y_1566_;
v___y_1410_ = v___y_1568_;
v___y_1411_ = v___y_1565_;
v___y_1412_ = v___y_1560_;
v___y_1413_ = v___y_1562_;
v___y_1414_ = v___y_1569_;
v___y_1415_ = v___y_1563_;
v___y_1416_ = v___x_1580_;
v___y_1417_ = v___x_1590_;
goto v___jp_1394_;
}
}
}
}
v___jp_1591_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_inc_ref(v___y_1609_);
v___x_1618_ = l_Array_append___redArg(v___y_1609_, v___y_1617_);
lean_dec_ref(v___y_1617_);
lean_inc(v___y_1611_);
lean_inc(v___y_1596_);
v___x_1619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1619_, 0, v___y_1596_);
lean_ctor_set(v___x_1619_, 1, v___y_1611_);
lean_ctor_set(v___x_1619_, 2, v___x_1618_);
lean_inc(v___y_1610_);
v___x_1620_ = l_Lean_Syntax_node6(v___y_1596_, v___y_1602_, v___y_1605_, v___y_1610_, v___y_1614_, v___y_1600_, v___y_1593_, v___x_1619_);
v___y_1555_ = v___y_1592_;
v___y_1556_ = v___y_1610_;
v___y_1557_ = v___y_1599_;
v___y_1558_ = v___y_1606_;
v___y_1559_ = v___y_1595_;
v___y_1560_ = v___y_1612_;
v___y_1561_ = v___y_1598_;
v___y_1562_ = v___y_1615_;
v___y_1563_ = v___y_1616_;
v_stxForExecution_1564_ = v___x_1620_;
v___y_1565_ = v___y_1607_;
v___y_1566_ = v___y_1604_;
v___y_1567_ = v___y_1601_;
v___y_1568_ = v___y_1597_;
v___y_1569_ = v___y_1608_;
v___y_1570_ = v___y_1594_;
v___y_1571_ = v___y_1613_;
v___y_1572_ = v___y_1603_;
goto v___jp_1554_;
}
v___jp_1621_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_inc_ref_n(v___y_1632_, 2);
v___x_1646_ = l_Array_append___redArg(v___y_1632_, v___y_1645_);
lean_dec_ref(v___y_1645_);
lean_inc_n(v___y_1635_, 3);
lean_inc_n(v___y_1627_, 5);
v___x_1647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1627_);
lean_ctor_set(v___x_1647_, 1, v___y_1635_);
lean_ctor_set(v___x_1647_, 2, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___y_1627_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1651_ = l_Lean_Syntax_SepArray_ofElems(v___x_1650_, v___y_1636_);
v___x_1652_ = l_Array_append___redArg(v___y_1632_, v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1627_);
lean_ctor_set(v___x_1653_, 1, v___y_1635_);
lean_ctor_set(v___x_1653_, 2, v___x_1652_);
v___x_1654_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___y_1627_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_Syntax_node3(v___y_1627_, v___y_1635_, v___x_1649_, v___x_1653_, v___x_1655_);
if (lean_obj_tag(v___y_1624_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1658_; 
v_val_1657_ = lean_ctor_get(v___y_1624_, 0);
lean_inc(v_val_1657_);
v___x_1658_ = l_Array_mkArray1___redArg(v_val_1657_);
v___y_1592_ = v___y_1622_;
v___y_1593_ = v___x_1656_;
v___y_1594_ = v___y_1625_;
v___y_1595_ = v___y_1626_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___y_1628_;
v___y_1598_ = v___y_1631_;
v___y_1599_ = v___y_1634_;
v___y_1600_ = v___x_1647_;
v___y_1601_ = v___y_1637_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1642_;
v___y_1604_ = v___y_1644_;
v___y_1605_ = v___y_1623_;
v___y_1606_ = v___y_1624_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___y_1630_;
v___y_1609_ = v___y_1632_;
v___y_1610_ = v___y_1633_;
v___y_1611_ = v___y_1635_;
v___y_1612_ = v___y_1636_;
v___y_1613_ = v___y_1638_;
v___y_1614_ = v___y_1639_;
v___y_1615_ = v___y_1641_;
v___y_1616_ = v___y_1643_;
v___y_1617_ = v___x_1658_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1592_ = v___y_1622_;
v___y_1593_ = v___x_1656_;
v___y_1594_ = v___y_1625_;
v___y_1595_ = v___y_1626_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___y_1628_;
v___y_1598_ = v___y_1631_;
v___y_1599_ = v___y_1634_;
v___y_1600_ = v___x_1647_;
v___y_1601_ = v___y_1637_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1642_;
v___y_1604_ = v___y_1644_;
v___y_1605_ = v___y_1623_;
v___y_1606_ = v___y_1624_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___y_1630_;
v___y_1609_ = v___y_1632_;
v___y_1610_ = v___y_1633_;
v___y_1611_ = v___y_1635_;
v___y_1612_ = v___y_1636_;
v___y_1613_ = v___y_1638_;
v___y_1614_ = v___y_1639_;
v___y_1615_ = v___y_1641_;
v___y_1616_ = v___y_1643_;
v___y_1617_ = v___x_1659_;
goto v___jp_1591_;
}
}
v___jp_1660_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_inc_ref(v___y_1671_);
v___x_1684_ = l_Array_append___redArg(v___y_1671_, v___y_1683_);
lean_dec_ref(v___y_1683_);
lean_inc(v___y_1674_);
lean_inc(v___y_1666_);
v___x_1685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1685_, 0, v___y_1666_);
lean_ctor_set(v___x_1685_, 1, v___y_1674_);
lean_ctor_set(v___x_1685_, 2, v___x_1684_);
if (lean_obj_tag(v___y_1670_) == 1)
{
lean_object* v_val_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_val_1686_ = lean_ctor_get(v___y_1670_, 0);
v___x_1687_ = l_Lean_SourceInfo_fromRef(v_val_1686_, v___x_1205_);
v___x_1688_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Array_mkArray1___redArg(v___x_1689_);
v___y_1622_ = v___y_1661_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___y_1663_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1665_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___y_1667_;
v___y_1629_ = v___y_1668_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1676_;
v___y_1637_ = v___y_1675_;
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___x_1685_;
v___y_1640_ = v___y_1678_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1679_;
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___y_1681_;
v___y_1645_ = v___x_1690_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1622_ = v___y_1661_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___y_1663_;
v___y_1625_ = v___y_1664_;
v___y_1626_ = v___y_1665_;
v___y_1627_ = v___y_1666_;
v___y_1628_ = v___y_1667_;
v___y_1629_ = v___y_1668_;
v___y_1630_ = v___y_1669_;
v___y_1631_ = v___y_1670_;
v___y_1632_ = v___y_1671_;
v___y_1633_ = v___y_1672_;
v___y_1634_ = v___y_1673_;
v___y_1635_ = v___y_1674_;
v___y_1636_ = v___y_1676_;
v___y_1637_ = v___y_1675_;
v___y_1638_ = v___y_1677_;
v___y_1639_ = v___x_1685_;
v___y_1640_ = v___y_1678_;
v___y_1641_ = v___y_1680_;
v___y_1642_ = v___y_1679_;
v___y_1643_ = v___y_1682_;
v___y_1644_ = v___y_1681_;
v___y_1645_ = v___x_1691_;
goto v___jp_1621_;
}
}
v___jp_1692_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_inc_ref(v___y_1700_);
v___x_1719_ = l_Array_append___redArg(v___y_1700_, v___y_1718_);
lean_dec_ref(v___y_1718_);
lean_inc(v___y_1713_);
lean_inc(v___y_1694_);
v___x_1720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1720_, 0, v___y_1694_);
lean_ctor_set(v___x_1720_, 1, v___y_1713_);
lean_ctor_set(v___x_1720_, 2, v___x_1719_);
lean_inc(v___y_1711_);
v___x_1721_ = l_Lean_Syntax_node6(v___y_1694_, v___y_1712_, v___y_1699_, v___y_1711_, v___y_1710_, v___y_1701_, v___y_1709_, v___x_1720_);
v___y_1555_ = v___y_1693_;
v___y_1556_ = v___y_1711_;
v___y_1557_ = v___y_1702_;
v___y_1558_ = v___y_1706_;
v___y_1559_ = v___y_1696_;
v___y_1560_ = v___y_1714_;
v___y_1561_ = v___y_1698_;
v___y_1562_ = v___y_1716_;
v___y_1563_ = v___y_1717_;
v_stxForExecution_1564_ = v___x_1721_;
v___y_1565_ = v___y_1707_;
v___y_1566_ = v___y_1705_;
v___y_1567_ = v___y_1703_;
v___y_1568_ = v___y_1697_;
v___y_1569_ = v___y_1708_;
v___y_1570_ = v___y_1695_;
v___y_1571_ = v___y_1715_;
v___y_1572_ = v___y_1704_;
goto v___jp_1554_;
}
v___jp_1722_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc_ref_n(v___y_1734_, 2);
v___x_1747_ = l_Array_append___redArg(v___y_1734_, v___y_1746_);
lean_dec_ref(v___y_1746_);
lean_inc_n(v___y_1737_, 3);
lean_inc_n(v___y_1724_, 5);
v___x_1748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1724_);
lean_ctor_set(v___x_1748_, 1, v___y_1737_);
lean_ctor_set(v___x_1748_, 2, v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_1750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___y_1724_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_1752_ = l_Lean_Syntax_SepArray_ofElems(v___x_1751_, v___y_1739_);
v___x_1753_ = l_Array_append___redArg(v___y_1734_, v___x_1752_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1754_, 0, v___y_1724_);
lean_ctor_set(v___x_1754_, 1, v___y_1737_);
lean_ctor_set(v___x_1754_, 2, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1724_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node3(v___y_1724_, v___y_1737_, v___x_1750_, v___x_1754_, v___x_1756_);
if (lean_obj_tag(v___y_1725_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1759_; 
v_val_1758_ = lean_ctor_get(v___y_1725_, 0);
lean_inc(v_val_1758_);
v___x_1759_ = l_Array_mkArray1___redArg(v_val_1758_);
v___y_1693_ = v___y_1723_;
v___y_1694_ = v___y_1724_;
v___y_1695_ = v___y_1726_;
v___y_1696_ = v___y_1727_;
v___y_1697_ = v___y_1728_;
v___y_1698_ = v___y_1731_;
v___y_1699_ = v___y_1733_;
v___y_1700_ = v___y_1734_;
v___y_1701_ = v___x_1748_;
v___y_1702_ = v___y_1738_;
v___y_1703_ = v___y_1740_;
v___y_1704_ = v___y_1743_;
v___y_1705_ = v___y_1745_;
v___y_1706_ = v___y_1725_;
v___y_1707_ = v___y_1729_;
v___y_1708_ = v___y_1730_;
v___y_1709_ = v___x_1757_;
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___y_1735_;
v___y_1712_ = v___y_1736_;
v___y_1713_ = v___y_1737_;
v___y_1714_ = v___y_1739_;
v___y_1715_ = v___y_1741_;
v___y_1716_ = v___y_1742_;
v___y_1717_ = v___y_1744_;
v___y_1718_ = v___x_1759_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1693_ = v___y_1723_;
v___y_1694_ = v___y_1724_;
v___y_1695_ = v___y_1726_;
v___y_1696_ = v___y_1727_;
v___y_1697_ = v___y_1728_;
v___y_1698_ = v___y_1731_;
v___y_1699_ = v___y_1733_;
v___y_1700_ = v___y_1734_;
v___y_1701_ = v___x_1748_;
v___y_1702_ = v___y_1738_;
v___y_1703_ = v___y_1740_;
v___y_1704_ = v___y_1743_;
v___y_1705_ = v___y_1745_;
v___y_1706_ = v___y_1725_;
v___y_1707_ = v___y_1729_;
v___y_1708_ = v___y_1730_;
v___y_1709_ = v___x_1757_;
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___y_1735_;
v___y_1712_ = v___y_1736_;
v___y_1713_ = v___y_1737_;
v___y_1714_ = v___y_1739_;
v___y_1715_ = v___y_1741_;
v___y_1716_ = v___y_1742_;
v___y_1717_ = v___y_1744_;
v___y_1718_ = v___x_1760_;
goto v___jp_1692_;
}
}
v___jp_1761_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_inc_ref(v___y_1772_);
v___x_1785_ = l_Array_append___redArg(v___y_1772_, v___y_1784_);
lean_dec_ref(v___y_1784_);
lean_inc(v___y_1775_);
lean_inc(v___y_1763_);
v___x_1786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1763_);
lean_ctor_set(v___x_1786_, 1, v___y_1775_);
lean_ctor_set(v___x_1786_, 2, v___x_1785_);
if (lean_obj_tag(v___y_1770_) == 1)
{
lean_object* v_val_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_val_1787_ = lean_ctor_get(v___y_1770_, 0);
v___x_1788_ = l_Lean_SourceInfo_fromRef(v_val_1787_, v___x_1205_);
v___x_1789_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = l_Array_mkArray1___redArg(v___x_1790_);
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___y_1763_;
v___y_1725_ = v___y_1764_;
v___y_1726_ = v___y_1765_;
v___y_1727_ = v___y_1766_;
v___y_1728_ = v___y_1767_;
v___y_1729_ = v___y_1768_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1770_;
v___y_1732_ = v___x_1786_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1772_;
v___y_1735_ = v___y_1773_;
v___y_1736_ = v___y_1776_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1774_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1777_;
v___y_1741_ = v___y_1779_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1780_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1782_;
v___y_1746_ = v___x_1791_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1723_ = v___y_1762_;
v___y_1724_ = v___y_1763_;
v___y_1725_ = v___y_1764_;
v___y_1726_ = v___y_1765_;
v___y_1727_ = v___y_1766_;
v___y_1728_ = v___y_1767_;
v___y_1729_ = v___y_1768_;
v___y_1730_ = v___y_1769_;
v___y_1731_ = v___y_1770_;
v___y_1732_ = v___x_1786_;
v___y_1733_ = v___y_1771_;
v___y_1734_ = v___y_1772_;
v___y_1735_ = v___y_1773_;
v___y_1736_ = v___y_1776_;
v___y_1737_ = v___y_1775_;
v___y_1738_ = v___y_1774_;
v___y_1739_ = v___y_1778_;
v___y_1740_ = v___y_1777_;
v___y_1741_ = v___y_1779_;
v___y_1742_ = v___y_1781_;
v___y_1743_ = v___y_1780_;
v___y_1744_ = v___y_1783_;
v___y_1745_ = v___y_1782_;
v___y_1746_ = v___x_1792_;
goto v___jp_1722_;
}
}
v___jp_1793_:
{
lean_object* v_ref_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_ref_1812_ = lean_ctor_get(v___y_1806_, 2);
v___x_1813_ = l_Lean_SourceInfo_fromRef(v_ref_1812_, v___y_1811_);
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9));
lean_inc_ref(v___x_1208_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v___x_1206_);
v___x_1815_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_1814_);
v___x_1816_ = l_Lean_SourceInfo_fromRef(v_tk_1221_, v___x_1205_);
v___x_1817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___x_1814_);
v___x_1818_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1819_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1797_) == 1)
{
lean_object* v_val_1820_; lean_object* v___x_1821_; 
v_val_1820_ = lean_ctor_get(v___y_1797_, 0);
lean_inc(v_val_1820_);
v___x_1821_ = l_Array_mkArray1___redArg(v_val_1820_);
v___y_1762_ = v___y_1794_;
v___y_1763_ = v___x_1813_;
v___y_1764_ = v___y_1795_;
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___y_1799_;
v___y_1769_ = v___y_1800_;
v___y_1770_ = v___y_1801_;
v___y_1771_ = v___x_1817_;
v___y_1772_ = v___x_1819_;
v___y_1773_ = v___y_1802_;
v___y_1774_ = v___y_1803_;
v___y_1775_ = v___x_1818_;
v___y_1776_ = v___x_1815_;
v___y_1777_ = v___y_1804_;
v___y_1778_ = v___y_1805_;
v___y_1779_ = v___y_1806_;
v___y_1780_ = v___y_1808_;
v___y_1781_ = v___y_1807_;
v___y_1782_ = v___y_1810_;
v___y_1783_ = v___y_1809_;
v___y_1784_ = v___x_1821_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1762_ = v___y_1794_;
v___y_1763_ = v___x_1813_;
v___y_1764_ = v___y_1795_;
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___y_1799_;
v___y_1769_ = v___y_1800_;
v___y_1770_ = v___y_1801_;
v___y_1771_ = v___x_1817_;
v___y_1772_ = v___x_1819_;
v___y_1773_ = v___y_1802_;
v___y_1774_ = v___y_1803_;
v___y_1775_ = v___x_1818_;
v___y_1776_ = v___x_1815_;
v___y_1777_ = v___y_1804_;
v___y_1778_ = v___y_1805_;
v___y_1779_ = v___y_1806_;
v___y_1780_ = v___y_1808_;
v___y_1781_ = v___y_1807_;
v___y_1782_ = v___y_1810_;
v___y_1783_ = v___y_1809_;
v___y_1784_ = v___x_1822_;
goto v___jp_1761_;
}
}
v___jp_1823_:
{
if (lean_obj_tag(v___y_1830_) == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = 0;
v___y_1794_ = v___y_1824_;
v___y_1795_ = v___y_1828_;
v___y_1796_ = v___y_1838_;
v___y_1797_ = v___y_1827_;
v___y_1798_ = v___y_1836_;
v___y_1799_ = v___y_1833_;
v___y_1800_ = v___y_1837_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1825_;
v___y_1803_ = v___y_1826_;
v___y_1804_ = v___y_1835_;
v___y_1805_ = v_argsArray_1832_;
v___y_1806_ = v___y_1839_;
v___y_1807_ = v___y_1830_;
v___y_1808_ = v___y_1840_;
v___y_1809_ = v___y_1831_;
v___y_1810_ = v___y_1834_;
v___y_1811_ = v___x_1841_;
goto v___jp_1793_;
}
else
{
if (v___y_1826_ == 0)
{
v___y_1794_ = v___y_1824_;
v___y_1795_ = v___y_1828_;
v___y_1796_ = v___y_1838_;
v___y_1797_ = v___y_1827_;
v___y_1798_ = v___y_1836_;
v___y_1799_ = v___y_1833_;
v___y_1800_ = v___y_1837_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1825_;
v___y_1803_ = v___y_1826_;
v___y_1804_ = v___y_1835_;
v___y_1805_ = v_argsArray_1832_;
v___y_1806_ = v___y_1839_;
v___y_1807_ = v___y_1830_;
v___y_1808_ = v___y_1840_;
v___y_1809_ = v___y_1831_;
v___y_1810_ = v___y_1834_;
v___y_1811_ = v___y_1826_;
goto v___jp_1793_;
}
else
{
lean_object* v_ref_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_ref_1842_ = lean_ctor_get(v___y_1839_, 2);
v___x_1843_ = 0;
v___x_1844_ = l_Lean_SourceInfo_fromRef(v_ref_1842_, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10));
lean_inc_ref(v___x_1208_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v___x_1206_);
v___x_1846_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_1845_);
v___x_1847_ = l_Lean_SourceInfo_fromRef(v_tk_1221_, v___x_1205_);
v___x_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_1851_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_1827_) == 1)
{
lean_object* v_val_1852_; lean_object* v___x_1853_; 
v_val_1852_ = lean_ctor_get(v___y_1827_, 0);
lean_inc(v_val_1852_);
v___x_1853_ = l_Array_mkArray1___redArg(v_val_1852_);
v___y_1661_ = v___y_1824_;
v___y_1662_ = v___x_1849_;
v___y_1663_ = v___y_1828_;
v___y_1664_ = v___y_1838_;
v___y_1665_ = v___y_1827_;
v___y_1666_ = v___x_1844_;
v___y_1667_ = v___y_1836_;
v___y_1668_ = v___y_1833_;
v___y_1669_ = v___y_1837_;
v___y_1670_ = v___y_1829_;
v___y_1671_ = v___x_1851_;
v___y_1672_ = v___y_1825_;
v___y_1673_ = v___y_1826_;
v___y_1674_ = v___x_1850_;
v___y_1675_ = v___y_1835_;
v___y_1676_ = v_argsArray_1832_;
v___y_1677_ = v___y_1839_;
v___y_1678_ = v___x_1846_;
v___y_1679_ = v___y_1840_;
v___y_1680_ = v___y_1830_;
v___y_1681_ = v___y_1834_;
v___y_1682_ = v___y_1831_;
v___y_1683_ = v___x_1853_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_1661_ = v___y_1824_;
v___y_1662_ = v___x_1849_;
v___y_1663_ = v___y_1828_;
v___y_1664_ = v___y_1838_;
v___y_1665_ = v___y_1827_;
v___y_1666_ = v___x_1844_;
v___y_1667_ = v___y_1836_;
v___y_1668_ = v___y_1833_;
v___y_1669_ = v___y_1837_;
v___y_1670_ = v___y_1829_;
v___y_1671_ = v___x_1851_;
v___y_1672_ = v___y_1825_;
v___y_1673_ = v___y_1826_;
v___y_1674_ = v___x_1850_;
v___y_1675_ = v___y_1835_;
v___y_1676_ = v_argsArray_1832_;
v___y_1677_ = v___y_1839_;
v___y_1678_ = v___x_1846_;
v___y_1679_ = v___y_1840_;
v___y_1680_ = v___y_1830_;
v___y_1681_ = v___y_1834_;
v___y_1682_ = v___y_1831_;
v___y_1683_ = v___x_1854_;
goto v___jp_1660_;
}
}
}
}
v___jp_1855_:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1865_, v___y_1862_, v___y_1867_, v___y_1857_, v___y_1869_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = l_Lean_LibrarySuggestions_select(v_a_1875_, v___y_1873_, v___y_1862_, v___y_1867_, v___y_1857_, v___y_1869_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; size_t v_sz_1878_; size_t v___x_1879_; lean_object* v___x_1880_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v_sz_1878_ = lean_array_size(v_a_1877_);
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_1877_, v_sz_1878_, v___x_1879_, v___y_1872_, v___y_1863_, v___y_1865_, v___y_1860_, v___y_1868_, v___y_1862_, v___y_1867_, v___y_1857_, v___y_1869_);
lean_dec(v_a_1877_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___y_1824_ = v___y_1856_;
v___y_1825_ = v___y_1864_;
v___y_1826_ = v___y_1866_;
v___y_1827_ = v___y_1859_;
v___y_1828_ = v___y_1858_;
v___y_1829_ = v___y_1861_;
v___y_1830_ = v___y_1870_;
v___y_1831_ = v___y_1871_;
v_argsArray_1832_ = v_a_1881_;
v___y_1833_ = v___y_1863_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1860_;
v___y_1836_ = v___y_1868_;
v___y_1837_ = v___y_1862_;
v___y_1838_ = v___y_1867_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1869_;
goto v___jp_1823_;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v___y_1870_);
lean_dec(v___y_1864_);
lean_dec(v___y_1861_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1856_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v_a_1882_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1880_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1880_);
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
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1870_);
lean_dec(v___y_1864_);
lean_dec(v___y_1861_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1856_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v_a_1890_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1876_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1876_);
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
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1870_);
lean_dec(v___y_1864_);
lean_dec(v___y_1861_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1856_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v_a_1898_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1874_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1874_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
v___jp_1906_:
{
lean_object* v_config_1925_; uint8_t v_suggestions_1926_; 
v_config_1925_ = lean_ctor_get(v___y_1912_, 0);
lean_inc_ref(v_config_1925_);
lean_dec_ref(v___y_1912_);
v_suggestions_1926_ = lean_ctor_get_uint8(v_config_1925_, sizeof(void*)*3 + 26);
if (v_suggestions_1926_ == 0)
{
lean_dec_ref(v_config_1925_);
lean_dec_ref(v___f_1209_);
v___y_1824_ = v___y_1907_;
v___y_1825_ = v___y_1916_;
v___y_1826_ = v___y_1918_;
v___y_1827_ = v___y_1910_;
v___y_1828_ = v___y_1909_;
v___y_1829_ = v___y_1913_;
v___y_1830_ = v___y_1922_;
v___y_1831_ = v___y_1923_;
v_argsArray_1832_ = v___y_1924_;
v___y_1833_ = v___y_1915_;
v___y_1834_ = v___y_1917_;
v___y_1835_ = v___y_1911_;
v___y_1836_ = v___y_1920_;
v___y_1837_ = v___y_1914_;
v___y_1838_ = v___y_1919_;
v___y_1839_ = v___y_1908_;
v___y_1840_ = v___y_1921_;
goto v___jp_1823_;
}
else
{
lean_object* v_maxSuggestions_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_maxSuggestions_1927_ = lean_ctor_get(v_config_1925_, 2);
lean_inc(v_maxSuggestions_1927_);
lean_dec_ref(v_config_1925_);
v___x_1928_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12));
v___x_1929_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_1927_) == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_unsigned_to_nat(100u);
v___x_1931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1928_);
lean_ctor_set(v___x_1931_, 2, v___f_1209_);
lean_ctor_set(v___x_1931_, 3, v___x_1929_);
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1911_;
v___y_1861_ = v___y_1913_;
v___y_1862_ = v___y_1914_;
v___y_1863_ = v___y_1915_;
v___y_1864_ = v___y_1916_;
v___y_1865_ = v___y_1917_;
v___y_1866_ = v___y_1918_;
v___y_1867_ = v___y_1919_;
v___y_1868_ = v___y_1920_;
v___y_1869_ = v___y_1921_;
v___y_1870_ = v___y_1922_;
v___y_1871_ = v___y_1923_;
v___y_1872_ = v___y_1924_;
v___y_1873_ = v___x_1931_;
goto v___jp_1855_;
}
else
{
lean_object* v_val_1932_; lean_object* v___x_1933_; 
v_val_1932_ = lean_ctor_get(v_maxSuggestions_1927_, 0);
lean_inc(v_val_1932_);
lean_dec_ref_known(v_maxSuggestions_1927_, 1);
v___x_1933_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1933_, 0, v_val_1932_);
lean_ctor_set(v___x_1933_, 1, v___x_1928_);
lean_ctor_set(v___x_1933_, 2, v___f_1209_);
lean_ctor_set(v___x_1933_, 3, v___x_1929_);
v___y_1856_ = v___y_1907_;
v___y_1857_ = v___y_1908_;
v___y_1858_ = v___y_1909_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1911_;
v___y_1861_ = v___y_1913_;
v___y_1862_ = v___y_1914_;
v___y_1863_ = v___y_1915_;
v___y_1864_ = v___y_1916_;
v___y_1865_ = v___y_1917_;
v___y_1866_ = v___y_1918_;
v___y_1867_ = v___y_1919_;
v___y_1868_ = v___y_1920_;
v___y_1869_ = v___y_1921_;
v___y_1870_ = v___y_1922_;
v___y_1871_ = v___y_1923_;
v___y_1872_ = v___y_1924_;
v___y_1873_ = v___x_1933_;
goto v___jp_1855_;
}
}
}
v___jp_1934_:
{
uint8_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = 0;
lean_inc(v___y_1944_);
v___x_1951_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_1944_, v___x_1950_, v___y_1947_, v___y_1938_, v___y_1936_);
if (lean_obj_tag(v___x_1951_) == 0)
{
if (lean_obj_tag(v___y_1943_) == 1)
{
lean_object* v_a_1952_; lean_object* v_val_1953_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v_val_1953_ = lean_ctor_get(v___y_1943_, 0);
lean_inc(v_val_1953_);
lean_dec_ref_known(v___y_1943_, 1);
v___x_1954_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1953_);
lean_dec(v_val_1953_);
lean_inc(v___y_1940_);
v___y_1907_ = v___y_1940_;
v___y_1908_ = v___y_1938_;
v___y_1909_ = v___y_1940_;
v___y_1910_ = v___y_1949_;
v___y_1911_ = v___y_1946_;
v___y_1912_ = v_a_1952_;
v___y_1913_ = v___y_1945_;
v___y_1914_ = v___y_1935_;
v___y_1915_ = v___y_1947_;
v___y_1916_ = v___y_1944_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1942_;
v___y_1919_ = v___y_1948_;
v___y_1920_ = v___y_1937_;
v___y_1921_ = v___y_1936_;
v___y_1922_ = v___y_1939_;
v___y_1923_ = v___x_1950_;
v___y_1924_ = v___x_1954_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1956_; 
lean_dec(v___y_1943_);
v_a_1955_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
lean_inc(v___y_1940_);
v___y_1907_ = v___y_1940_;
v___y_1908_ = v___y_1938_;
v___y_1909_ = v___y_1940_;
v___y_1910_ = v___y_1949_;
v___y_1911_ = v___y_1946_;
v___y_1912_ = v_a_1955_;
v___y_1913_ = v___y_1945_;
v___y_1914_ = v___y_1935_;
v___y_1915_ = v___y_1947_;
v___y_1916_ = v___y_1944_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1942_;
v___y_1919_ = v___y_1948_;
v___y_1920_ = v___y_1937_;
v___y_1921_ = v___y_1936_;
v___y_1922_ = v___y_1939_;
v___y_1923_ = v___x_1950_;
v___y_1924_ = v___x_1956_;
goto v___jp_1906_;
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v___y_1949_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v_a_1957_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1951_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1951_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
v___jp_1965_:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Syntax_getOptional_x3f(v___y_1979_);
lean_dec(v___y_1979_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_box(0);
v___y_1935_ = v___y_1969_;
v___y_1936_ = v___y_1977_;
v___y_1937_ = v___y_1975_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___y_1978_;
v___y_1940_ = v___y_1980_;
v___y_1941_ = v___y_1973_;
v___y_1942_ = v___y_1972_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1971_;
v___y_1945_ = v___y_1968_;
v___y_1946_ = v___y_1967_;
v___y_1947_ = v___y_1970_;
v___y_1948_ = v___y_1974_;
v___y_1949_ = v___x_1982_;
goto v___jp_1934_;
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_val_1983_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_val_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v___y_1935_ = v___y_1969_;
v___y_1936_ = v___y_1977_;
v___y_1937_ = v___y_1975_;
v___y_1938_ = v___y_1966_;
v___y_1939_ = v___y_1978_;
v___y_1940_ = v___y_1980_;
v___y_1941_ = v___y_1973_;
v___y_1942_ = v___y_1972_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1971_;
v___y_1945_ = v___y_1968_;
v___y_1946_ = v___y_1967_;
v___y_1947_ = v___y_1970_;
v___y_1948_ = v___y_1974_;
v___y_1949_ = v___x_1988_;
goto v___jp_1934_;
}
}
}
}
v___jp_1991_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_unsigned_to_nat(4u);
v___x_2008_ = l_Lean_Syntax_getArg(v___y_1994_, v___x_2007_);
lean_dec(v___y_1994_);
v___x_2009_ = l_Lean_Syntax_getOptional_x3f(v___x_2008_);
lean_dec(v___x_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_box(0);
v___y_1966_ = v___y_2005_;
v___y_1967_ = v___y_2001_;
v___y_1968_ = v___y_1995_;
v___y_1969_ = v___y_2003_;
v___y_1970_ = v___y_1999_;
v___y_1971_ = v___y_1992_;
v___y_1972_ = v___y_1993_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_2004_;
v___y_1975_ = v___y_2002_;
v___y_1976_ = v_args_1998_;
v___y_1977_ = v___y_2006_;
v___y_1978_ = v___y_1996_;
v___y_1979_ = v___y_1997_;
v___y_1980_ = v___x_2010_;
goto v___jp_1965_;
}
else
{
lean_object* v_val_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_val_2011_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2009_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_val_2011_);
lean_dec(v___x_2009_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_val_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v___y_1966_ = v___y_2005_;
v___y_1967_ = v___y_2001_;
v___y_1968_ = v___y_1995_;
v___y_1969_ = v___y_2003_;
v___y_1970_ = v___y_1999_;
v___y_1971_ = v___y_1992_;
v___y_1972_ = v___y_1993_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_2004_;
v___y_1975_ = v___y_2002_;
v___y_1976_ = v_args_1998_;
v___y_1977_ = v___y_2006_;
v___y_1978_ = v___y_1996_;
v___y_1979_ = v___y_1997_;
v___y_1980_ = v___x_2016_;
goto v___jp_1965_;
}
}
}
}
v___jp_2020_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = lean_unsigned_to_nat(3u);
v___x_2036_ = l_Lean_Syntax_getArg(v___y_2023_, v___x_2035_);
v___x_2037_ = l_Lean_Syntax_isNone(v___x_2036_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; 
lean_inc(v___x_2036_);
v___x_2038_ = l_Lean_Syntax_matchesNull(v___x_2036_, v___x_2019_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec(v___x_2036_);
lean_dec(v_o_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec(v___y_2021_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_2039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2040_ = l_Lean_Syntax_getArg(v___x_2036_, v___x_1220_);
lean_dec(v___x_2036_);
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13));
lean_inc_ref(v___x_1208_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v___x_1206_);
v___x_2042_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_2041_);
lean_inc(v___x_2040_);
v___x_2043_ = l_Lean_Syntax_isOfKind(v___x_2040_, v___x_2042_);
lean_dec(v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v___x_2040_);
lean_dec(v_o_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec(v___y_2021_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_2044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v_args_2046_; lean_object* v___x_2047_; 
v___x_2045_ = l_Lean_Syntax_getArg(v___x_2040_, v___x_2019_);
lean_dec(v___x_2040_);
v_args_2046_ = l_Lean_Syntax_getArgs(v___x_2045_);
lean_dec(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_args_2046_);
v___y_1992_ = v___y_2021_;
v___y_1993_ = v___y_2022_;
v___y_1994_ = v___y_2023_;
v___y_1995_ = v_o_2026_;
v___y_1996_ = v___y_2024_;
v___y_1997_ = v___y_2025_;
v_args_1998_ = v___x_2047_;
v___y_1999_ = v___y_2027_;
v___y_2000_ = v___y_2028_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v___y_2031_;
v___y_2004_ = v___y_2032_;
v___y_2005_ = v___y_2033_;
v___y_2006_ = v___y_2034_;
goto v___jp_1991_;
}
}
}
else
{
lean_object* v___x_2048_; 
lean_dec(v___x_2036_);
v___x_2048_ = lean_box(0);
v___y_1992_ = v___y_2021_;
v___y_1993_ = v___y_2022_;
v___y_1994_ = v___y_2023_;
v___y_1995_ = v_o_2026_;
v___y_1996_ = v___y_2024_;
v___y_1997_ = v___y_2025_;
v_args_1998_ = v___x_2048_;
v___y_1999_ = v___y_2027_;
v___y_2000_ = v___y_2028_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v___y_2031_;
v___y_2004_ = v___y_2032_;
v___y_2005_ = v___y_2033_;
v___y_2006_ = v___y_2034_;
goto v___jp_1991_;
}
}
v___jp_2049_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2059_ = lean_unsigned_to_nat(2u);
v___x_2060_ = l_Lean_Syntax_getArg(v_stx_1204_, v___x_2059_);
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14));
lean_inc_ref(v___x_1208_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v___x_1206_);
v___x_2062_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_2061_);
lean_inc(v___x_2060_);
v___x_2063_ = l_Lean_Syntax_isOfKind(v___x_2060_, v___x_2062_);
lean_dec(v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec(v___x_2060_);
lean_dec(v_bang_2050_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_2064_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2064_;
}
else
{
lean_object* v_cfg_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_cfg_2065_ = l_Lean_Syntax_getArg(v___x_2060_, v___x_1220_);
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_1208_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v___x_1206_);
v___x_2067_ = l_Lean_Name_mkStr4(v___x_1206_, v___x_1207_, v___x_1208_, v___x_2066_);
lean_inc(v_cfg_2065_);
v___x_2068_ = l_Lean_Syntax_isOfKind(v_cfg_2065_, v___x_2067_);
lean_dec(v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec(v_cfg_2065_);
lean_dec(v___x_2060_);
lean_dec(v_bang_2050_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_2069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = l_Lean_Syntax_getArg(v___x_2060_, v___x_2019_);
v___x_2071_ = l_Lean_Syntax_getArg(v___x_2060_, v___x_2059_);
v___x_2072_ = l_Lean_Syntax_isNone(v___x_2071_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; 
lean_inc(v___x_2071_);
v___x_2073_ = l_Lean_Syntax_matchesNull(v___x_2071_, v___x_2019_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_dec(v___x_2071_);
lean_dec(v___x_2070_);
lean_dec(v_cfg_2065_);
lean_dec(v___x_2060_);
lean_dec(v_bang_2050_);
lean_dec(v_tk_1221_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
v___x_2074_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2074_;
}
else
{
lean_object* v_o_2075_; lean_object* v___x_2076_; 
v_o_2075_ = l_Lean_Syntax_getArg(v___x_2071_, v___x_1220_);
lean_dec(v___x_2071_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_o_2075_);
v___y_2021_ = v_cfg_2065_;
v___y_2022_ = v___x_2063_;
v___y_2023_ = v___x_2060_;
v___y_2024_ = v_bang_2050_;
v___y_2025_ = v___x_2070_;
v_o_2026_ = v___x_2076_;
v___y_2027_ = v___y_2051_;
v___y_2028_ = v___y_2052_;
v___y_2029_ = v___y_2053_;
v___y_2030_ = v___y_2054_;
v___y_2031_ = v___y_2055_;
v___y_2032_ = v___y_2056_;
v___y_2033_ = v___y_2057_;
v___y_2034_ = v___y_2058_;
goto v___jp_2020_;
}
}
else
{
lean_object* v___x_2077_; 
lean_dec(v___x_2071_);
v___x_2077_ = lean_box(0);
v___y_2021_ = v_cfg_2065_;
v___y_2022_ = v___x_2063_;
v___y_2023_ = v___x_2060_;
v___y_2024_ = v_bang_2050_;
v___y_2025_ = v___x_2070_;
v_o_2026_ = v___x_2077_;
v___y_2027_ = v___y_2051_;
v___y_2028_ = v___y_2052_;
v___y_2029_ = v___y_2053_;
v___y_2030_ = v___y_2054_;
v___y_2031_ = v___y_2055_;
v___y_2032_ = v___y_2056_;
v___y_2033_ = v___y_2057_;
v___y_2034_ = v___y_2058_;
goto v___jp_2020_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* v___x_2085_, lean_object* v_stx_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v___f_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_35147__boxed_2101_; uint8_t v___x_35148__boxed_2102_; lean_object* v_res_2103_; 
v___x_35147__boxed_2101_ = lean_unbox(v___x_2085_);
v___x_35148__boxed_2102_ = lean_unbox(v___x_2087_);
v_res_2103_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(v___x_35147__boxed_2101_, v_stx_2086_, v___x_35148__boxed_2102_, v___x_2088_, v___x_2089_, v___x_2090_, v___f_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v_stx_2086_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* v_stx_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; uint8_t v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___y_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_2124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_2125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_2126_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
lean_inc(v_stx_2113_);
v___x_2127_ = l_Lean_Syntax_isOfKind(v_stx_2113_, v___x_2126_);
v___x_2128_ = 1;
v___f_2129_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_2130_ = lean_box(v___x_2127_);
v___x_2131_ = lean_box(v___x_2128_);
v___y_2132_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___y_2132_, 0, v___x_2130_);
lean_closure_set(v___y_2132_, 1, v_stx_2113_);
lean_closure_set(v___y_2132_, 2, v___x_2131_);
lean_closure_set(v___y_2132_, 3, v___x_2123_);
lean_closure_set(v___y_2132_, 4, v___x_2124_);
lean_closure_set(v___y_2132_, 5, v___x_2125_);
lean_closure_set(v___y_2132_, 6, v___f_2129_);
v___x_2133_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2133_, 0, v___y_2132_);
v___x_2134_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2133_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* v_stx_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_Elab_Tactic_evalSimpTrace(v_stx_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(lean_object* v___x_2146_, lean_object* v_as_2147_, lean_object* v_as_x27_2148_, lean_object* v_b_2149_, lean_object* v_a_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_2146_, v_as_x27_2148_, v_b_2149_, v___y_2157_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(lean_object* v___x_2161_, lean_object* v_as_2162_, lean_object* v_as_x27_2163_, lean_object* v_b_2164_, lean_object* v_a_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(v___x_2161_, v_as_2162_, v_as_x27_2163_, v_b_2164_, v_a_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v_as_x27_2163_);
lean_dec(v_as_2162_);
lean_dec(v___x_2161_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_2176_, lean_object* v_ref_2177_, lean_object* v_msg_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_2177_, v_msg_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_ref_2190_, lean_object* v_msg_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_2189_, v_ref_2190_, v_msg_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v_ref_2190_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(lean_object* v_00_u03b1_2202_, lean_object* v_ref_2203_, lean_object* v_constName_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_2203_, v_constName_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_ref_2216_, lean_object* v_constName_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_2215_, v_ref_2216_, v_constName_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_ref_2216_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b1_2228_, lean_object* v_msg_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_2229_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_2240_, v_msg_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(lean_object* v_opt_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_2252_, v___y_2259_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_opt_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_opt_2263_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(lean_object* v_00_u03b1_2274_, lean_object* v_ref_2275_, lean_object* v_msg_2276_, lean_object* v_declHint_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_2275_, v_msg_2276_, v_declHint_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2288_, lean_object* v_ref_2289_, lean_object* v_msg_2290_, lean_object* v_declHint_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_2288_, v_ref_2289_, v_msg_2290_, v_declHint_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v_ref_2289_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(lean_object* v_msg_2302_, lean_object* v_declHint_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_2302_, v_declHint_2303_, v___y_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(lean_object* v_msg_2314_, lean_object* v_declHint_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_2314_, v_declHint_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(lean_object* v_ref_2326_, lean_object* v_msgData_2327_, uint8_t v_severity_2328_, uint8_t v_isSilent_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_2326_, v_msgData_2327_, v_severity_2328_, v_isSilent_2329_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(lean_object* v_ref_2340_, lean_object* v_msgData_2341_, lean_object* v_severity_2342_, lean_object* v_isSilent_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_severity_boxed_2353_; uint8_t v_isSilent_boxed_2354_; lean_object* v_res_2355_; 
v_severity_boxed_2353_ = lean_unbox(v_severity_2342_);
v_isSilent_boxed_2354_ = lean_unbox(v_isSilent_2343_);
v_res_2355_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_2340_, v_msgData_2341_, v_severity_boxed_2353_, v_isSilent_boxed_2354_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v_ref_2340_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2363_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2364_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__1));
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2366_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
v___x_2367_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2363_, v___x_2364_, v___x_2365_, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1));
v___x_2397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6));
v___x_2398_ = l_Lean_addBuiltinDeclarationRanges(v___x_2396_, v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(lean_object* v___x_2401_, lean_object* v_as_x27_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_){
_start:
{
if (lean_obj_tag(v_as_x27_2402_) == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v_b_2403_);
return v___x_2406_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v_ref_2409_; uint8_t v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_head_2407_ = lean_ctor_get(v_as_x27_2402_, 0);
v_tail_2408_ = lean_ctor_get(v_as_x27_2402_, 1);
v_ref_2409_ = lean_ctor_get(v___y_2404_, 2);
v___x_2410_ = 1;
v___x_2411_ = 0;
v___x_2412_ = l_Lean_SourceInfo_fromRef(v_ref_2409_, v___x_2411_);
v___x_2413_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1));
v___x_2414_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2415_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_2412_);
v___x_2416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2412_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
lean_ctor_set(v___x_2416_, 2, v___x_2415_);
lean_inc(v_head_2407_);
v___x_2417_ = l_Lean_mkCIdentFrom(v___x_2401_, v_head_2407_, v___x_2410_);
lean_inc_ref(v___x_2416_);
v___x_2418_ = l_Lean_Syntax_node3(v___x_2412_, v___x_2413_, v___x_2416_, v___x_2416_, v___x_2417_);
v___x_2419_ = lean_array_push(v_b_2403_, v___x_2418_);
v_as_x27_2402_ = v_tail_2408_;
v_b_2403_ = v___x_2419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(lean_object* v___x_2421_, lean_object* v_as_x27_2422_, lean_object* v_b_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2421_, v_as_x27_2422_, v_b_2423_, v___y_2424_);
lean_dec_ref(v___y_2424_);
lean_dec(v_as_x27_2422_);
lean_dec(v___x_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(lean_object* v_as_2427_, size_t v_sz_2428_, size_t v_i_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
uint8_t v___x_2440_; 
v___x_2440_ = lean_usize_dec_lt(v_i_2429_, v_sz_2428_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_b_2430_);
return v___x_2441_;
}
else
{
lean_object* v_a_2442_; lean_object* v_name_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_a_2442_ = lean_array_uget_borrowed(v_as_2427_, v_i_2429_);
v_name_2443_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_name_2443_);
v___x_2444_ = l_Lean_mkIdent(v_name_2443_);
lean_inc(v___x_2444_);
v___x_2445_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(v___x_2444_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_2444_, v_a_2446_, v_b_2430_, v___y_2437_);
lean_dec(v_a_2446_);
lean_dec(v___x_2444_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; size_t v___x_2449_; size_t v___x_2450_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = ((size_t)1ULL);
v___x_2450_ = lean_usize_add(v_i_2429_, v___x_2449_);
v_i_2429_ = v___x_2450_;
v_b_2430_ = v_a_2448_;
goto _start;
}
else
{
return v___x_2447_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v___x_2444_);
lean_dec_ref(v_b_2430_);
v_a_2452_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2445_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2445_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(lean_object* v_as_2460_, lean_object* v_sz_2461_, lean_object* v_i_2462_, lean_object* v_b_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2461_);
lean_dec(v_sz_2461_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2462_);
lean_dec(v_i_2462_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_2460_, v_sz_boxed_2473_, v_i_boxed_2474_, v_b_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_as_2460_);
return v_res_2475_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2478_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = lean_unsigned_to_nat(32u);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___x_2481_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3(void){
_start:
{
size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2484_ = ((size_t)5ULL);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = lean_unsigned_to_nat(32u);
v___x_2487_ = lean_mk_empty_array_with_capacity(v___x_2486_);
v___x_2488_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2);
v___x_2489_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v___x_2487_);
lean_ctor_set(v___x_2489_, 2, v___x_2485_);
lean_ctor_set(v___x_2489_, 3, v___x_2485_);
lean_ctor_set_usize(v___x_2489_, 4, v___x_2484_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3);
v___x_2491_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0);
v___x_2492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
lean_ctor_set(v___x_2492_, 2, v___x_2491_);
lean_ctor_set(v___x_2492_, 3, v___x_2490_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4);
v___x_2494_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(uint8_t v___x_2504_, lean_object* v_stx_2505_, uint8_t v___x_2506_, lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v___x_2509_, lean_object* v___f_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
if (v___x_2504_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_2520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v_tk_2522_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2637_; uint8_t v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v_stxForSuggestion_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; uint8_t v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; uint8_t v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; uint8_t v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; uint8_t v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint8_t v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2822_; lean_object* v___y_2823_; uint8_t v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; uint8_t v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; uint8_t v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; uint8_t v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; uint8_t v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; uint8_t v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; uint8_t v___y_2939_; uint8_t v___y_2940_; lean_object* v___y_2941_; lean_object* v_stxForExecution_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; uint8_t v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; uint8_t v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; uint8_t v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; uint8_t v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; uint8_t v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; uint8_t v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; uint8_t v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; uint8_t v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; uint8_t v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; uint8_t v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; uint8_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; uint8_t v___y_3253_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; uint8_t v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v_argsArray_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; uint8_t v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; lean_object* v___y_3432_; lean_object* v_args_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___x_3452_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v_o_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_bang_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v_tk_2522_ = l_Lean_Syntax_getArg(v_stx_2505_, v___x_2521_);
v___x_3452_ = lean_unsigned_to_nat(1u);
v___x_3511_ = l_Lean_Syntax_getArg(v_stx_2505_, v___x_3452_);
v___x_3512_ = l_Lean_Syntax_isNone(v___x_3511_);
if (v___x_3512_ == 0)
{
uint8_t v___x_3513_; 
lean_inc(v___x_3511_);
v___x_3513_ = l_Lean_Syntax_matchesNull(v___x_3511_, v___x_3452_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
lean_dec(v___x_3511_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_3514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3514_;
}
else
{
lean_object* v_bang_3515_; lean_object* v___x_3516_; 
v_bang_3515_ = l_Lean_Syntax_getArg(v___x_3511_, v___x_2521_);
lean_dec(v___x_3511_);
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_bang_3515_);
v_bang_3483_ = v___x_3516_;
v___y_3484_ = v___y_2511_;
v___y_3485_ = v___y_2512_;
v___y_3486_ = v___y_2513_;
v___y_3487_ = v___y_2514_;
v___y_3488_ = v___y_2515_;
v___y_3489_ = v___y_2516_;
v___y_3490_ = v___y_2517_;
v___y_3491_ = v___y_2518_;
goto v___jp_3482_;
}
}
else
{
lean_object* v___x_3517_; 
lean_dec(v___x_3511_);
v___x_3517_ = lean_box(0);
v_bang_3483_ = v___x_3517_;
v___y_3484_ = v___y_2511_;
v___y_3485_ = v___y_2512_;
v___y_3486_ = v___y_2513_;
v___y_3487_ = v___y_2514_;
v___y_3488_ = v___y_2515_;
v___y_3489_ = v___y_2516_;
v___y_3490_ = v___y_2517_;
v___y_3491_ = v___y_2518_;
goto v___jp_3482_;
}
v___jp_2523_:
{
lean_object* v_usedTheorems_2530_; lean_object* v_diag_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2573_; 
v_usedTheorems_2530_ = lean_ctor_get(v___y_2525_, 0);
v_diag_2531_ = lean_ctor_get(v___y_2525_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___y_2525_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2533_ = v___y_2525_;
v_isShared_2534_ = v_isSharedCheck_2573_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_diag_2531_);
lean_inc(v_usedTheorems_2530_);
lean_dec(v___y_2525_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2573_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_2524_, v_usedTheorems_2530_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec_ref(v_usedTheorems_2530_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v_ref_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v_ref_2537_ = lean_ctor_get(v___y_2528_, 2);
v___x_2538_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v_a_2536_);
lean_ctor_set(v___x_2533_, 0, v___x_2538_);
v___x_2540_ = v___x_2533_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_a_2536_);
v___x_2540_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
lean_ctor_set(v___x_2542_, 2, v___x_2541_);
lean_ctor_set(v___x_2542_, 3, v___x_2541_);
lean_ctor_set(v___x_2542_, 4, v___x_2541_);
lean_ctor_set(v___x_2542_, 5, v___x_2541_);
lean_inc(v_ref_2537_);
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_ref_2537_);
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_2545_ = 4;
v___x_2546_ = l_Lean_MessageData_nil;
v___x_2547_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2522_, v___x_2542_, v___x_2543_, v___x_2544_, v___x_2541_, v___x_2545_, v___x_2546_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2547_, 0);
lean_dec(v_unused_2555_);
v___x_2549_ = v___x_2547_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_dec(v___x_2547_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_diag_2531_);
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_diag_2531_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_diag_2531_);
v_a_2556_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2547_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2547_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_del_object(v___x_2533_);
lean_dec_ref(v_diag_2531_);
lean_dec(v_tk_2522_);
v_a_2565_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2535_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2535_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
v___jp_2574_:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2578_, v___y_2575_, v___y_2577_, v___y_2580_, v___y_2576_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_2586_ = l_Lean_Meta_simpAll(v_a_2584_, v___y_2582_, v___y_2581_, v___x_2585_, v___y_2575_, v___y_2577_, v___y_2580_, v___y_2576_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v_fst_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v_fst_2588_ = lean_ctor_get(v_a_2587_, 0);
if (lean_obj_tag(v_fst_2588_) == 0)
{
lean_object* v_snd_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_snd_2589_ = lean_ctor_get(v_a_2587_, 1);
lean_inc(v_snd_2589_);
lean_dec(v_a_2587_);
v___x_2590_ = lean_box(0);
v___x_2591_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2590_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2580_, v___y_2576_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v___y_2524_ = v___y_2579_;
v___y_2525_ = v_snd_2589_;
v___y_2526_ = v___y_2575_;
v___y_2527_ = v___y_2577_;
v___y_2528_ = v___y_2580_;
v___y_2529_ = v___y_2576_;
goto v___jp_2523_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_snd_2589_);
lean_dec(v___y_2579_);
lean_dec(v_tk_2522_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_snd_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2618_; 
lean_inc_ref(v_fst_2588_);
v_snd_2600_ = lean_ctor_get(v_a_2587_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_a_2587_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_a_2587_, 0);
lean_dec(v_unused_2619_);
v___x_2602_ = v_a_2587_;
v_isShared_2603_ = v_isSharedCheck_2618_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_snd_2600_);
lean_dec(v_a_2587_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2618_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_val_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v_val_2604_ = lean_ctor_get(v_fst_2588_, 0);
lean_inc(v_val_2604_);
lean_dec_ref_known(v_fst_2588_, 1);
v___x_2605_ = lean_box(0);
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 1);
lean_ctor_set(v___x_2602_, 1, v___x_2605_);
lean_ctor_set(v___x_2602_, 0, v_val_2604_);
v___x_2607_ = v___x_2602_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_val_2604_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2607_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2580_, v___y_2576_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_dec_ref_known(v___x_2608_, 1);
v___y_2524_ = v___y_2579_;
v___y_2525_ = v_snd_2600_;
v___y_2526_ = v___y_2575_;
v___y_2527_ = v___y_2577_;
v___y_2528_ = v___y_2580_;
v___y_2529_ = v___y_2576_;
goto v___jp_2523_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_snd_2600_);
lean_dec(v___y_2579_);
lean_dec(v_tk_2522_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v___y_2579_);
lean_dec(v_tk_2522_);
v_a_2620_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2586_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2586_);
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
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2579_);
lean_dec(v_tk_2522_);
v_a_2628_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2583_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2583_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
v___jp_2636_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_2651_ = l_Lean_Elab_Tactic_mkSimpContext(v___y_2640_, v___x_2506_, v___y_2638_, v___x_2506_, v___x_2650_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2640_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
if (lean_obj_tag(v___y_2637_) == 0)
{
lean_object* v_ctx_2653_; lean_object* v_simprocs_2654_; 
v_ctx_2653_ = lean_ctor_get(v_a_2652_, 0);
lean_inc_ref(v_ctx_2653_);
v_simprocs_2654_ = lean_ctor_get(v_a_2652_, 1);
lean_inc_ref(v_simprocs_2654_);
lean_dec(v_a_2652_);
v___y_2575_ = v___y_2646_;
v___y_2576_ = v___y_2649_;
v___y_2577_ = v___y_2647_;
v___y_2578_ = v___y_2643_;
v___y_2579_ = v_stxForSuggestion_2641_;
v___y_2580_ = v___y_2648_;
v___y_2581_ = v_simprocs_2654_;
v___y_2582_ = v_ctx_2653_;
goto v___jp_2574_;
}
else
{
lean_dec_ref_known(v___y_2637_, 1);
if (v___y_2639_ == 0)
{
lean_object* v_ctx_2655_; lean_object* v_simprocs_2656_; 
v_ctx_2655_ = lean_ctor_get(v_a_2652_, 0);
lean_inc_ref(v_ctx_2655_);
v_simprocs_2656_ = lean_ctor_get(v_a_2652_, 1);
lean_inc_ref(v_simprocs_2656_);
lean_dec(v_a_2652_);
v___y_2575_ = v___y_2646_;
v___y_2576_ = v___y_2649_;
v___y_2577_ = v___y_2647_;
v___y_2578_ = v___y_2643_;
v___y_2579_ = v_stxForSuggestion_2641_;
v___y_2580_ = v___y_2648_;
v___y_2581_ = v_simprocs_2656_;
v___y_2582_ = v_ctx_2655_;
goto v___jp_2574_;
}
else
{
lean_object* v_ctx_2657_; lean_object* v_simprocs_2658_; lean_object* v___x_2659_; 
v_ctx_2657_ = lean_ctor_get(v_a_2652_, 0);
lean_inc_ref(v_ctx_2657_);
v_simprocs_2658_ = lean_ctor_get(v_a_2652_, 1);
lean_inc_ref(v_simprocs_2658_);
lean_dec(v_a_2652_);
v___x_2659_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2657_);
v___y_2575_ = v___y_2646_;
v___y_2576_ = v___y_2649_;
v___y_2577_ = v___y_2647_;
v___y_2578_ = v___y_2643_;
v___y_2579_ = v_stxForSuggestion_2641_;
v___y_2580_ = v___y_2648_;
v___y_2581_ = v_simprocs_2658_;
v___y_2582_ = v___x_2659_;
goto v___jp_2574_;
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_stxForSuggestion_2641_);
lean_dec(v___y_2637_);
lean_dec(v_tk_2522_);
v_a_2660_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2651_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2651_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
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
v___jp_2668_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_inc_ref_n(v___y_2675_, 2);
v___x_2690_ = l_Array_append___redArg(v___y_2675_, v___y_2689_);
lean_dec_ref(v___y_2689_);
lean_inc_n(v___y_2672_, 3);
lean_inc_n(v___y_2670_, 5);
v___x_2691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2670_);
lean_ctor_set(v___x_2691_, 1, v___y_2672_);
lean_ctor_set(v___x_2691_, 2, v___x_2690_);
v___x_2692_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2670_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2695_ = l_Lean_Syntax_SepArray_ofElems(v___x_2694_, v___y_2669_);
lean_dec_ref(v___y_2669_);
v___x_2696_ = l_Array_append___redArg(v___y_2675_, v___x_2695_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2670_);
lean_ctor_set(v___x_2697_, 1, v___y_2672_);
lean_ctor_set(v___x_2697_, 2, v___x_2696_);
v___x_2698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___y_2670_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = l_Lean_Syntax_node3(v___y_2670_, v___y_2672_, v___x_2693_, v___x_2697_, v___x_2699_);
v___x_2701_ = l_Lean_Syntax_node5(v___y_2670_, v___y_2676_, v___y_2687_, v___y_2673_, v___y_2679_, v___x_2691_, v___x_2700_);
v___y_2637_ = v___y_2681_;
v___y_2638_ = v___y_2683_;
v___y_2639_ = v___y_2674_;
v___y_2640_ = v___y_2678_;
v_stxForSuggestion_2641_ = v___x_2701_;
v___y_2642_ = v___y_2686_;
v___y_2643_ = v___y_2688_;
v___y_2644_ = v___y_2685_;
v___y_2645_ = v___y_2671_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2682_;
v___y_2649_ = v___y_2684_;
goto v___jp_2636_;
}
v___jp_2702_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_inc_ref(v___y_2708_);
v___x_2724_ = l_Array_append___redArg(v___y_2708_, v___y_2723_);
lean_dec_ref(v___y_2723_);
lean_inc(v___y_2706_);
lean_inc(v___y_2704_);
v___x_2725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2704_);
lean_ctor_set(v___x_2725_, 1, v___y_2706_);
lean_ctor_set(v___x_2725_, 2, v___x_2724_);
if (lean_obj_tag(v___y_2712_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_val_2726_ = lean_ctor_get(v___y_2712_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v___y_2712_, 1);
v___x_2727_ = l_Lean_SourceInfo_fromRef(v_val_2726_, v___x_2506_);
lean_dec(v_val_2726_);
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = l_Array_mkArray1___redArg(v___x_2729_);
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2708_;
v___y_2676_ = v___y_2710_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___y_2713_;
v___y_2679_ = v___x_2725_;
v___y_2680_ = v___y_2714_;
v___y_2681_ = v___y_2715_;
v___y_2682_ = v___y_2716_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2719_;
v___y_2685_ = v___y_2718_;
v___y_2686_ = v___y_2720_;
v___y_2687_ = v___y_2722_;
v___y_2688_ = v___y_2721_;
v___y_2689_ = v___x_2730_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v___y_2712_);
v___x_2731_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2669_ = v___y_2703_;
v___y_2670_ = v___y_2704_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2708_;
v___y_2676_ = v___y_2710_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___y_2713_;
v___y_2679_ = v___x_2725_;
v___y_2680_ = v___y_2714_;
v___y_2681_ = v___y_2715_;
v___y_2682_ = v___y_2716_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2719_;
v___y_2685_ = v___y_2718_;
v___y_2686_ = v___y_2720_;
v___y_2687_ = v___y_2722_;
v___y_2688_ = v___y_2721_;
v___y_2689_ = v___x_2731_;
goto v___jp_2668_;
}
}
v___jp_2732_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_inc_ref_n(v___y_2742_, 2);
v___x_2754_ = l_Array_append___redArg(v___y_2742_, v___y_2753_);
lean_dec_ref(v___y_2753_);
lean_inc_n(v___y_2734_, 3);
lean_inc_n(v___y_2743_, 5);
v___x_2755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___y_2743_);
lean_ctor_set(v___x_2755_, 1, v___y_2734_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2743_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_2759_ = l_Lean_Syntax_SepArray_ofElems(v___x_2758_, v___y_2733_);
lean_dec_ref(v___y_2733_);
v___x_2760_ = l_Array_append___redArg(v___y_2742_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___y_2743_);
lean_ctor_set(v___x_2761_, 1, v___y_2734_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_2763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2743_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_Syntax_node3(v___y_2743_, v___y_2734_, v___x_2757_, v___x_2761_, v___x_2763_);
v___x_2765_ = l_Lean_Syntax_node5(v___y_2743_, v___y_2740_, v___y_2747_, v___y_2736_, v___y_2750_, v___x_2755_, v___x_2764_);
v___y_2637_ = v___y_2744_;
v___y_2638_ = v___y_2746_;
v___y_2639_ = v___y_2737_;
v___y_2640_ = v___y_2739_;
v_stxForSuggestion_2641_ = v___x_2765_;
v___y_2642_ = v___y_2751_;
v___y_2643_ = v___y_2752_;
v___y_2644_ = v___y_2749_;
v___y_2645_ = v___y_2735_;
v___y_2646_ = v___y_2738_;
v___y_2647_ = v___y_2741_;
v___y_2648_ = v___y_2745_;
v___y_2649_ = v___y_2748_;
goto v___jp_2636_;
}
v___jp_2766_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc_ref(v___y_2777_);
v___x_2788_ = l_Array_append___redArg(v___y_2777_, v___y_2787_);
lean_dec_ref(v___y_2787_);
lean_inc(v___y_2768_);
lean_inc(v___y_2778_);
v___x_2789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2789_, 0, v___y_2778_);
lean_ctor_set(v___x_2789_, 1, v___y_2768_);
lean_ctor_set(v___x_2789_, 2, v___x_2788_);
if (lean_obj_tag(v___y_2773_) == 1)
{
lean_object* v_val_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_val_2790_ = lean_ctor_get(v___y_2773_, 0);
lean_inc(v_val_2790_);
lean_dec_ref_known(v___y_2773_, 1);
v___x_2791_ = l_Lean_SourceInfo_fromRef(v_val_2790_, v___x_2506_);
lean_dec(v_val_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Array_mkArray1___redArg(v___x_2793_);
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2771_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2774_;
v___y_2740_ = v___y_2775_;
v___y_2741_ = v___y_2776_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___y_2779_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2781_;
v___y_2747_ = v___y_2782_;
v___y_2748_ = v___y_2784_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___x_2789_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___x_2794_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2795_; 
lean_dec(v___y_2773_);
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2733_ = v___y_2767_;
v___y_2734_ = v___y_2768_;
v___y_2735_ = v___y_2769_;
v___y_2736_ = v___y_2770_;
v___y_2737_ = v___y_2771_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___y_2774_;
v___y_2740_ = v___y_2775_;
v___y_2741_ = v___y_2776_;
v___y_2742_ = v___y_2777_;
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___y_2779_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2781_;
v___y_2747_ = v___y_2782_;
v___y_2748_ = v___y_2784_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___x_2789_;
v___y_2751_ = v___y_2785_;
v___y_2752_ = v___y_2786_;
v___y_2753_ = v___x_2795_;
goto v___jp_2732_;
}
}
v___jp_2796_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_inc_ref_n(v___y_2813_, 2);
v___x_2817_ = l_Array_append___redArg(v___y_2813_, v___y_2816_);
lean_dec_ref(v___y_2816_);
lean_inc_n(v___y_2804_, 2);
lean_inc_n(v___y_2808_, 2);
v___x_2818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2818_, 0, v___y_2808_);
lean_ctor_set(v___x_2818_, 1, v___y_2804_);
lean_ctor_set(v___x_2818_, 2, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___y_2808_);
lean_ctor_set(v___x_2819_, 1, v___y_2804_);
lean_ctor_set(v___x_2819_, 2, v___y_2813_);
v___x_2820_ = l_Lean_Syntax_node5(v___y_2808_, v___y_2800_, v___y_2806_, v___y_2798_, v___y_2814_, v___x_2818_, v___x_2819_);
v___y_2637_ = v___y_2805_;
v___y_2638_ = v___y_2809_;
v___y_2639_ = v___y_2799_;
v___y_2640_ = v___y_2802_;
v_stxForSuggestion_2641_ = v___x_2820_;
v___y_2642_ = v___y_2812_;
v___y_2643_ = v___y_2815_;
v___y_2644_ = v___y_2811_;
v___y_2645_ = v___y_2797_;
v___y_2646_ = v___y_2801_;
v___y_2647_ = v___y_2803_;
v___y_2648_ = v___y_2807_;
v___y_2649_ = v___y_2810_;
goto v___jp_2636_;
}
v___jp_2821_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_inc_ref(v___y_2840_);
v___x_2842_ = l_Array_append___redArg(v___y_2840_, v___y_2841_);
lean_dec_ref(v___y_2841_);
lean_inc(v___y_2830_);
lean_inc(v___y_2834_);
v___x_2843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2843_, 0, v___y_2834_);
lean_ctor_set(v___x_2843_, 1, v___y_2830_);
lean_ctor_set(v___x_2843_, 2, v___x_2842_);
if (lean_obj_tag(v___y_2827_) == 1)
{
lean_object* v_val_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_val_2844_ = lean_ctor_get(v___y_2827_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v___y_2827_, 1);
v___x_2845_ = l_Lean_SourceInfo_fromRef(v_val_2844_, v___x_2506_);
lean_dec(v_val_2844_);
v___x_2846_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = l_Array_mkArray1___redArg(v___x_2847_);
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___y_2825_;
v___y_2801_ = v___y_2826_;
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2829_;
v___y_2804_ = v___y_2830_;
v___y_2805_ = v___y_2831_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___y_2833_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2835_;
v___y_2810_ = v___y_2837_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___y_2838_;
v___y_2813_ = v___y_2840_;
v___y_2814_ = v___x_2843_;
v___y_2815_ = v___y_2839_;
v___y_2816_ = v___x_2848_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2849_; 
lean_dec(v___y_2827_);
v___x_2849_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2797_ = v___y_2822_;
v___y_2798_ = v___y_2823_;
v___y_2799_ = v___y_2824_;
v___y_2800_ = v___y_2825_;
v___y_2801_ = v___y_2826_;
v___y_2802_ = v___y_2828_;
v___y_2803_ = v___y_2829_;
v___y_2804_ = v___y_2830_;
v___y_2805_ = v___y_2831_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___y_2833_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2835_;
v___y_2810_ = v___y_2837_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___y_2838_;
v___y_2813_ = v___y_2840_;
v___y_2814_ = v___x_2843_;
v___y_2815_ = v___y_2839_;
v___y_2816_ = v___x_2849_;
goto v___jp_2796_;
}
}
v___jp_2850_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_inc_ref_n(v___y_2852_, 2);
v___x_2871_ = l_Array_append___redArg(v___y_2852_, v___y_2870_);
lean_dec_ref(v___y_2870_);
lean_inc_n(v___y_2865_, 2);
lean_inc_n(v___y_2854_, 2);
v___x_2872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2854_);
lean_ctor_set(v___x_2872_, 1, v___y_2865_);
lean_ctor_set(v___x_2872_, 2, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2873_, 0, v___y_2854_);
lean_ctor_set(v___x_2873_, 1, v___y_2865_);
lean_ctor_set(v___x_2873_, 2, v___y_2852_);
v___x_2874_ = l_Lean_Syntax_node5(v___y_2854_, v___y_2859_, v___y_2866_, v___y_2853_, v___y_2868_, v___x_2872_, v___x_2873_);
v___y_2637_ = v___y_2860_;
v___y_2638_ = v___y_2862_;
v___y_2639_ = v___y_2855_;
v___y_2640_ = v___y_2857_;
v_stxForSuggestion_2641_ = v___x_2874_;
v___y_2642_ = v___y_2867_;
v___y_2643_ = v___y_2869_;
v___y_2644_ = v___y_2864_;
v___y_2645_ = v___y_2851_;
v___y_2646_ = v___y_2856_;
v___y_2647_ = v___y_2858_;
v___y_2648_ = v___y_2861_;
v___y_2649_ = v___y_2863_;
goto v___jp_2636_;
}
v___jp_2875_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_inc_ref(v___y_2877_);
v___x_2896_ = l_Array_append___redArg(v___y_2877_, v___y_2895_);
lean_dec_ref(v___y_2895_);
lean_inc(v___y_2893_);
lean_inc(v___y_2879_);
v___x_2897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2897_, 0, v___y_2879_);
lean_ctor_set(v___x_2897_, 1, v___y_2893_);
lean_ctor_set(v___x_2897_, 2, v___x_2896_);
if (lean_obj_tag(v___y_2882_) == 1)
{
lean_object* v_val_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_val_2898_ = lean_ctor_get(v___y_2882_, 0);
lean_inc(v_val_2898_);
lean_dec_ref_known(v___y_2882_, 1);
v___x_2899_ = l_Lean_SourceInfo_fromRef(v_val_2898_, v___x_2506_);
lean_dec(v_val_2898_);
v___x_2900_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_2901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Array_mkArray1___redArg(v___x_2901_);
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2878_;
v___y_2854_ = v___y_2879_;
v___y_2855_ = v___y_2880_;
v___y_2856_ = v___y_2881_;
v___y_2857_ = v___y_2883_;
v___y_2858_ = v___y_2884_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2886_;
v___y_2861_ = v___y_2887_;
v___y_2862_ = v___y_2888_;
v___y_2863_ = v___y_2890_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2893_;
v___y_2866_ = v___y_2892_;
v___y_2867_ = v___y_2891_;
v___y_2868_ = v___x_2897_;
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___x_2902_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2903_; 
lean_dec(v___y_2882_);
v___x_2903_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2851_ = v___y_2876_;
v___y_2852_ = v___y_2877_;
v___y_2853_ = v___y_2878_;
v___y_2854_ = v___y_2879_;
v___y_2855_ = v___y_2880_;
v___y_2856_ = v___y_2881_;
v___y_2857_ = v___y_2883_;
v___y_2858_ = v___y_2884_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2886_;
v___y_2861_ = v___y_2887_;
v___y_2862_ = v___y_2888_;
v___y_2863_ = v___y_2890_;
v___y_2864_ = v___y_2889_;
v___y_2865_ = v___y_2893_;
v___y_2866_ = v___y_2892_;
v___y_2867_ = v___y_2891_;
v___y_2868_ = v___x_2897_;
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___x_2903_;
goto v___jp_2850_;
}
}
v___jp_2904_:
{
lean_object* v_ref_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_ref_2922_ = lean_ctor_get(v___y_2915_, 2);
v___x_2923_ = l_Lean_SourceInfo_fromRef(v_ref_2922_, v___y_2921_);
v___x_2924_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2925_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_2924_);
v___x_2926_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_2927_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2930_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2913_) == 1)
{
lean_object* v_val_2931_; lean_object* v___x_2932_; 
v_val_2931_ = lean_ctor_get(v___y_2913_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v___y_2913_, 1);
v___x_2932_ = l_Array_mkArray1___redArg(v_val_2931_);
v___y_2703_ = v___y_2905_;
v___y_2704_ = v___x_2923_;
v___y_2705_ = v___y_2906_;
v___y_2706_ = v___x_2929_;
v___y_2707_ = v___y_2907_;
v___y_2708_ = v___x_2930_;
v___y_2709_ = v___y_2908_;
v___y_2710_ = v___x_2925_;
v___y_2711_ = v___y_2909_;
v___y_2712_ = v___y_2910_;
v___y_2713_ = v___y_2911_;
v___y_2714_ = v___y_2912_;
v___y_2715_ = v___y_2914_;
v___y_2716_ = v___y_2915_;
v___y_2717_ = v___y_2916_;
v___y_2718_ = v___y_2918_;
v___y_2719_ = v___y_2917_;
v___y_2720_ = v___y_2919_;
v___y_2721_ = v___y_2920_;
v___y_2722_ = v___x_2928_;
v___y_2723_ = v___x_2932_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2933_; 
lean_dec(v___y_2913_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2703_ = v___y_2905_;
v___y_2704_ = v___x_2923_;
v___y_2705_ = v___y_2906_;
v___y_2706_ = v___x_2929_;
v___y_2707_ = v___y_2907_;
v___y_2708_ = v___x_2930_;
v___y_2709_ = v___y_2908_;
v___y_2710_ = v___x_2925_;
v___y_2711_ = v___y_2909_;
v___y_2712_ = v___y_2910_;
v___y_2713_ = v___y_2911_;
v___y_2714_ = v___y_2912_;
v___y_2715_ = v___y_2914_;
v___y_2716_ = v___y_2915_;
v___y_2717_ = v___y_2916_;
v___y_2718_ = v___y_2918_;
v___y_2719_ = v___y_2917_;
v___y_2720_ = v___y_2919_;
v___y_2721_ = v___y_2920_;
v___y_2722_ = v___x_2928_;
v___y_2723_ = v___x_2933_;
goto v___jp_2702_;
}
}
v___jp_2934_:
{
lean_object* v___x_2951_; lean_object* v_a_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2951_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v___y_2937_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = lean_array_get_size(v___y_2935_);
v___x_2954_ = lean_nat_dec_eq(v___x_2953_, v___x_2521_);
if (v___x_2954_ == 0)
{
if (lean_obj_tag(v___y_2938_) == 0)
{
v___y_2905_ = v___y_2935_;
v___y_2906_ = v___y_2946_;
v___y_2907_ = v_a_2952_;
v___y_2908_ = v___y_2940_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2941_;
v___y_2911_ = v_stxForExecution_2942_;
v___y_2912_ = v___y_2948_;
v___y_2913_ = v___y_2936_;
v___y_2914_ = v___y_2938_;
v___y_2915_ = v___y_2949_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2950_;
v___y_2918_ = v___y_2945_;
v___y_2919_ = v___y_2943_;
v___y_2920_ = v___y_2944_;
v___y_2921_ = v___x_2954_;
goto v___jp_2904_;
}
else
{
if (v___y_2940_ == 0)
{
v___y_2905_ = v___y_2935_;
v___y_2906_ = v___y_2946_;
v___y_2907_ = v_a_2952_;
v___y_2908_ = v___y_2940_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2941_;
v___y_2911_ = v_stxForExecution_2942_;
v___y_2912_ = v___y_2948_;
v___y_2913_ = v___y_2936_;
v___y_2914_ = v___y_2938_;
v___y_2915_ = v___y_2949_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2950_;
v___y_2918_ = v___y_2945_;
v___y_2919_ = v___y_2943_;
v___y_2920_ = v___y_2944_;
v___y_2921_ = v___y_2940_;
goto v___jp_2904_;
}
else
{
lean_object* v_ref_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_ref_2955_ = lean_ctor_get(v___y_2949_, 2);
v___x_2956_ = l_Lean_SourceInfo_fromRef(v_ref_2955_, v___x_2954_);
v___x_2957_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2958_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_2957_);
v___x_2959_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_2960_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2963_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2936_) == 1)
{
lean_object* v_val_2964_; lean_object* v___x_2965_; 
v_val_2964_ = lean_ctor_get(v___y_2936_, 0);
lean_inc(v_val_2964_);
lean_dec_ref_known(v___y_2936_, 1);
v___x_2965_ = l_Array_mkArray1___redArg(v_val_2964_);
v___y_2767_ = v___y_2935_;
v___y_2768_ = v___x_2962_;
v___y_2769_ = v___y_2946_;
v___y_2770_ = v_a_2952_;
v___y_2771_ = v___y_2940_;
v___y_2772_ = v___y_2947_;
v___y_2773_ = v___y_2941_;
v___y_2774_ = v_stxForExecution_2942_;
v___y_2775_ = v___x_2958_;
v___y_2776_ = v___y_2948_;
v___y_2777_ = v___x_2963_;
v___y_2778_ = v___x_2956_;
v___y_2779_ = v___y_2938_;
v___y_2780_ = v___y_2949_;
v___y_2781_ = v___y_2939_;
v___y_2782_ = v___x_2961_;
v___y_2783_ = v___y_2945_;
v___y_2784_ = v___y_2950_;
v___y_2785_ = v___y_2943_;
v___y_2786_ = v___y_2944_;
v___y_2787_ = v___x_2965_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2966_; 
lean_dec(v___y_2936_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2767_ = v___y_2935_;
v___y_2768_ = v___x_2962_;
v___y_2769_ = v___y_2946_;
v___y_2770_ = v_a_2952_;
v___y_2771_ = v___y_2940_;
v___y_2772_ = v___y_2947_;
v___y_2773_ = v___y_2941_;
v___y_2774_ = v_stxForExecution_2942_;
v___y_2775_ = v___x_2958_;
v___y_2776_ = v___y_2948_;
v___y_2777_ = v___x_2963_;
v___y_2778_ = v___x_2956_;
v___y_2779_ = v___y_2938_;
v___y_2780_ = v___y_2949_;
v___y_2781_ = v___y_2939_;
v___y_2782_ = v___x_2961_;
v___y_2783_ = v___y_2945_;
v___y_2784_ = v___y_2950_;
v___y_2785_ = v___y_2943_;
v___y_2786_ = v___y_2944_;
v___y_2787_ = v___x_2966_;
goto v___jp_2766_;
}
}
}
}
else
{
lean_dec_ref(v___y_2935_);
if (lean_obj_tag(v___y_2938_) == 0)
{
lean_object* v_ref_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_ref_2967_ = lean_ctor_get(v___y_2949_, 2);
v___x_2968_ = 0;
v___x_2969_ = l_Lean_SourceInfo_fromRef(v_ref_2967_, v___x_2968_);
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
v___x_2971_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_2970_);
v___x_2972_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_2974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2976_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2936_) == 1)
{
lean_object* v_val_2977_; lean_object* v___x_2978_; 
v_val_2977_ = lean_ctor_get(v___y_2936_, 0);
lean_inc(v_val_2977_);
lean_dec_ref_known(v___y_2936_, 1);
v___x_2978_ = l_Array_mkArray1___redArg(v_val_2977_);
v___y_2822_ = v___y_2946_;
v___y_2823_ = v_a_2952_;
v___y_2824_ = v___y_2940_;
v___y_2825_ = v___x_2971_;
v___y_2826_ = v___y_2947_;
v___y_2827_ = v___y_2941_;
v___y_2828_ = v_stxForExecution_2942_;
v___y_2829_ = v___y_2948_;
v___y_2830_ = v___x_2975_;
v___y_2831_ = v___y_2938_;
v___y_2832_ = v___x_2974_;
v___y_2833_ = v___y_2949_;
v___y_2834_ = v___x_2969_;
v___y_2835_ = v___y_2939_;
v___y_2836_ = v___y_2945_;
v___y_2837_ = v___y_2950_;
v___y_2838_ = v___y_2943_;
v___y_2839_ = v___y_2944_;
v___y_2840_ = v___x_2976_;
v___y_2841_ = v___x_2978_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2979_; 
lean_dec(v___y_2936_);
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2822_ = v___y_2946_;
v___y_2823_ = v_a_2952_;
v___y_2824_ = v___y_2940_;
v___y_2825_ = v___x_2971_;
v___y_2826_ = v___y_2947_;
v___y_2827_ = v___y_2941_;
v___y_2828_ = v_stxForExecution_2942_;
v___y_2829_ = v___y_2948_;
v___y_2830_ = v___x_2975_;
v___y_2831_ = v___y_2938_;
v___y_2832_ = v___x_2974_;
v___y_2833_ = v___y_2949_;
v___y_2834_ = v___x_2969_;
v___y_2835_ = v___y_2939_;
v___y_2836_ = v___y_2945_;
v___y_2837_ = v___y_2950_;
v___y_2838_ = v___y_2943_;
v___y_2839_ = v___y_2944_;
v___y_2840_ = v___x_2976_;
v___y_2841_ = v___x_2979_;
goto v___jp_2821_;
}
}
else
{
lean_object* v_ref_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_ref_2980_ = lean_ctor_get(v___y_2949_, 2);
v___x_2981_ = 0;
v___x_2982_ = l_Lean_SourceInfo_fromRef(v_ref_2980_, v___x_2981_);
v___x_2983_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
v___x_2984_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_2983_);
v___x_2985_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_2986_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_2987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_2989_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_2936_) == 1)
{
lean_object* v_val_2990_; lean_object* v___x_2991_; 
v_val_2990_ = lean_ctor_get(v___y_2936_, 0);
lean_inc(v_val_2990_);
lean_dec_ref_known(v___y_2936_, 1);
v___x_2991_ = l_Array_mkArray1___redArg(v_val_2990_);
v___y_2876_ = v___y_2946_;
v___y_2877_ = v___x_2989_;
v___y_2878_ = v_a_2952_;
v___y_2879_ = v___x_2982_;
v___y_2880_ = v___y_2940_;
v___y_2881_ = v___y_2947_;
v___y_2882_ = v___y_2941_;
v___y_2883_ = v_stxForExecution_2942_;
v___y_2884_ = v___y_2948_;
v___y_2885_ = v___x_2984_;
v___y_2886_ = v___y_2938_;
v___y_2887_ = v___y_2949_;
v___y_2888_ = v___y_2939_;
v___y_2889_ = v___y_2945_;
v___y_2890_ = v___y_2950_;
v___y_2891_ = v___y_2943_;
v___y_2892_ = v___x_2987_;
v___y_2893_ = v___x_2988_;
v___y_2894_ = v___y_2944_;
v___y_2895_ = v___x_2991_;
goto v___jp_2875_;
}
else
{
lean_object* v___x_2992_; 
lean_dec(v___y_2936_);
v___x_2992_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2876_ = v___y_2946_;
v___y_2877_ = v___x_2989_;
v___y_2878_ = v_a_2952_;
v___y_2879_ = v___x_2982_;
v___y_2880_ = v___y_2940_;
v___y_2881_ = v___y_2947_;
v___y_2882_ = v___y_2941_;
v___y_2883_ = v_stxForExecution_2942_;
v___y_2884_ = v___y_2948_;
v___y_2885_ = v___x_2984_;
v___y_2886_ = v___y_2938_;
v___y_2887_ = v___y_2949_;
v___y_2888_ = v___y_2939_;
v___y_2889_ = v___y_2945_;
v___y_2890_ = v___y_2950_;
v___y_2891_ = v___y_2943_;
v___y_2892_ = v___x_2987_;
v___y_2893_ = v___x_2988_;
v___y_2894_ = v___y_2944_;
v___y_2895_ = v___x_2992_;
goto v___jp_2875_;
}
}
}
}
v___jp_2993_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_inc_ref_n(v___y_2997_, 2);
v___x_3016_ = l_Array_append___redArg(v___y_2997_, v___y_3015_);
lean_dec_ref(v___y_3015_);
lean_inc_n(v___y_3000_, 3);
lean_inc_n(v___y_3006_, 5);
v___x_3017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3017_, 0, v___y_3006_);
lean_ctor_set(v___x_3017_, 1, v___y_3000_);
lean_ctor_set(v___x_3017_, 2, v___x_3016_);
v___x_3018_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___y_3006_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3021_ = l_Lean_Syntax_SepArray_ofElems(v___x_3020_, v___y_2994_);
v___x_3022_ = l_Array_append___redArg(v___y_2997_, v___x_3021_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3023_, 0, v___y_3006_);
lean_ctor_set(v___x_3023_, 1, v___y_3000_);
lean_ctor_set(v___x_3023_, 2, v___x_3022_);
v___x_3024_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___y_3006_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_Syntax_node3(v___y_3006_, v___y_3000_, v___x_3019_, v___x_3023_, v___x_3025_);
lean_inc(v___y_2999_);
v___x_3027_ = l_Lean_Syntax_node5(v___y_3006_, v___y_3013_, v___y_3009_, v___y_2999_, v___y_3011_, v___x_3017_, v___x_3026_);
v___y_2935_ = v___y_2994_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_2999_;
v___y_2938_ = v___y_3008_;
v___y_2939_ = v___y_3010_;
v___y_2940_ = v___y_3001_;
v___y_2941_ = v___y_3005_;
v_stxForExecution_2942_ = v___x_3027_;
v___y_2943_ = v___y_3012_;
v___y_2944_ = v___y_2995_;
v___y_2945_ = v___y_3002_;
v___y_2946_ = v___y_3014_;
v___y_2947_ = v___y_2998_;
v___y_2948_ = v___y_3004_;
v___y_2949_ = v___y_2996_;
v___y_2950_ = v___y_3003_;
goto v___jp_2934_;
}
v___jp_3028_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_inc_ref(v___y_3031_);
v___x_3050_ = l_Array_append___redArg(v___y_3031_, v___y_3049_);
lean_dec_ref(v___y_3049_);
lean_inc(v___y_3035_);
lean_inc(v___y_3041_);
v___x_3051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___y_3041_);
lean_ctor_set(v___x_3051_, 1, v___y_3035_);
lean_ctor_set(v___x_3051_, 2, v___x_3050_);
if (lean_obj_tag(v___y_3040_) == 1)
{
lean_object* v_val_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_val_3052_ = lean_ctor_get(v___y_3040_, 0);
v___x_3053_ = l_Lean_SourceInfo_fromRef(v_val_3052_, v___x_2506_);
v___x_3054_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = l_Array_mkArray1___redArg(v___x_3055_);
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3032_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3036_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3038_;
v___y_3004_ = v___y_3039_;
v___y_3005_ = v___y_3040_;
v___y_3006_ = v___y_3041_;
v___y_3007_ = v___y_3042_;
v___y_3008_ = v___y_3043_;
v___y_3009_ = v___y_3044_;
v___y_3010_ = v___y_3046_;
v___y_3011_ = v___x_3051_;
v___y_3012_ = v___y_3045_;
v___y_3013_ = v___y_3047_;
v___y_3014_ = v___y_3048_;
v___y_3015_ = v___x_3056_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3032_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3034_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3036_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3038_;
v___y_3004_ = v___y_3039_;
v___y_3005_ = v___y_3040_;
v___y_3006_ = v___y_3041_;
v___y_3007_ = v___y_3042_;
v___y_3008_ = v___y_3043_;
v___y_3009_ = v___y_3044_;
v___y_3010_ = v___y_3046_;
v___y_3011_ = v___x_3051_;
v___y_3012_ = v___y_3045_;
v___y_3013_ = v___y_3047_;
v___y_3014_ = v___y_3048_;
v___y_3015_ = v___x_3057_;
goto v___jp_2993_;
}
}
v___jp_3058_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_inc_ref_n(v___y_3066_, 2);
v___x_3081_ = l_Array_append___redArg(v___y_3066_, v___y_3080_);
lean_dec_ref(v___y_3080_);
lean_inc_n(v___y_3078_, 3);
lean_inc_n(v___y_3072_, 5);
v___x_3082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___y_3072_);
lean_ctor_set(v___x_3082_, 1, v___y_3078_);
lean_ctor_set(v___x_3082_, 2, v___x_3081_);
v___x_3083_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
v___x_3084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3072_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5));
v___x_3086_ = l_Lean_Syntax_SepArray_ofElems(v___x_3085_, v___y_3060_);
v___x_3087_ = l_Array_append___redArg(v___y_3066_, v___x_3086_);
lean_dec_ref(v___x_3086_);
v___x_3088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3088_, 0, v___y_3072_);
lean_ctor_set(v___x_3088_, 1, v___y_3078_);
lean_ctor_set(v___x_3088_, 2, v___x_3087_);
v___x_3089_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_3090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___y_3072_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = l_Lean_Syntax_node3(v___y_3072_, v___y_3078_, v___x_3084_, v___x_3088_, v___x_3090_);
lean_inc(v___y_3064_);
v___x_3092_ = l_Lean_Syntax_node5(v___y_3072_, v___y_3073_, v___y_3067_, v___y_3064_, v___y_3059_, v___x_3082_, v___x_3091_);
v___y_2935_ = v___y_3060_;
v___y_2936_ = v___y_3074_;
v___y_2937_ = v___y_3064_;
v___y_2938_ = v___y_3075_;
v___y_2939_ = v___y_3076_;
v___y_2940_ = v___y_3065_;
v___y_2941_ = v___y_3071_;
v_stxForExecution_2942_ = v___x_3092_;
v___y_2943_ = v___y_3077_;
v___y_2944_ = v___y_3061_;
v___y_2945_ = v___y_3068_;
v___y_2946_ = v___y_3079_;
v___y_2947_ = v___y_3063_;
v___y_2948_ = v___y_3070_;
v___y_2949_ = v___y_3062_;
v___y_2950_ = v___y_3069_;
goto v___jp_2934_;
}
v___jp_3093_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_inc_ref(v___y_3099_);
v___x_3115_ = l_Array_append___redArg(v___y_3099_, v___y_3114_);
lean_dec_ref(v___y_3114_);
lean_inc(v___y_3113_);
lean_inc(v___y_3106_);
v___x_3116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3116_, 0, v___y_3106_);
lean_ctor_set(v___x_3116_, 1, v___y_3113_);
lean_ctor_set(v___x_3116_, 2, v___x_3115_);
if (lean_obj_tag(v___y_3105_) == 1)
{
lean_object* v_val_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_val_3117_ = lean_ctor_get(v___y_3105_, 0);
v___x_3118_ = l_Lean_SourceInfo_fromRef(v_val_3117_, v___x_2506_);
v___x_3119_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3118_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = l_Array_mkArray1___redArg(v___x_3120_);
v___y_3059_ = v___x_3116_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3098_;
v___y_3065_ = v___y_3100_;
v___y_3066_ = v___y_3099_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___y_3103_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3105_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3108_;
v___y_3075_ = v___y_3109_;
v___y_3076_ = v___y_3111_;
v___y_3077_ = v___y_3110_;
v___y_3078_ = v___y_3113_;
v___y_3079_ = v___y_3112_;
v___y_3080_ = v___x_3121_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3122_; 
v___x_3122_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3059_ = v___x_3116_;
v___y_3060_ = v___y_3094_;
v___y_3061_ = v___y_3095_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3098_;
v___y_3065_ = v___y_3100_;
v___y_3066_ = v___y_3099_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___y_3103_;
v___y_3070_ = v___y_3104_;
v___y_3071_ = v___y_3105_;
v___y_3072_ = v___y_3106_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3108_;
v___y_3075_ = v___y_3109_;
v___y_3076_ = v___y_3111_;
v___y_3077_ = v___y_3110_;
v___y_3078_ = v___y_3113_;
v___y_3079_ = v___y_3112_;
v___y_3080_ = v___x_3122_;
goto v___jp_3058_;
}
}
v___jp_3123_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_inc_ref_n(v___y_3141_, 2);
v___x_3146_ = l_Array_append___redArg(v___y_3141_, v___y_3145_);
lean_dec_ref(v___y_3145_);
lean_inc_n(v___y_3144_, 2);
lean_inc_n(v___y_3142_, 2);
v___x_3147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3147_, 0, v___y_3142_);
lean_ctor_set(v___x_3147_, 1, v___y_3144_);
lean_ctor_set(v___x_3147_, 2, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3148_, 0, v___y_3142_);
lean_ctor_set(v___x_3148_, 1, v___y_3144_);
lean_ctor_set(v___x_3148_, 2, v___y_3141_);
lean_inc(v___y_3129_);
v___x_3149_ = l_Lean_Syntax_node5(v___y_3142_, v___y_3135_, v___y_3124_, v___y_3129_, v___y_3137_, v___x_3147_, v___x_3148_);
v___y_2935_ = v___y_3125_;
v___y_2936_ = v___y_3136_;
v___y_2937_ = v___y_3129_;
v___y_2938_ = v___y_3138_;
v___y_2939_ = v___y_3139_;
v___y_2940_ = v___y_3130_;
v___y_2941_ = v___y_3134_;
v_stxForExecution_2942_ = v___x_3149_;
v___y_2943_ = v___y_3140_;
v___y_2944_ = v___y_3126_;
v___y_2945_ = v___y_3131_;
v___y_2946_ = v___y_3143_;
v___y_2947_ = v___y_3128_;
v___y_2948_ = v___y_3133_;
v___y_2949_ = v___y_3127_;
v___y_2950_ = v___y_3132_;
goto v___jp_2934_;
}
v___jp_3150_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_inc_ref(v___y_3167_);
v___x_3172_ = l_Array_append___redArg(v___y_3167_, v___y_3171_);
lean_dec_ref(v___y_3171_);
lean_inc(v___y_3170_);
lean_inc(v___y_3168_);
v___x_3173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___y_3168_);
lean_ctor_set(v___x_3173_, 1, v___y_3170_);
lean_ctor_set(v___x_3173_, 2, v___x_3172_);
if (lean_obj_tag(v___y_3161_) == 1)
{
lean_object* v_val_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_val_3174_ = lean_ctor_get(v___y_3161_, 0);
v___x_3175_ = l_Lean_SourceInfo_fromRef(v_val_3174_, v___x_2506_);
v___x_3176_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Array_mkArray1___redArg(v___x_3177_);
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v___y_3158_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
v___y_3135_ = v___y_3162_;
v___y_3136_ = v___y_3163_;
v___y_3137_ = v___x_3173_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3166_;
v___y_3140_ = v___y_3165_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3168_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___y_3170_;
v___y_3145_ = v___x_3178_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3179_; 
v___x_3179_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
v___y_3127_ = v___y_3154_;
v___y_3128_ = v___y_3155_;
v___y_3129_ = v___y_3156_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v___y_3158_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
v___y_3135_ = v___y_3162_;
v___y_3136_ = v___y_3163_;
v___y_3137_ = v___x_3173_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3166_;
v___y_3140_ = v___y_3165_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3168_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___y_3170_;
v___y_3145_ = v___x_3179_;
goto v___jp_3123_;
}
}
v___jp_3180_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_inc_ref_n(v___y_3186_, 2);
v___x_3203_ = l_Array_append___redArg(v___y_3186_, v___y_3202_);
lean_dec_ref(v___y_3202_);
lean_inc_n(v___y_3194_, 2);
lean_inc_n(v___y_3200_, 2);
v___x_3204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3204_, 0, v___y_3200_);
lean_ctor_set(v___x_3204_, 1, v___y_3194_);
lean_ctor_set(v___x_3204_, 2, v___x_3203_);
v___x_3205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3205_, 0, v___y_3200_);
lean_ctor_set(v___x_3205_, 1, v___y_3194_);
lean_ctor_set(v___x_3205_, 2, v___y_3186_);
lean_inc(v___y_3185_);
v___x_3206_ = l_Lean_Syntax_node5(v___y_3200_, v___y_3191_, v___y_3187_, v___y_3185_, v___y_3196_, v___x_3204_, v___x_3205_);
v___y_2935_ = v___y_3181_;
v___y_2936_ = v___y_3195_;
v___y_2937_ = v___y_3185_;
v___y_2938_ = v___y_3197_;
v___y_2939_ = v___y_3198_;
v___y_2940_ = v___y_3188_;
v___y_2941_ = v___y_3193_;
v_stxForExecution_2942_ = v___x_3206_;
v___y_2943_ = v___y_3199_;
v___y_2944_ = v___y_3182_;
v___y_2945_ = v___y_3189_;
v___y_2946_ = v___y_3201_;
v___y_2947_ = v___y_3184_;
v___y_2948_ = v___y_3192_;
v___y_2949_ = v___y_3183_;
v___y_2950_ = v___y_3190_;
goto v___jp_2934_;
}
v___jp_3207_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_inc_ref(v___y_3213_);
v___x_3229_ = l_Array_append___redArg(v___y_3213_, v___y_3228_);
lean_dec_ref(v___y_3228_);
lean_inc(v___y_3221_);
lean_inc(v___y_3226_);
v___x_3230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3230_, 0, v___y_3226_);
lean_ctor_set(v___x_3230_, 1, v___y_3221_);
lean_ctor_set(v___x_3230_, 2, v___x_3229_);
if (lean_obj_tag(v___y_3220_) == 1)
{
lean_object* v_val_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_val_3231_ = lean_ctor_get(v___y_3220_, 0);
v___x_3232_ = l_Lean_SourceInfo_fromRef(v_val_3231_, v___x_2506_);
v___x_3233_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_3234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = l_Array_mkArray1___redArg(v___x_3234_);
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___y_3216_;
v___y_3190_ = v___y_3217_;
v___y_3191_ = v___y_3219_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___x_3230_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v___y_3224_;
v___y_3200_ = v___y_3226_;
v___y_3201_ = v___y_3227_;
v___y_3202_ = v___x_3235_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3236_; 
v___x_3236_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3211_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___y_3216_;
v___y_3190_ = v___y_3217_;
v___y_3191_ = v___y_3219_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___x_3230_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v___y_3224_;
v___y_3200_ = v___y_3226_;
v___y_3201_ = v___y_3227_;
v___y_3202_ = v___x_3236_;
goto v___jp_3180_;
}
}
v___jp_3237_:
{
lean_object* v_ref_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_ref_3254_ = lean_ctor_get(v___y_3240_, 2);
v___x_3255_ = l_Lean_SourceInfo_fromRef(v_ref_3254_, v___y_3253_);
v___x_3256_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3257_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3256_);
v___x_3258_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_3259_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3262_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3248_) == 1)
{
lean_object* v_val_3263_; lean_object* v___x_3264_; 
v_val_3263_ = lean_ctor_get(v___y_3248_, 0);
lean_inc(v_val_3263_);
v___x_3264_ = l_Array_mkArray1___redArg(v_val_3263_);
v___y_3029_ = v___y_3238_;
v___y_3030_ = v___y_3239_;
v___y_3031_ = v___x_3262_;
v___y_3032_ = v___y_3240_;
v___y_3033_ = v___y_3241_;
v___y_3034_ = v___y_3242_;
v___y_3035_ = v___x_3261_;
v___y_3036_ = v___y_3243_;
v___y_3037_ = v___y_3244_;
v___y_3038_ = v___y_3245_;
v___y_3039_ = v___y_3246_;
v___y_3040_ = v___y_3247_;
v___y_3041_ = v___x_3255_;
v___y_3042_ = v___y_3248_;
v___y_3043_ = v___y_3249_;
v___y_3044_ = v___x_3260_;
v___y_3045_ = v___y_3251_;
v___y_3046_ = v___y_3250_;
v___y_3047_ = v___x_3257_;
v___y_3048_ = v___y_3252_;
v___y_3049_ = v___x_3264_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3029_ = v___y_3238_;
v___y_3030_ = v___y_3239_;
v___y_3031_ = v___x_3262_;
v___y_3032_ = v___y_3240_;
v___y_3033_ = v___y_3241_;
v___y_3034_ = v___y_3242_;
v___y_3035_ = v___x_3261_;
v___y_3036_ = v___y_3243_;
v___y_3037_ = v___y_3244_;
v___y_3038_ = v___y_3245_;
v___y_3039_ = v___y_3246_;
v___y_3040_ = v___y_3247_;
v___y_3041_ = v___x_3255_;
v___y_3042_ = v___y_3248_;
v___y_3043_ = v___y_3249_;
v___y_3044_ = v___x_3260_;
v___y_3045_ = v___y_3251_;
v___y_3046_ = v___y_3250_;
v___y_3047_ = v___x_3257_;
v___y_3048_ = v___y_3252_;
v___y_3049_ = v___x_3265_;
goto v___jp_3028_;
}
}
v___jp_3266_:
{
lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = lean_array_get_size(v_argsArray_3273_);
v___x_3283_ = lean_nat_dec_eq(v___x_3282_, v___x_2521_);
if (v___x_3283_ == 0)
{
if (lean_obj_tag(v___y_3268_) == 0)
{
v___y_3238_ = v_argsArray_3273_;
v___y_3239_ = v___y_3275_;
v___y_3240_ = v___y_3280_;
v___y_3241_ = v___y_3278_;
v___y_3242_ = v___y_3269_;
v___y_3243_ = v___y_3271_;
v___y_3244_ = v___y_3276_;
v___y_3245_ = v___y_3281_;
v___y_3246_ = v___y_3279_;
v___y_3247_ = v___y_3272_;
v___y_3248_ = v___y_3267_;
v___y_3249_ = v___y_3268_;
v___y_3250_ = v___y_3270_;
v___y_3251_ = v___y_3274_;
v___y_3252_ = v___y_3277_;
v___y_3253_ = v___x_3283_;
goto v___jp_3237_;
}
else
{
if (v___y_3271_ == 0)
{
v___y_3238_ = v_argsArray_3273_;
v___y_3239_ = v___y_3275_;
v___y_3240_ = v___y_3280_;
v___y_3241_ = v___y_3278_;
v___y_3242_ = v___y_3269_;
v___y_3243_ = v___y_3271_;
v___y_3244_ = v___y_3276_;
v___y_3245_ = v___y_3281_;
v___y_3246_ = v___y_3279_;
v___y_3247_ = v___y_3272_;
v___y_3248_ = v___y_3267_;
v___y_3249_ = v___y_3268_;
v___y_3250_ = v___y_3270_;
v___y_3251_ = v___y_3274_;
v___y_3252_ = v___y_3277_;
v___y_3253_ = v___y_3271_;
goto v___jp_3237_;
}
else
{
lean_object* v_ref_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_ref_3284_ = lean_ctor_get(v___y_3280_, 2);
v___x_3285_ = l_Lean_SourceInfo_fromRef(v_ref_3284_, v___x_3283_);
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3287_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3286_);
v___x_3288_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_3289_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3292_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3267_) == 1)
{
lean_object* v_val_3293_; lean_object* v___x_3294_; 
v_val_3293_ = lean_ctor_get(v___y_3267_, 0);
lean_inc(v_val_3293_);
v___x_3294_ = l_Array_mkArray1___redArg(v_val_3293_);
v___y_3094_ = v_argsArray_3273_;
v___y_3095_ = v___y_3275_;
v___y_3096_ = v___y_3280_;
v___y_3097_ = v___y_3278_;
v___y_3098_ = v___y_3269_;
v___y_3099_ = v___x_3292_;
v___y_3100_ = v___y_3271_;
v___y_3101_ = v___x_3290_;
v___y_3102_ = v___y_3276_;
v___y_3103_ = v___y_3281_;
v___y_3104_ = v___y_3279_;
v___y_3105_ = v___y_3272_;
v___y_3106_ = v___x_3285_;
v___y_3107_ = v___x_3287_;
v___y_3108_ = v___y_3267_;
v___y_3109_ = v___y_3268_;
v___y_3110_ = v___y_3274_;
v___y_3111_ = v___y_3270_;
v___y_3112_ = v___y_3277_;
v___y_3113_ = v___x_3291_;
v___y_3114_ = v___x_3294_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3295_; 
v___x_3295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3094_ = v_argsArray_3273_;
v___y_3095_ = v___y_3275_;
v___y_3096_ = v___y_3280_;
v___y_3097_ = v___y_3278_;
v___y_3098_ = v___y_3269_;
v___y_3099_ = v___x_3292_;
v___y_3100_ = v___y_3271_;
v___y_3101_ = v___x_3290_;
v___y_3102_ = v___y_3276_;
v___y_3103_ = v___y_3281_;
v___y_3104_ = v___y_3279_;
v___y_3105_ = v___y_3272_;
v___y_3106_ = v___x_3285_;
v___y_3107_ = v___x_3287_;
v___y_3108_ = v___y_3267_;
v___y_3109_ = v___y_3268_;
v___y_3110_ = v___y_3274_;
v___y_3111_ = v___y_3270_;
v___y_3112_ = v___y_3277_;
v___y_3113_ = v___x_3291_;
v___y_3114_ = v___x_3295_;
goto v___jp_3093_;
}
}
}
}
else
{
if (lean_obj_tag(v___y_3268_) == 0)
{
lean_object* v_ref_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_ref_3296_ = lean_ctor_get(v___y_3280_, 2);
v___x_3297_ = 0;
v___x_3298_ = l_Lean_SourceInfo_fromRef(v_ref_3296_, v___x_3297_);
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3300_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3299_);
v___x_3301_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_3302_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7));
v___x_3303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3305_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3267_) == 1)
{
lean_object* v_val_3306_; lean_object* v___x_3307_; 
v_val_3306_ = lean_ctor_get(v___y_3267_, 0);
lean_inc(v_val_3306_);
v___x_3307_ = l_Array_mkArray1___redArg(v_val_3306_);
v___y_3151_ = v___x_3303_;
v___y_3152_ = v_argsArray_3273_;
v___y_3153_ = v___y_3275_;
v___y_3154_ = v___y_3280_;
v___y_3155_ = v___y_3278_;
v___y_3156_ = v___y_3269_;
v___y_3157_ = v___y_3271_;
v___y_3158_ = v___y_3276_;
v___y_3159_ = v___y_3281_;
v___y_3160_ = v___y_3279_;
v___y_3161_ = v___y_3272_;
v___y_3162_ = v___x_3300_;
v___y_3163_ = v___y_3267_;
v___y_3164_ = v___y_3268_;
v___y_3165_ = v___y_3274_;
v___y_3166_ = v___y_3270_;
v___y_3167_ = v___x_3305_;
v___y_3168_ = v___x_3298_;
v___y_3169_ = v___y_3277_;
v___y_3170_ = v___x_3304_;
v___y_3171_ = v___x_3307_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3151_ = v___x_3303_;
v___y_3152_ = v_argsArray_3273_;
v___y_3153_ = v___y_3275_;
v___y_3154_ = v___y_3280_;
v___y_3155_ = v___y_3278_;
v___y_3156_ = v___y_3269_;
v___y_3157_ = v___y_3271_;
v___y_3158_ = v___y_3276_;
v___y_3159_ = v___y_3281_;
v___y_3160_ = v___y_3279_;
v___y_3161_ = v___y_3272_;
v___y_3162_ = v___x_3300_;
v___y_3163_ = v___y_3267_;
v___y_3164_ = v___y_3268_;
v___y_3165_ = v___y_3274_;
v___y_3166_ = v___y_3270_;
v___y_3167_ = v___x_3305_;
v___y_3168_ = v___x_3298_;
v___y_3169_ = v___y_3277_;
v___y_3170_ = v___x_3304_;
v___y_3171_ = v___x_3308_;
goto v___jp_3150_;
}
}
else
{
lean_object* v_ref_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_ref_3309_ = lean_ctor_get(v___y_3280_, 2);
v___x_3310_ = 0;
v___x_3311_ = l_Lean_SourceInfo_fromRef(v_ref_3309_, v___x_3310_);
v___x_3312_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3313_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3312_);
v___x_3314_ = l_Lean_SourceInfo_fromRef(v_tk_2522_, v___x_2506_);
v___x_3315_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9));
v___x_3316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_3318_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v___y_3267_) == 1)
{
lean_object* v_val_3319_; lean_object* v___x_3320_; 
v_val_3319_ = lean_ctor_get(v___y_3267_, 0);
lean_inc(v_val_3319_);
v___x_3320_ = l_Array_mkArray1___redArg(v_val_3319_);
v___y_3208_ = v_argsArray_3273_;
v___y_3209_ = v___y_3275_;
v___y_3210_ = v___y_3280_;
v___y_3211_ = v___y_3278_;
v___y_3212_ = v___y_3269_;
v___y_3213_ = v___x_3318_;
v___y_3214_ = v___x_3316_;
v___y_3215_ = v___y_3271_;
v___y_3216_ = v___y_3276_;
v___y_3217_ = v___y_3281_;
v___y_3218_ = v___y_3279_;
v___y_3219_ = v___x_3313_;
v___y_3220_ = v___y_3272_;
v___y_3221_ = v___x_3317_;
v___y_3222_ = v___y_3267_;
v___y_3223_ = v___y_3268_;
v___y_3224_ = v___y_3274_;
v___y_3225_ = v___y_3270_;
v___y_3226_ = v___x_3311_;
v___y_3227_ = v___y_3277_;
v___y_3228_ = v___x_3320_;
goto v___jp_3207_;
}
else
{
lean_object* v___x_3321_; 
v___x_3321_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_3208_ = v_argsArray_3273_;
v___y_3209_ = v___y_3275_;
v___y_3210_ = v___y_3280_;
v___y_3211_ = v___y_3278_;
v___y_3212_ = v___y_3269_;
v___y_3213_ = v___x_3318_;
v___y_3214_ = v___x_3316_;
v___y_3215_ = v___y_3271_;
v___y_3216_ = v___y_3276_;
v___y_3217_ = v___y_3281_;
v___y_3218_ = v___y_3279_;
v___y_3219_ = v___x_3313_;
v___y_3220_ = v___y_3272_;
v___y_3221_ = v___x_3317_;
v___y_3222_ = v___y_3267_;
v___y_3223_ = v___y_3268_;
v___y_3224_ = v___y_3274_;
v___y_3225_ = v___y_3270_;
v___y_3226_ = v___x_3311_;
v___y_3227_ = v___y_3277_;
v___y_3228_ = v___x_3321_;
goto v___jp_3207_;
}
}
}
}
v___jp_3322_:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3337_, v___y_3327_, v___y_3330_, v___y_3324_, v___y_3332_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = l_Lean_LibrarySuggestions_select(v_a_3340_, v___y_3338_, v___y_3327_, v___y_3330_, v___y_3324_, v___y_3332_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; size_t v_sz_3343_; size_t v___x_3344_; lean_object* v___x_3345_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v_sz_3343_ = lean_array_size(v_a_3342_);
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_3342_, v_sz_3343_, v___x_3344_, v___y_3326_, v___y_3335_, v___y_3337_, v___y_3329_, v___y_3336_, v___y_3327_, v___y_3330_, v___y_3324_, v___y_3332_);
lean_dec(v_a_3342_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___y_3267_ = v___y_3331_;
v___y_3268_ = v___y_3333_;
v___y_3269_ = v___y_3323_;
v___y_3270_ = v___y_3334_;
v___y_3271_ = v___y_3325_;
v___y_3272_ = v___y_3328_;
v_argsArray_3273_ = v_a_3346_;
v___y_3274_ = v___y_3335_;
v___y_3275_ = v___y_3337_;
v___y_3276_ = v___y_3329_;
v___y_3277_ = v___y_3336_;
v___y_3278_ = v___y_3327_;
v___y_3279_ = v___y_3330_;
v___y_3280_ = v___y_3324_;
v___y_3281_ = v___y_3332_;
goto v___jp_3266_;
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec(v___y_3333_);
lean_dec(v___y_3331_);
lean_dec(v___y_3328_);
lean_dec(v___y_3323_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v_a_3347_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3345_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3345_);
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
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec(v___y_3333_);
lean_dec(v___y_3331_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3323_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v_a_3355_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3341_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3341_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3333_);
lean_dec(v___y_3331_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3323_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v_a_3363_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3339_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3339_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
v___jp_3371_:
{
lean_object* v_config_3388_; uint8_t v_suggestions_3389_; 
v_config_3388_ = lean_ctor_get(v___y_3372_, 0);
lean_inc_ref(v_config_3388_);
lean_dec_ref(v___y_3372_);
v_suggestions_3389_ = lean_ctor_get_uint8(v_config_3388_, sizeof(void*)*3 + 26);
if (v_suggestions_3389_ == 0)
{
lean_dec_ref(v_config_3388_);
lean_dec_ref(v___f_2510_);
v___y_3267_ = v___y_3380_;
v___y_3268_ = v___y_3382_;
v___y_3269_ = v___y_3373_;
v___y_3270_ = v___y_3383_;
v___y_3271_ = v___y_3375_;
v___y_3272_ = v___y_3377_;
v_argsArray_3273_ = v___y_3387_;
v___y_3274_ = v___y_3384_;
v___y_3275_ = v___y_3386_;
v___y_3276_ = v___y_3378_;
v___y_3277_ = v___y_3385_;
v___y_3278_ = v___y_3376_;
v___y_3279_ = v___y_3379_;
v___y_3280_ = v___y_3374_;
v___y_3281_ = v___y_3381_;
goto v___jp_3266_;
}
else
{
lean_object* v_maxSuggestions_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v_maxSuggestions_3390_ = lean_ctor_get(v_config_3388_, 2);
lean_inc(v_maxSuggestions_3390_);
lean_dec_ref(v_config_3388_);
v___x_3391_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10));
v___x_3392_ = lean_box(0);
if (lean_obj_tag(v_maxSuggestions_3390_) == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = lean_unsigned_to_nat(100u);
v___x_3394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___x_3391_);
lean_ctor_set(v___x_3394_, 2, v___f_2510_);
lean_ctor_set(v___x_3394_, 3, v___x_3392_);
v___y_3323_ = v___y_3373_;
v___y_3324_ = v___y_3374_;
v___y_3325_ = v___y_3375_;
v___y_3326_ = v___y_3387_;
v___y_3327_ = v___y_3376_;
v___y_3328_ = v___y_3377_;
v___y_3329_ = v___y_3378_;
v___y_3330_ = v___y_3379_;
v___y_3331_ = v___y_3380_;
v___y_3332_ = v___y_3381_;
v___y_3333_ = v___y_3382_;
v___y_3334_ = v___y_3383_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
v___y_3337_ = v___y_3386_;
v___y_3338_ = v___x_3394_;
goto v___jp_3322_;
}
else
{
lean_object* v_val_3395_; lean_object* v___x_3396_; 
v_val_3395_ = lean_ctor_get(v_maxSuggestions_3390_, 0);
lean_inc(v_val_3395_);
lean_dec_ref_known(v_maxSuggestions_3390_, 1);
v___x_3396_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3396_, 0, v_val_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3391_);
lean_ctor_set(v___x_3396_, 2, v___f_2510_);
lean_ctor_set(v___x_3396_, 3, v___x_3392_);
v___y_3323_ = v___y_3373_;
v___y_3324_ = v___y_3374_;
v___y_3325_ = v___y_3375_;
v___y_3326_ = v___y_3387_;
v___y_3327_ = v___y_3376_;
v___y_3328_ = v___y_3377_;
v___y_3329_ = v___y_3378_;
v___y_3330_ = v___y_3379_;
v___y_3331_ = v___y_3380_;
v___y_3332_ = v___y_3381_;
v___y_3333_ = v___y_3382_;
v___y_3334_ = v___y_3383_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
v___y_3337_ = v___y_3386_;
v___y_3338_ = v___x_3396_;
goto v___jp_3322_;
}
}
}
v___jp_3397_:
{
uint8_t v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = 1;
lean_inc(v___y_3398_);
v___x_3413_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(v___y_3398_, v___x_3412_, v___y_3407_, v___y_3399_, v___y_3405_);
if (lean_obj_tag(v___x_3413_) == 0)
{
if (lean_obj_tag(v___y_3410_) == 1)
{
lean_object* v_a_3414_; lean_object* v_val_3415_; lean_object* v___x_3416_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v_val_3415_ = lean_ctor_get(v___y_3410_, 0);
lean_inc(v_val_3415_);
lean_dec_ref_known(v___y_3410_, 1);
v___x_3416_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3415_);
lean_dec(v_val_3415_);
v___y_3372_ = v_a_3414_;
v___y_3373_ = v___y_3398_;
v___y_3374_ = v___y_3399_;
v___y_3375_ = v___y_3400_;
v___y_3376_ = v___y_3401_;
v___y_3377_ = v___y_3402_;
v___y_3378_ = v___y_3403_;
v___y_3379_ = v___y_3404_;
v___y_3380_ = v___y_3411_;
v___y_3381_ = v___y_3405_;
v___y_3382_ = v___y_3406_;
v___y_3383_ = v___x_3412_;
v___y_3384_ = v___y_3407_;
v___y_3385_ = v___y_3408_;
v___y_3386_ = v___y_3409_;
v___y_3387_ = v___x_3416_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3418_; 
lean_dec(v___y_3410_);
v_a_3417_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3418_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___y_3372_ = v_a_3417_;
v___y_3373_ = v___y_3398_;
v___y_3374_ = v___y_3399_;
v___y_3375_ = v___y_3400_;
v___y_3376_ = v___y_3401_;
v___y_3377_ = v___y_3402_;
v___y_3378_ = v___y_3403_;
v___y_3379_ = v___y_3404_;
v___y_3380_ = v___y_3411_;
v___y_3381_ = v___y_3405_;
v___y_3382_ = v___y_3406_;
v___y_3383_ = v___x_3412_;
v___y_3384_ = v___y_3407_;
v___y_3385_ = v___y_3408_;
v___y_3386_ = v___y_3409_;
v___y_3387_ = v___x_3418_;
goto v___jp_3371_;
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec(v___y_3406_);
lean_dec(v___y_3402_);
lean_dec(v___y_3398_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v_a_3419_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3413_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3413_);
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
v___jp_3427_:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Syntax_getOptional_x3f(v___y_3430_);
lean_dec(v___y_3430_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_box(0);
v___y_3398_ = v___y_3429_;
v___y_3399_ = v___y_3440_;
v___y_3400_ = v___y_3431_;
v___y_3401_ = v___y_3438_;
v___y_3402_ = v___y_3432_;
v___y_3403_ = v___y_3436_;
v___y_3404_ = v___y_3439_;
v___y_3405_ = v___y_3441_;
v___y_3406_ = v___y_3428_;
v___y_3407_ = v___y_3434_;
v___y_3408_ = v___y_3437_;
v___y_3409_ = v___y_3435_;
v___y_3410_ = v_args_3433_;
v___y_3411_ = v___x_3443_;
goto v___jp_3397_;
}
else
{
lean_object* v_val_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_val_3444_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3442_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_val_3444_);
lean_dec(v___x_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_val_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v___y_3398_ = v___y_3429_;
v___y_3399_ = v___y_3440_;
v___y_3400_ = v___y_3431_;
v___y_3401_ = v___y_3438_;
v___y_3402_ = v___y_3432_;
v___y_3403_ = v___y_3436_;
v___y_3404_ = v___y_3439_;
v___y_3405_ = v___y_3441_;
v___y_3406_ = v___y_3428_;
v___y_3407_ = v___y_3434_;
v___y_3408_ = v___y_3437_;
v___y_3409_ = v___y_3435_;
v___y_3410_ = v_args_3433_;
v___y_3411_ = v___x_3449_;
goto v___jp_3397_;
}
}
}
}
v___jp_3453_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3468_ = lean_unsigned_to_nat(3u);
v___x_3469_ = l_Lean_Syntax_getArg(v___y_3458_, v___x_3468_);
lean_dec(v___y_3458_);
v___x_3470_ = l_Lean_Syntax_isNone(v___x_3469_);
if (v___x_3470_ == 0)
{
uint8_t v___x_3471_; 
lean_inc(v___x_3469_);
v___x_3471_ = l_Lean_Syntax_matchesNull(v___x_3469_, v___x_3452_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; 
lean_dec(v___x_3469_);
lean_dec(v_o_3459_);
lean_dec(v___y_3457_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_3472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3472_;
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3473_ = l_Lean_Syntax_getArg(v___x_3469_, v___x_2521_);
lean_dec(v___x_3469_);
v___x_3474_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3475_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3474_);
lean_inc(v___x_3473_);
v___x_3476_ = l_Lean_Syntax_isOfKind(v___x_3473_, v___x_3475_);
lean_dec(v___x_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_dec(v___x_3473_);
lean_dec(v_o_3459_);
lean_dec(v___y_3457_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_3477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3477_;
}
else
{
lean_object* v___x_3478_; lean_object* v_args_3479_; lean_object* v___x_3480_; 
v___x_3478_ = l_Lean_Syntax_getArg(v___x_3473_, v___x_3452_);
lean_dec(v___x_3473_);
v_args_3479_ = l_Lean_Syntax_getArgs(v___x_3478_);
lean_dec(v___x_3478_);
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_args_3479_);
v___y_3428_ = v___y_3455_;
v___y_3429_ = v___y_3454_;
v___y_3430_ = v___y_3457_;
v___y_3431_ = v___y_3456_;
v___y_3432_ = v_o_3459_;
v_args_3433_ = v___x_3480_;
v___y_3434_ = v___y_3460_;
v___y_3435_ = v___y_3461_;
v___y_3436_ = v___y_3462_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3464_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3466_;
v___y_3441_ = v___y_3467_;
goto v___jp_3427_;
}
}
}
else
{
lean_object* v___x_3481_; 
lean_dec(v___x_3469_);
v___x_3481_ = lean_box(0);
v___y_3428_ = v___y_3455_;
v___y_3429_ = v___y_3454_;
v___y_3430_ = v___y_3457_;
v___y_3431_ = v___y_3456_;
v___y_3432_ = v_o_3459_;
v_args_3433_ = v___x_3481_;
v___y_3434_ = v___y_3460_;
v___y_3435_ = v___y_3461_;
v___y_3436_ = v___y_3462_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3464_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3466_;
v___y_3441_ = v___y_3467_;
goto v___jp_3427_;
}
}
v___jp_3482_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3492_ = lean_unsigned_to_nat(2u);
v___x_3493_ = l_Lean_Syntax_getArg(v_stx_2505_, v___x_3492_);
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3495_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3494_);
lean_inc(v___x_3493_);
v___x_3496_ = l_Lean_Syntax_isOfKind(v___x_3493_, v___x_3495_);
lean_dec(v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v___x_3493_);
lean_dec(v_bang_3483_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_3497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3497_;
}
else
{
lean_object* v_cfg_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_cfg_3498_ = l_Lean_Syntax_getArg(v___x_3493_, v___x_2521_);
v___x_3499_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_2509_);
lean_inc_ref(v___x_2508_);
lean_inc_ref(v___x_2507_);
v___x_3500_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_3499_);
lean_inc(v_cfg_3498_);
v___x_3501_ = l_Lean_Syntax_isOfKind(v_cfg_3498_, v___x_3500_);
lean_dec(v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v_cfg_3498_);
lean_dec(v___x_3493_);
lean_dec(v_bang_3483_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_3502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3503_ = l_Lean_Syntax_getArg(v___x_3493_, v___x_3452_);
v___x_3504_ = l_Lean_Syntax_getArg(v___x_3493_, v___x_3492_);
v___x_3505_ = l_Lean_Syntax_isNone(v___x_3504_);
if (v___x_3505_ == 0)
{
uint8_t v___x_3506_; 
lean_inc(v___x_3504_);
v___x_3506_ = l_Lean_Syntax_matchesNull(v___x_3504_, v___x_3452_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v___x_3504_);
lean_dec(v___x_3503_);
lean_dec(v_cfg_3498_);
lean_dec(v___x_3493_);
lean_dec(v_bang_3483_);
lean_dec(v_tk_2522_);
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_3507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3507_;
}
else
{
lean_object* v_o_3508_; lean_object* v___x_3509_; 
v_o_3508_ = l_Lean_Syntax_getArg(v___x_3504_, v___x_2521_);
lean_dec(v___x_3504_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_o_3508_);
v___y_3454_ = v_cfg_3498_;
v___y_3455_ = v_bang_3483_;
v___y_3456_ = v___x_3496_;
v___y_3457_ = v___x_3503_;
v___y_3458_ = v___x_3493_;
v_o_3459_ = v___x_3509_;
v___y_3460_ = v___y_3484_;
v___y_3461_ = v___y_3485_;
v___y_3462_ = v___y_3486_;
v___y_3463_ = v___y_3487_;
v___y_3464_ = v___y_3488_;
v___y_3465_ = v___y_3489_;
v___y_3466_ = v___y_3490_;
v___y_3467_ = v___y_3491_;
goto v___jp_3453_;
}
}
else
{
lean_object* v___x_3510_; 
lean_dec(v___x_3504_);
v___x_3510_ = lean_box(0);
v___y_3454_ = v_cfg_3498_;
v___y_3455_ = v_bang_3483_;
v___y_3456_ = v___x_3496_;
v___y_3457_ = v___x_3503_;
v___y_3458_ = v___x_3493_;
v_o_3459_ = v___x_3510_;
v___y_3460_ = v___y_3484_;
v___y_3461_ = v___y_3485_;
v___y_3462_ = v___y_3486_;
v___y_3463_ = v___y_3487_;
v___y_3464_ = v___y_3488_;
v___y_3465_ = v___y_3489_;
v___y_3466_ = v___y_3490_;
v___y_3467_ = v___y_3491_;
goto v___jp_3453_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(lean_object* v___x_3518_, lean_object* v_stx_3519_, lean_object* v___x_3520_, lean_object* v___x_3521_, lean_object* v___x_3522_, lean_object* v___x_3523_, lean_object* v___f_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
uint8_t v___x_31035__boxed_3534_; uint8_t v___x_31036__boxed_3535_; lean_object* v_res_3536_; 
v___x_31035__boxed_3534_ = lean_unbox(v___x_3518_);
v___x_31036__boxed_3535_ = lean_unbox(v___x_3520_);
v_res_3536_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(v___x_31035__boxed_3534_, v_stx_3519_, v___x_31036__boxed_3535_, v___x_3521_, v___x_3522_, v___x_3523_, v___f_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_stx_3519_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* v_stx_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; uint8_t v___x_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___y_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_3554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_3555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_3556_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
lean_inc(v_stx_3543_);
v___x_3557_ = l_Lean_Syntax_isOfKind(v_stx_3543_, v___x_3556_);
v___x_3558_ = 1;
v___f_3559_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___closed__2));
v___x_3560_ = lean_box(v___x_3557_);
v___x_3561_ = lean_box(v___x_3558_);
v___y_3562_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed), 16, 7);
lean_closure_set(v___y_3562_, 0, v___x_3560_);
lean_closure_set(v___y_3562_, 1, v_stx_3543_);
lean_closure_set(v___y_3562_, 2, v___x_3561_);
lean_closure_set(v___y_3562_, 3, v___x_3553_);
lean_closure_set(v___y_3562_, 4, v___x_3554_);
lean_closure_set(v___y_3562_, 5, v___x_3555_);
lean_closure_set(v___y_3562_, 6, v___f_3559_);
v___x_3563_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3563_, 0, v___y_3562_);
v___x_3564_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3563_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* v_stx_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Elab_Tactic_evalSimpAllTrace(v_stx_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(lean_object* v___x_3576_, lean_object* v_as_3577_, lean_object* v_as_x27_3578_, lean_object* v_b_3579_, lean_object* v_a_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_3576_, v_as_x27_3578_, v_b_3579_, v___y_3587_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(lean_object* v___x_3591_, lean_object* v_as_3592_, lean_object* v_as_x27_3593_, lean_object* v_b_3594_, lean_object* v_a_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(v___x_3591_, v_as_3592_, v_as_x27_3593_, v_b_3594_, v_a_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v_as_x27_3593_);
lean_dec(v_as_3592_);
lean_dec(v___x_3591_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3613_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3614_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1));
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3616_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
v___x_3617_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3613_, v___x_3614_, v___x_3615_, v___x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1));
v___x_3646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6));
v___x_3647_ = l_Lean_addBuiltinDeclarationRanges(v___x_3645_, v___x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* v_ctx_3650_, lean_object* v_simprocs_3651_, lean_object* v_fvarIdsToSimp_3652_, uint8_t v_simplifyTarget_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v___x_3662_ = lean_unsigned_to_nat(32u);
v___x_3663_ = lean_mk_empty_array_with_capacity(v___x_3662_);
lean_dec_ref(v___x_3663_);
v___x_3664_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5, &l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5);
v___x_3665_ = l_Lean_Meta_dsimpGoal(v_a_3661_, v_ctx_3650_, v_simprocs_3651_, v_simplifyTarget_3653_, v_fvarIdsToSimp_3652_, v___x_3664_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v_fst_3667_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v_fst_3667_ = lean_ctor_get(v_a_3666_, 0);
if (lean_obj_tag(v_fst_3667_) == 0)
{
lean_object* v_snd_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_snd_3668_ = lean_ctor_get(v_a_3666_, 1);
lean_inc(v_snd_3668_);
lean_dec(v_a_3666_);
v___x_3669_ = lean_box(0);
v___x_3670_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3669_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v___x_3670_, 0);
lean_dec(v_unused_3678_);
v___x_3672_ = v___x_3670_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v___x_3670_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_snd_3668_);
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_snd_3668_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_snd_3668_);
v_a_3679_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3670_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3670_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_object* v_snd_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3713_; 
lean_inc_ref(v_fst_3667_);
v_snd_3687_ = lean_ctor_get(v_a_3666_, 1);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_a_3666_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; 
v_unused_3714_ = lean_ctor_get(v_a_3666_, 0);
lean_dec(v_unused_3714_);
v___x_3689_ = v_a_3666_;
v_isShared_3690_ = v_isSharedCheck_3713_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_snd_3687_);
lean_dec(v_a_3666_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3713_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_val_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v_val_3691_ = lean_ctor_get(v_fst_3667_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_fst_3667_, 1);
v___x_3692_ = lean_box(0);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 1);
lean_ctor_set(v___x_3689_, 1, v___x_3692_);
lean_ctor_set(v___x_3689_, 0, v_val_3691_);
v___x_3694_ = v___x_3689_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_val_3691_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3694_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; 
v_unused_3703_ = lean_ctor_get(v___x_3695_, 0);
lean_dec(v_unused_3703_);
v___x_3697_ = v___x_3695_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_dec(v___x_3695_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v_snd_3687_);
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_snd_3687_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_snd_3687_);
v_a_3704_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3695_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3695_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
v_a_3715_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3665_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3665_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_fvarIdsToSimp_3652_);
lean_dec_ref(v_simprocs_3651_);
lean_dec_ref(v_ctx_3650_);
v_a_3723_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3660_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3660_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* v_ctx_3731_, lean_object* v_simprocs_3732_, lean_object* v_fvarIdsToSimp_3733_, lean_object* v_simplifyTarget_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
uint8_t v_simplifyTarget_boxed_3741_; lean_object* v_res_3742_; 
v_simplifyTarget_boxed_3741_ = lean_unbox(v_simplifyTarget_3734_);
v_res_3742_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3731_, v_simprocs_3732_, v_fvarIdsToSimp_3733_, v_simplifyTarget_boxed_3741_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* v_ctx_3743_, lean_object* v_simprocs_3744_, lean_object* v_fvarIdsToSimp_3745_, uint8_t v_simplifyTarget_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3743_, v_simprocs_3744_, v_fvarIdsToSimp_3745_, v_simplifyTarget_3746_, v_a_3748_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* v_ctx_3757_, lean_object* v_simprocs_3758_, lean_object* v_fvarIdsToSimp_3759_, lean_object* v_simplifyTarget_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
uint8_t v_simplifyTarget_boxed_3770_; lean_object* v_res_3771_; 
v_simplifyTarget_boxed_3770_ = lean_unbox(v_simplifyTarget_3760_);
v_res_3771_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(v_ctx_3757_, v_simprocs_3758_, v_fvarIdsToSimp_3759_, v_simplifyTarget_boxed_3770_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* v_ctx_3772_, lean_object* v_simprocs_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3775_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = l_Lean_MVarId_getNondepPropHyps(v_a_3784_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; uint8_t v___x_3787_; lean_object* v___x_3788_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = 1;
v___x_3788_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3772_, v_simprocs_3773_, v_a_3786_, v___x_3787_, v___y_3775_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
return v___x_3788_;
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref(v_simprocs_3773_);
lean_dec_ref(v_ctx_3772_);
v_a_3789_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3785_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3785_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_simprocs_3773_);
lean_dec_ref(v_ctx_3772_);
v_a_3797_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3783_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3783_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* v_ctx_3805_, lean_object* v_simprocs_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(v_ctx_3805_, v_simprocs_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* v_hypotheses_3817_, lean_object* v_ctx_3818_, lean_object* v_simprocs_3819_, uint8_t v_type_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3817_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v___x_3832_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_3818_, v_simprocs_3819_, v_a_3831_, v_type_3820_, v___y_3822_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3832_;
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v_simprocs_3819_);
lean_dec_ref(v_ctx_3818_);
v_a_3833_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3830_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3830_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* v_hypotheses_3841_, lean_object* v_ctx_3842_, lean_object* v_simprocs_3843_, lean_object* v_type_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
uint8_t v_type_638__boxed_3854_; lean_object* v_res_3855_; 
v_type_638__boxed_3854_ = lean_unbox(v_type_3844_);
v_res_3855_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(v_hypotheses_3841_, v_ctx_3842_, v_simprocs_3843_, v_type_638__boxed_3854_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* v_ctx_3856_, lean_object* v_simprocs_3857_, lean_object* v_loc_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
if (lean_obj_tag(v_loc_3858_) == 0)
{
lean_object* v___f_3868_; lean_object* v___x_3869_; 
v___f_3868_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3868_, 0, v_ctx_3856_);
lean_closure_set(v___f_3868_, 1, v_simprocs_3857_);
v___x_3869_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3868_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
return v___x_3869_;
}
else
{
lean_object* v_hypotheses_3870_; uint8_t v_type_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; 
v_hypotheses_3870_ = lean_ctor_get(v_loc_3858_, 0);
lean_inc_ref(v_hypotheses_3870_);
v_type_3871_ = lean_ctor_get_uint8(v_loc_3858_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_3858_, 1);
v___x_3872_ = lean_box(v_type_3871_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3873_, 0, v_hypotheses_3870_);
lean_closure_set(v___f_3873_, 1, v_ctx_3856_);
lean_closure_set(v___f_3873_, 2, v_simprocs_3857_);
lean_closure_set(v___f_3873_, 3, v___x_3872_);
v___x_3874_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3873_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* v_ctx_3875_, lean_object* v_simprocs_3876_, lean_object* v_loc_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v_ctx_3875_, v_simprocs_3876_, v_loc_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t v___x_3892_, lean_object* v_stx_3893_, uint8_t v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v___x_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
if (v___x_3892_ == 0)
{
lean_object* v___x_3907_; 
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_3907_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_3907_;
}
else
{
lean_object* v___x_3908_; lean_object* v_tk_3909_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; uint8_t v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v_stx_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; uint8_t v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; uint8_t v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; uint8_t v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; uint8_t v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; uint8_t v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; uint8_t v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; uint8_t v___y_4214_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; uint8_t v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; uint8_t v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v_args_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___x_4290_; uint8_t v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v_o_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v_bang_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_3908_ = lean_unsigned_to_nat(0u);
v_tk_3909_ = l_Lean_Syntax_getArg(v_stx_3893_, v___x_3908_);
v___x_4290_ = lean_unsigned_to_nat(1u);
v___x_4347_ = l_Lean_Syntax_getArg(v_stx_3893_, v___x_4290_);
v___x_4348_ = l_Lean_Syntax_isNone(v___x_4347_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
lean_inc(v___x_4347_);
v___x_4349_ = l_Lean_Syntax_matchesNull(v___x_4347_, v___x_4290_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
lean_dec(v___x_4347_);
lean_dec(v_tk_3909_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_4350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4350_;
}
else
{
lean_object* v_bang_4351_; lean_object* v___x_4352_; 
v_bang_4351_ = l_Lean_Syntax_getArg(v___x_4347_, v___x_3908_);
lean_dec(v___x_4347_);
v___x_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4352_, 0, v_bang_4351_);
v_bang_4320_ = v___x_4352_;
v___y_4321_ = v___y_3898_;
v___y_4322_ = v___y_3899_;
v___y_4323_ = v___y_3900_;
v___y_4324_ = v___y_3901_;
v___y_4325_ = v___y_3902_;
v___y_4326_ = v___y_3903_;
v___y_4327_ = v___y_3904_;
v___y_4328_ = v___y_3905_;
goto v___jp_4319_;
}
}
else
{
lean_object* v___x_4353_; 
lean_dec(v___x_4347_);
v___x_4353_ = lean_box(0);
v_bang_4320_ = v___x_4353_;
v___y_4321_ = v___y_3898_;
v___y_4322_ = v___y_3899_;
v___y_4323_ = v___y_3900_;
v___y_4324_ = v___y_3901_;
v___y_4325_ = v___y_3902_;
v___y_4326_ = v___y_3903_;
v___y_4327_ = v___y_3904_;
v___y_4328_ = v___y_3905_;
goto v___jp_4319_;
}
v___jp_3910_:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_Elab_Tactic_dsimpLocation_x27(v___y_3919_, v___y_3913_, v___y_3922_, v___y_3912_, v___y_3918_, v___y_3917_, v___y_3921_, v___y_3911_, v___y_3916_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v_usedTheorems_3925_; lean_object* v_diag_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3968_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v_usedTheorems_3925_ = lean_ctor_get(v_a_3924_, 0);
v_diag_3926_ = lean_ctor_get(v_a_3924_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_a_3924_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3928_ = v_a_3924_;
v_isShared_3929_ = v_isSharedCheck_3968_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_diag_3926_);
lean_inc(v_usedTheorems_3925_);
lean_dec(v_a_3924_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3968_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___y_3920_, v_usedTheorems_3925_, v___y_3911_, v___y_3916_, v___y_3914_, v___y_3915_);
lean_dec_ref(v_usedTheorems_3925_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v_ref_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
v_ref_3932_ = lean_ctor_get(v___y_3914_, 2);
v___x_3933_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1));
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 1, v_a_3931_);
lean_ctor_set(v___x_3928_, 0, v___x_3933_);
v___x_3935_ = v___x_3928_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_a_3931_);
v___x_3935_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3936_ = lean_box(0);
v___x_3937_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
lean_ctor_set(v___x_3937_, 2, v___x_3936_);
lean_ctor_set(v___x_3937_, 3, v___x_3936_);
lean_ctor_set(v___x_3937_, 4, v___x_3936_);
lean_ctor_set(v___x_3937_, 5, v___x_3936_);
lean_inc(v_ref_3932_);
v___x_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_ref_3932_);
v___x_3939_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2));
v___x_3940_ = 4;
v___x_3941_ = l_Lean_MessageData_nil;
v___x_3942_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_3909_, v___x_3937_, v___x_3938_, v___x_3939_, v___x_3936_, v___x_3940_, v___x_3941_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; 
v_unused_3950_ = lean_ctor_get(v___x_3942_, 0);
lean_dec(v_unused_3950_);
v___x_3944_ = v___x_3942_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_dec(v___x_3942_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v_diag_3926_);
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_diag_3926_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec_ref(v_diag_3926_);
v_a_3951_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3942_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3942_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_del_object(v___x_3928_);
lean_dec_ref(v_diag_3926_);
lean_dec(v_tk_3909_);
v_a_3960_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3930_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3930_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v___y_3920_);
lean_dec(v_tk_3909_);
v_a_3969_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3923_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3923_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
v___jp_3977_:
{
if (lean_obj_tag(v___y_3987_) == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = ((lean_object*)(l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0));
v___x_3991_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set_uint8(v___x_3991_, sizeof(void*)*1, v___x_3894_);
v___y_3911_ = v___y_3980_;
v___y_3912_ = v___y_3979_;
v___y_3913_ = v___y_3978_;
v___y_3914_ = v___y_3981_;
v___y_3915_ = v___y_3983_;
v___y_3916_ = v___y_3982_;
v___y_3917_ = v___y_3984_;
v___y_3918_ = v___y_3985_;
v___y_3919_ = v___y_3989_;
v___y_3920_ = v___y_3986_;
v___y_3921_ = v___y_3988_;
v___y_3922_ = v___x_3991_;
goto v___jp_3910_;
}
else
{
lean_object* v_val_3992_; lean_object* v___x_3993_; 
v_val_3992_ = lean_ctor_get(v___y_3987_, 0);
lean_inc(v_val_3992_);
lean_dec_ref_known(v___y_3987_, 1);
v___x_3993_ = l_Lean_Elab_Tactic_expandLocation(v_val_3992_);
lean_dec(v_val_3992_);
v___y_3911_ = v___y_3980_;
v___y_3912_ = v___y_3979_;
v___y_3913_ = v___y_3978_;
v___y_3914_ = v___y_3981_;
v___y_3915_ = v___y_3983_;
v___y_3916_ = v___y_3982_;
v___y_3917_ = v___y_3984_;
v___y_3918_ = v___y_3985_;
v___y_3919_ = v___y_3989_;
v___y_3920_ = v___y_3986_;
v___y_3921_ = v___y_3988_;
v___y_3922_ = v___x_3993_;
goto v___jp_3910_;
}
}
v___jp_3994_:
{
uint8_t v___x_4007_; uint8_t v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4007_ = 0;
v___x_4008_ = 2;
v___x_4009_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3));
v___x_4010_ = lean_box(v___x_4007_);
v___x_4011_ = lean_box(v___x_4008_);
v___x_4012_ = lean_box(v___x_4007_);
lean_inc(v_stx_3998_);
v___x_4013_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_4013_, 0, v_stx_3998_);
lean_closure_set(v___x_4013_, 1, v___x_4010_);
lean_closure_set(v___x_4013_, 2, v___x_4011_);
lean_closure_set(v___x_4013_, 3, v___x_4012_);
lean_closure_set(v___x_4013_, 4, v___x_4009_);
v___x_4014_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4013_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
if (lean_obj_tag(v___y_3997_) == 0)
{
lean_object* v_ctx_4016_; lean_object* v_simprocs_4017_; 
v_ctx_4016_ = lean_ctor_get(v_a_4015_, 0);
lean_inc_ref(v_ctx_4016_);
v_simprocs_4017_ = lean_ctor_get(v_a_4015_, 1);
lean_inc_ref(v_simprocs_4017_);
lean_dec(v_a_4015_);
v___y_3978_ = v_simprocs_4017_;
v___y_3979_ = v___y_3999_;
v___y_3980_ = v___y_4003_;
v___y_3981_ = v___y_4005_;
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___y_4006_;
v___y_3984_ = v___y_4001_;
v___y_3985_ = v___y_4000_;
v___y_3986_ = v_stx_3998_;
v___y_3987_ = v___y_3996_;
v___y_3988_ = v___y_4002_;
v___y_3989_ = v_ctx_4016_;
goto v___jp_3977_;
}
else
{
lean_dec_ref_known(v___y_3997_, 1);
if (v___y_3995_ == 0)
{
lean_object* v_ctx_4018_; lean_object* v_simprocs_4019_; 
v_ctx_4018_ = lean_ctor_get(v_a_4015_, 0);
lean_inc_ref(v_ctx_4018_);
v_simprocs_4019_ = lean_ctor_get(v_a_4015_, 1);
lean_inc_ref(v_simprocs_4019_);
lean_dec(v_a_4015_);
v___y_3978_ = v_simprocs_4019_;
v___y_3979_ = v___y_3999_;
v___y_3980_ = v___y_4003_;
v___y_3981_ = v___y_4005_;
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___y_4006_;
v___y_3984_ = v___y_4001_;
v___y_3985_ = v___y_4000_;
v___y_3986_ = v_stx_3998_;
v___y_3987_ = v___y_3996_;
v___y_3988_ = v___y_4002_;
v___y_3989_ = v_ctx_4018_;
goto v___jp_3977_;
}
else
{
lean_object* v_ctx_4020_; lean_object* v_simprocs_4021_; lean_object* v___x_4022_; 
v_ctx_4020_ = lean_ctor_get(v_a_4015_, 0);
lean_inc_ref(v_ctx_4020_);
v_simprocs_4021_ = lean_ctor_get(v_a_4015_, 1);
lean_inc_ref(v_simprocs_4021_);
lean_dec(v_a_4015_);
v___x_4022_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_4020_);
v___y_3978_ = v_simprocs_4021_;
v___y_3979_ = v___y_3999_;
v___y_3980_ = v___y_4003_;
v___y_3981_ = v___y_4005_;
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___y_4006_;
v___y_3984_ = v___y_4001_;
v___y_3985_ = v___y_4000_;
v___y_3986_ = v_stx_3998_;
v___y_3987_ = v___y_3996_;
v___y_3988_ = v___y_4002_;
v___y_3989_ = v___x_4022_;
goto v___jp_3977_;
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec(v_stx_3998_);
lean_dec(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec(v_tk_3909_);
v_a_4023_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4014_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4014_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
v___jp_4031_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_inc_ref(v___y_4050_);
v___x_4053_ = l_Array_append___redArg(v___y_4050_, v___y_4052_);
lean_dec_ref(v___y_4052_);
lean_inc(v___y_4039_);
lean_inc(v___y_4044_);
v___x_4054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4054_, 0, v___y_4044_);
lean_ctor_set(v___x_4054_, 1, v___y_4039_);
lean_ctor_set(v___x_4054_, 2, v___x_4053_);
v___x_4055_ = l_Lean_Syntax_node6(v___y_4044_, v___y_4036_, v___y_4051_, v___y_4045_, v___y_4032_, v___y_4033_, v___y_4049_, v___x_4054_);
v___y_3995_ = v___y_4041_;
v___y_3996_ = v___y_4048_;
v___y_3997_ = v___y_4038_;
v_stx_3998_ = v___x_4055_;
v___y_3999_ = v___y_4035_;
v___y_4000_ = v___y_4046_;
v___y_4001_ = v___y_4042_;
v___y_4002_ = v___y_4043_;
v___y_4003_ = v___y_4047_;
v___y_4004_ = v___y_4040_;
v___y_4005_ = v___y_4037_;
v___y_4006_ = v___y_4034_;
goto v___jp_3994_;
}
v___jp_4056_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_inc_ref(v___y_4075_);
v___x_4077_ = l_Array_append___redArg(v___y_4075_, v___y_4076_);
lean_dec_ref(v___y_4076_);
lean_inc(v___y_4063_);
lean_inc(v___y_4069_);
v___x_4078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4078_, 0, v___y_4069_);
lean_ctor_set(v___x_4078_, 1, v___y_4063_);
lean_ctor_set(v___x_4078_, 2, v___x_4077_);
if (lean_obj_tag(v___y_4073_) == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___y_4058_;
v___y_4034_ = v___y_4059_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4061_;
v___y_4037_ = v___y_4062_;
v___y_4038_ = v___y_4064_;
v___y_4039_ = v___y_4063_;
v___y_4040_ = v___y_4065_;
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4067_;
v___y_4043_ = v___y_4066_;
v___y_4044_ = v___y_4069_;
v___y_4045_ = v___y_4070_;
v___y_4046_ = v___y_4071_;
v___y_4047_ = v___y_4072_;
v___y_4048_ = v___y_4073_;
v___y_4049_ = v___x_4078_;
v___y_4050_ = v___y_4075_;
v___y_4051_ = v___y_4074_;
v___y_4052_ = v___x_4079_;
goto v___jp_4031_;
}
else
{
lean_object* v_val_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v_val_4080_ = lean_ctor_get(v___y_4073_, 0);
v___x_4081_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4080_);
v___x_4082_ = lean_array_push(v___x_4081_, v_val_4080_);
v___y_4032_ = v___y_4057_;
v___y_4033_ = v___y_4058_;
v___y_4034_ = v___y_4059_;
v___y_4035_ = v___y_4060_;
v___y_4036_ = v___y_4061_;
v___y_4037_ = v___y_4062_;
v___y_4038_ = v___y_4064_;
v___y_4039_ = v___y_4063_;
v___y_4040_ = v___y_4065_;
v___y_4041_ = v___y_4068_;
v___y_4042_ = v___y_4067_;
v___y_4043_ = v___y_4066_;
v___y_4044_ = v___y_4069_;
v___y_4045_ = v___y_4070_;
v___y_4046_ = v___y_4071_;
v___y_4047_ = v___y_4072_;
v___y_4048_ = v___y_4073_;
v___y_4049_ = v___x_4078_;
v___y_4050_ = v___y_4075_;
v___y_4051_ = v___y_4074_;
v___y_4052_ = v___x_4082_;
goto v___jp_4031_;
}
}
v___jp_4083_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
lean_inc_ref(v___y_4101_);
v___x_4104_ = l_Array_append___redArg(v___y_4101_, v___y_4103_);
lean_dec_ref(v___y_4103_);
lean_inc(v___y_4089_);
lean_inc(v___y_4095_);
v___x_4105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4105_, 0, v___y_4095_);
lean_ctor_set(v___x_4105_, 1, v___y_4089_);
lean_ctor_set(v___x_4105_, 2, v___x_4104_);
if (lean_obj_tag(v___y_4102_) == 1)
{
lean_object* v_val_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v_val_4106_ = lean_ctor_get(v___y_4102_, 0);
lean_inc(v_val_4106_);
lean_dec_ref_known(v___y_4102_, 1);
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4095_, 3);
v___x_4108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___y_4095_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
lean_inc_ref(v___y_4101_);
v___x_4109_ = l_Array_append___redArg(v___y_4101_, v_val_4106_);
lean_dec(v_val_4106_);
lean_inc(v___y_4089_);
v___x_4110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4110_, 0, v___y_4095_);
lean_ctor_set(v___x_4110_, 1, v___y_4089_);
lean_ctor_set(v___x_4110_, 2, v___x_4109_);
v___x_4111_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___y_4095_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = l_Array_mkArray3___redArg(v___x_4108_, v___x_4110_, v___x_4112_);
v___y_4057_ = v___y_4084_;
v___y_4058_ = v___x_4105_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___y_4087_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___y_4089_;
v___y_4064_ = v___y_4090_;
v___y_4065_ = v___y_4091_;
v___y_4066_ = v___y_4093_;
v___y_4067_ = v___y_4094_;
v___y_4068_ = v___y_4092_;
v___y_4069_ = v___y_4095_;
v___y_4070_ = v___y_4096_;
v___y_4071_ = v___y_4097_;
v___y_4072_ = v___y_4098_;
v___y_4073_ = v___y_4099_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___y_4101_;
v___y_4076_ = v___x_4113_;
goto v___jp_4056_;
}
else
{
lean_object* v___x_4114_; 
lean_dec(v___y_4102_);
v___x_4114_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4057_ = v___y_4084_;
v___y_4058_ = v___x_4105_;
v___y_4059_ = v___y_4085_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___y_4087_;
v___y_4062_ = v___y_4088_;
v___y_4063_ = v___y_4089_;
v___y_4064_ = v___y_4090_;
v___y_4065_ = v___y_4091_;
v___y_4066_ = v___y_4093_;
v___y_4067_ = v___y_4094_;
v___y_4068_ = v___y_4092_;
v___y_4069_ = v___y_4095_;
v___y_4070_ = v___y_4096_;
v___y_4071_ = v___y_4097_;
v___y_4072_ = v___y_4098_;
v___y_4073_ = v___y_4099_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___y_4101_;
v___y_4076_ = v___x_4114_;
goto v___jp_4056_;
}
}
v___jp_4115_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
lean_inc_ref(v___y_4119_);
v___x_4137_ = l_Array_append___redArg(v___y_4119_, v___y_4136_);
lean_dec_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc(v___y_4121_);
v___x_4138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4138_, 0, v___y_4121_);
lean_ctor_set(v___x_4138_, 1, v___y_4135_);
lean_ctor_set(v___x_4138_, 2, v___x_4137_);
v___x_4139_ = l_Lean_Syntax_node6(v___y_4121_, v___y_4130_, v___y_4118_, v___y_4128_, v___y_4120_, v___y_4134_, v___y_4129_, v___x_4138_);
v___y_3995_ = v___y_4125_;
v___y_3996_ = v___y_4133_;
v___y_3997_ = v___y_4123_;
v_stx_3998_ = v___x_4139_;
v___y_3999_ = v___y_4117_;
v___y_4000_ = v___y_4131_;
v___y_4001_ = v___y_4126_;
v___y_4002_ = v___y_4127_;
v___y_4003_ = v___y_4132_;
v___y_4004_ = v___y_4124_;
v___y_4005_ = v___y_4122_;
v___y_4006_ = v___y_4116_;
goto v___jp_3994_;
}
v___jp_4140_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_inc_ref(v___y_4144_);
v___x_4161_ = l_Array_append___redArg(v___y_4144_, v___y_4160_);
lean_dec_ref(v___y_4160_);
lean_inc(v___y_4159_);
lean_inc(v___y_4146_);
v___x_4162_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4162_, 0, v___y_4146_);
lean_ctor_set(v___x_4162_, 1, v___y_4159_);
lean_ctor_set(v___x_4162_, 2, v___x_4161_);
if (lean_obj_tag(v___y_4157_) == 0)
{
lean_object* v___x_4163_; 
v___x_4163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4142_;
v___y_4118_ = v___y_4143_;
v___y_4119_ = v___y_4144_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___y_4149_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___y_4152_;
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___y_4153_;
v___y_4129_ = v___x_4162_;
v___y_4130_ = v___y_4155_;
v___y_4131_ = v___y_4154_;
v___y_4132_ = v___y_4156_;
v___y_4133_ = v___y_4157_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___y_4159_;
v___y_4136_ = v___x_4163_;
goto v___jp_4115_;
}
else
{
lean_object* v_val_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_val_4164_ = lean_ctor_get(v___y_4157_, 0);
v___x_4165_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
lean_inc(v_val_4164_);
v___x_4166_ = lean_array_push(v___x_4165_, v_val_4164_);
v___y_4116_ = v___y_4141_;
v___y_4117_ = v___y_4142_;
v___y_4118_ = v___y_4143_;
v___y_4119_ = v___y_4144_;
v___y_4120_ = v___y_4145_;
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___y_4149_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___y_4152_;
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___y_4153_;
v___y_4129_ = v___x_4162_;
v___y_4130_ = v___y_4155_;
v___y_4131_ = v___y_4154_;
v___y_4132_ = v___y_4156_;
v___y_4133_ = v___y_4157_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___y_4159_;
v___y_4136_ = v___x_4166_;
goto v___jp_4115_;
}
}
v___jp_4167_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
lean_inc_ref(v___y_4171_);
v___x_4188_ = l_Array_append___redArg(v___y_4171_, v___y_4187_);
lean_dec_ref(v___y_4187_);
lean_inc(v___y_4185_);
lean_inc(v___y_4173_);
v___x_4189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4189_, 0, v___y_4173_);
lean_ctor_set(v___x_4189_, 1, v___y_4185_);
lean_ctor_set(v___x_4189_, 2, v___x_4188_);
if (lean_obj_tag(v___y_4186_) == 1)
{
lean_object* v_val_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_val_4190_ = lean_ctor_get(v___y_4186_, 0);
lean_inc(v_val_4190_);
lean_dec_ref_known(v___y_4186_, 1);
v___x_4191_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4));
lean_inc_n(v___y_4173_, 3);
v___x_4192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___y_4173_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
lean_inc_ref(v___y_4171_);
v___x_4193_ = l_Array_append___redArg(v___y_4171_, v_val_4190_);
lean_dec(v_val_4190_);
lean_inc(v___y_4185_);
v___x_4194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4194_, 0, v___y_4173_);
lean_ctor_set(v___x_4194_, 1, v___y_4185_);
lean_ctor_set(v___x_4194_, 2, v___x_4193_);
v___x_4195_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6));
v___x_4196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___y_4173_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Array_mkArray3___redArg(v___x_4192_, v___x_4194_, v___x_4196_);
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___y_4174_;
v___y_4148_ = v___y_4175_;
v___y_4149_ = v___y_4176_;
v___y_4150_ = v___y_4178_;
v___y_4151_ = v___y_4179_;
v___y_4152_ = v___y_4177_;
v___y_4153_ = v___y_4180_;
v___y_4154_ = v___y_4182_;
v___y_4155_ = v___y_4181_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___y_4184_;
v___y_4158_ = v___x_4189_;
v___y_4159_ = v___y_4185_;
v___y_4160_ = v___x_4197_;
goto v___jp_4140_;
}
else
{
lean_object* v___x_4198_; 
lean_dec(v___y_4186_);
v___x_4198_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4141_ = v___y_4168_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4170_;
v___y_4144_ = v___y_4171_;
v___y_4145_ = v___y_4172_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___y_4174_;
v___y_4148_ = v___y_4175_;
v___y_4149_ = v___y_4176_;
v___y_4150_ = v___y_4178_;
v___y_4151_ = v___y_4179_;
v___y_4152_ = v___y_4177_;
v___y_4153_ = v___y_4180_;
v___y_4154_ = v___y_4182_;
v___y_4155_ = v___y_4181_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___y_4184_;
v___y_4158_ = v___x_4189_;
v___y_4159_ = v___y_4185_;
v___y_4160_ = v___x_4198_;
goto v___jp_4140_;
}
}
v___jp_4199_:
{
lean_object* v_ref_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v_ref_4215_ = lean_ctor_get(v___y_4203_, 2);
v___x_4216_ = l_Lean_SourceInfo_fromRef(v_ref_4215_, v___y_4214_);
v___x_4217_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0));
v___x_4218_ = l_Lean_Name_mkStr4(v___x_3895_, v___x_3896_, v___x_3897_, v___x_4217_);
v___x_4219_ = l_Lean_SourceInfo_fromRef(v_tk_3909_, v___x_3894_);
v___x_4220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
lean_ctor_set(v___x_4220_, 1, v___x_4217_);
v___x_4221_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4222_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4216_);
v___x_4223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4216_);
lean_ctor_set(v___x_4223_, 1, v___x_4221_);
lean_ctor_set(v___x_4223_, 2, v___x_4222_);
if (lean_obj_tag(v___y_4200_) == 1)
{
lean_object* v_val_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v_val_4224_ = lean_ctor_get(v___y_4200_, 0);
lean_inc(v_val_4224_);
lean_dec_ref_known(v___y_4200_, 1);
v___x_4225_ = l_Lean_SourceInfo_fromRef(v_val_4224_, v___x_3894_);
lean_dec(v_val_4224_);
v___x_4226_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4225_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
v___x_4228_ = l_Array_mkArray1___redArg(v___x_4227_);
v___y_4084_ = v___x_4223_;
v___y_4085_ = v___y_4201_;
v___y_4086_ = v___y_4202_;
v___y_4087_ = v___x_4218_;
v___y_4088_ = v___y_4203_;
v___y_4089_ = v___x_4221_;
v___y_4090_ = v___y_4204_;
v___y_4091_ = v___y_4205_;
v___y_4092_ = v___y_4206_;
v___y_4093_ = v___y_4207_;
v___y_4094_ = v___y_4208_;
v___y_4095_ = v___x_4216_;
v___y_4096_ = v___y_4209_;
v___y_4097_ = v___y_4210_;
v___y_4098_ = v___y_4211_;
v___y_4099_ = v___y_4212_;
v___y_4100_ = v___x_4220_;
v___y_4101_ = v___x_4222_;
v___y_4102_ = v___y_4213_;
v___y_4103_ = v___x_4228_;
goto v___jp_4083_;
}
else
{
lean_object* v___x_4229_; 
lean_dec(v___y_4200_);
v___x_4229_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4084_ = v___x_4223_;
v___y_4085_ = v___y_4201_;
v___y_4086_ = v___y_4202_;
v___y_4087_ = v___x_4218_;
v___y_4088_ = v___y_4203_;
v___y_4089_ = v___x_4221_;
v___y_4090_ = v___y_4204_;
v___y_4091_ = v___y_4205_;
v___y_4092_ = v___y_4206_;
v___y_4093_ = v___y_4207_;
v___y_4094_ = v___y_4208_;
v___y_4095_ = v___x_4216_;
v___y_4096_ = v___y_4209_;
v___y_4097_ = v___y_4210_;
v___y_4098_ = v___y_4211_;
v___y_4099_ = v___y_4212_;
v___y_4100_ = v___x_4220_;
v___y_4101_ = v___x_4222_;
v___y_4102_ = v___y_4213_;
v___y_4103_ = v___x_4229_;
goto v___jp_4083_;
}
}
v___jp_4230_:
{
if (lean_obj_tag(v___y_4235_) == 0)
{
uint8_t v___x_4245_; 
v___x_4245_ = 0;
v___y_4200_ = v___y_4231_;
v___y_4201_ = v___y_4232_;
v___y_4202_ = v___y_4233_;
v___y_4203_ = v___y_4234_;
v___y_4204_ = v___y_4235_;
v___y_4205_ = v___y_4236_;
v___y_4206_ = v___y_4237_;
v___y_4207_ = v___y_4238_;
v___y_4208_ = v___y_4239_;
v___y_4209_ = v___y_4240_;
v___y_4210_ = v___y_4241_;
v___y_4211_ = v___y_4242_;
v___y_4212_ = v___y_4244_;
v___y_4213_ = v___y_4243_;
v___y_4214_ = v___x_4245_;
goto v___jp_4199_;
}
else
{
if (v___y_4237_ == 0)
{
v___y_4200_ = v___y_4231_;
v___y_4201_ = v___y_4232_;
v___y_4202_ = v___y_4233_;
v___y_4203_ = v___y_4234_;
v___y_4204_ = v___y_4235_;
v___y_4205_ = v___y_4236_;
v___y_4206_ = v___y_4237_;
v___y_4207_ = v___y_4238_;
v___y_4208_ = v___y_4239_;
v___y_4209_ = v___y_4240_;
v___y_4210_ = v___y_4241_;
v___y_4211_ = v___y_4242_;
v___y_4212_ = v___y_4244_;
v___y_4213_ = v___y_4243_;
v___y_4214_ = v___y_4237_;
goto v___jp_4199_;
}
else
{
lean_object* v_ref_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_ref_4246_ = lean_ctor_get(v___y_4234_, 2);
v___x_4247_ = 0;
v___x_4248_ = l_Lean_SourceInfo_fromRef(v_ref_4246_, v___x_4247_);
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1));
v___x_4250_ = l_Lean_Name_mkStr4(v___x_3895_, v___x_3896_, v___x_3897_, v___x_4249_);
v___x_4251_ = l_Lean_SourceInfo_fromRef(v_tk_3909_, v___x_3894_);
v___x_4252_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2));
v___x_4253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4251_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3));
v___x_4255_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
lean_inc(v___x_4248_);
v___x_4256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4248_);
lean_ctor_set(v___x_4256_, 1, v___x_4254_);
lean_ctor_set(v___x_4256_, 2, v___x_4255_);
if (lean_obj_tag(v___y_4231_) == 1)
{
lean_object* v_val_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_val_4257_ = lean_ctor_get(v___y_4231_, 0);
lean_inc(v_val_4257_);
lean_dec_ref_known(v___y_4231_, 1);
v___x_4258_ = l_Lean_SourceInfo_fromRef(v_val_4257_, v___x_3894_);
lean_dec(v_val_4257_);
v___x_4259_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8));
v___x_4260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Array_mkArray1___redArg(v___x_4260_);
v___y_4168_ = v___y_4232_;
v___y_4169_ = v___y_4233_;
v___y_4170_ = v___x_4253_;
v___y_4171_ = v___x_4255_;
v___y_4172_ = v___x_4256_;
v___y_4173_ = v___x_4248_;
v___y_4174_ = v___y_4234_;
v___y_4175_ = v___y_4235_;
v___y_4176_ = v___y_4236_;
v___y_4177_ = v___y_4239_;
v___y_4178_ = v___y_4238_;
v___y_4179_ = v___y_4237_;
v___y_4180_ = v___y_4240_;
v___y_4181_ = v___x_4250_;
v___y_4182_ = v___y_4241_;
v___y_4183_ = v___y_4242_;
v___y_4184_ = v___y_4244_;
v___y_4185_ = v___x_4254_;
v___y_4186_ = v___y_4243_;
v___y_4187_ = v___x_4261_;
goto v___jp_4167_;
}
else
{
lean_object* v___x_4262_; 
lean_dec(v___y_4231_);
v___x_4262_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7));
v___y_4168_ = v___y_4232_;
v___y_4169_ = v___y_4233_;
v___y_4170_ = v___x_4253_;
v___y_4171_ = v___x_4255_;
v___y_4172_ = v___x_4256_;
v___y_4173_ = v___x_4248_;
v___y_4174_ = v___y_4234_;
v___y_4175_ = v___y_4235_;
v___y_4176_ = v___y_4236_;
v___y_4177_ = v___y_4239_;
v___y_4178_ = v___y_4238_;
v___y_4179_ = v___y_4237_;
v___y_4180_ = v___y_4240_;
v___y_4181_ = v___x_4250_;
v___y_4182_ = v___y_4241_;
v___y_4183_ = v___y_4242_;
v___y_4184_ = v___y_4244_;
v___y_4185_ = v___x_4254_;
v___y_4186_ = v___y_4243_;
v___y_4187_ = v___x_4262_;
goto v___jp_4167_;
}
}
}
}
v___jp_4263_:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = lean_unsigned_to_nat(3u);
v___x_4279_ = l_Lean_Syntax_getArg(v___y_4267_, v___x_4278_);
lean_dec(v___y_4267_);
v___x_4280_ = l_Lean_Syntax_getOptional_x3f(v___x_4279_);
lean_dec(v___x_4279_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_box(0);
v___y_4231_ = v___y_4265_;
v___y_4232_ = v___y_4277_;
v___y_4233_ = v___y_4270_;
v___y_4234_ = v___y_4276_;
v___y_4235_ = v___y_4268_;
v___y_4236_ = v___y_4275_;
v___y_4237_ = v___y_4264_;
v___y_4238_ = v___y_4273_;
v___y_4239_ = v___y_4272_;
v___y_4240_ = v___y_4266_;
v___y_4241_ = v___y_4271_;
v___y_4242_ = v___y_4274_;
v___y_4243_ = v_args_4269_;
v___y_4244_ = v___x_4281_;
goto v___jp_4230_;
}
else
{
lean_object* v_val_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
v_val_4282_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4280_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_val_4282_);
lean_dec(v___x_4280_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_val_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
v___y_4231_ = v___y_4265_;
v___y_4232_ = v___y_4277_;
v___y_4233_ = v___y_4270_;
v___y_4234_ = v___y_4276_;
v___y_4235_ = v___y_4268_;
v___y_4236_ = v___y_4275_;
v___y_4237_ = v___y_4264_;
v___y_4238_ = v___y_4273_;
v___y_4239_ = v___y_4272_;
v___y_4240_ = v___y_4266_;
v___y_4241_ = v___y_4271_;
v___y_4242_ = v___y_4274_;
v___y_4243_ = v_args_4269_;
v___y_4244_ = v___x_4287_;
goto v___jp_4230_;
}
}
}
}
v___jp_4291_:
{
lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4306_ = l_Lean_Syntax_getArg(v___y_4295_, v___y_4293_);
v___x_4307_ = l_Lean_Syntax_isNone(v___x_4306_);
if (v___x_4307_ == 0)
{
uint8_t v___x_4308_; 
lean_inc(v___x_4306_);
v___x_4308_ = l_Lean_Syntax_matchesNull(v___x_4306_, v___x_4290_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
lean_dec(v___x_4306_);
lean_dec(v_o_4297_);
lean_dec(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec(v_tk_3909_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_4309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4309_;
}
else
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4310_ = l_Lean_Syntax_getArg(v___x_4306_, v___x_3908_);
lean_dec(v___x_4306_);
v___x_4311_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11));
lean_inc_ref(v___x_3897_);
lean_inc_ref(v___x_3896_);
lean_inc_ref(v___x_3895_);
v___x_4312_ = l_Lean_Name_mkStr4(v___x_3895_, v___x_3896_, v___x_3897_, v___x_4311_);
lean_inc(v___x_4310_);
v___x_4313_ = l_Lean_Syntax_isOfKind(v___x_4310_, v___x_4312_);
lean_dec(v___x_4312_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; 
lean_dec(v___x_4310_);
lean_dec(v_o_4297_);
lean_dec(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec(v_tk_3909_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_4314_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4314_;
}
else
{
lean_object* v___x_4315_; lean_object* v_args_4316_; lean_object* v___x_4317_; 
v___x_4315_ = l_Lean_Syntax_getArg(v___x_4310_, v___x_4290_);
lean_dec(v___x_4310_);
v_args_4316_ = l_Lean_Syntax_getArgs(v___x_4315_);
lean_dec(v___x_4315_);
v___x_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4317_, 0, v_args_4316_);
v___y_4264_ = v___y_4292_;
v___y_4265_ = v_o_4297_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v___y_4268_ = v___y_4296_;
v_args_4269_ = v___x_4317_;
v___y_4270_ = v___y_4298_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4300_;
v___y_4273_ = v___y_4301_;
v___y_4274_ = v___y_4302_;
v___y_4275_ = v___y_4303_;
v___y_4276_ = v___y_4304_;
v___y_4277_ = v___y_4305_;
goto v___jp_4263_;
}
}
}
else
{
lean_object* v___x_4318_; 
lean_dec(v___x_4306_);
v___x_4318_ = lean_box(0);
v___y_4264_ = v___y_4292_;
v___y_4265_ = v_o_4297_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v___y_4268_ = v___y_4296_;
v_args_4269_ = v___x_4318_;
v___y_4270_ = v___y_4298_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4300_;
v___y_4273_ = v___y_4301_;
v___y_4274_ = v___y_4302_;
v___y_4275_ = v___y_4303_;
v___y_4276_ = v___y_4304_;
v___y_4277_ = v___y_4305_;
goto v___jp_4263_;
}
}
v___jp_4319_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4329_ = lean_unsigned_to_nat(2u);
v___x_4330_ = l_Lean_Syntax_getArg(v_stx_3893_, v___x_4329_);
v___x_4331_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3));
lean_inc_ref(v___x_3897_);
lean_inc_ref(v___x_3896_);
lean_inc_ref(v___x_3895_);
v___x_4332_ = l_Lean_Name_mkStr4(v___x_3895_, v___x_3896_, v___x_3897_, v___x_4331_);
lean_inc(v___x_4330_);
v___x_4333_ = l_Lean_Syntax_isOfKind(v___x_4330_, v___x_4332_);
lean_dec(v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_dec(v___x_4330_);
lean_dec(v_bang_4320_);
lean_dec(v_tk_3909_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_4334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4335_ = l_Lean_Syntax_getArg(v___x_4330_, v___x_3908_);
v___x_4336_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15));
lean_inc_ref(v___x_3897_);
lean_inc_ref(v___x_3896_);
lean_inc_ref(v___x_3895_);
v___x_4337_ = l_Lean_Name_mkStr4(v___x_3895_, v___x_3896_, v___x_3897_, v___x_4336_);
lean_inc(v___x_4335_);
v___x_4338_ = l_Lean_Syntax_isOfKind(v___x_4335_, v___x_4337_);
lean_dec(v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; 
lean_dec(v___x_4335_);
lean_dec(v___x_4330_);
lean_dec(v_bang_4320_);
lean_dec(v_tk_3909_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_4339_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4339_;
}
else
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = l_Lean_Syntax_getArg(v___x_4330_, v___x_4290_);
v___x_4341_ = l_Lean_Syntax_isNone(v___x_4340_);
if (v___x_4341_ == 0)
{
uint8_t v___x_4342_; 
lean_inc(v___x_4340_);
v___x_4342_ = l_Lean_Syntax_matchesNull(v___x_4340_, v___x_4290_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; 
lean_dec(v___x_4340_);
lean_dec(v___x_4335_);
lean_dec(v___x_4330_);
lean_dec(v_bang_4320_);
lean_dec(v_tk_3909_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
v___x_4343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
return v___x_4343_;
}
else
{
lean_object* v_o_4344_; lean_object* v___x_4345_; 
v_o_4344_ = l_Lean_Syntax_getArg(v___x_4340_, v___x_3908_);
lean_dec(v___x_4340_);
v___x_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4345_, 0, v_o_4344_);
v___y_4292_ = v___x_4333_;
v___y_4293_ = v___x_4329_;
v___y_4294_ = v___x_4335_;
v___y_4295_ = v___x_4330_;
v___y_4296_ = v_bang_4320_;
v_o_4297_ = v___x_4345_;
v___y_4298_ = v___y_4321_;
v___y_4299_ = v___y_4322_;
v___y_4300_ = v___y_4323_;
v___y_4301_ = v___y_4324_;
v___y_4302_ = v___y_4325_;
v___y_4303_ = v___y_4326_;
v___y_4304_ = v___y_4327_;
v___y_4305_ = v___y_4328_;
goto v___jp_4291_;
}
}
else
{
lean_object* v___x_4346_; 
lean_dec(v___x_4340_);
v___x_4346_ = lean_box(0);
v___y_4292_ = v___x_4333_;
v___y_4293_ = v___x_4329_;
v___y_4294_ = v___x_4335_;
v___y_4295_ = v___x_4330_;
v___y_4296_ = v_bang_4320_;
v_o_4297_ = v___x_4346_;
v___y_4298_ = v___y_4321_;
v___y_4299_ = v___y_4322_;
v___y_4300_ = v___y_4323_;
v___y_4301_ = v___y_4324_;
v___y_4302_ = v___y_4325_;
v___y_4303_ = v___y_4326_;
v___y_4304_ = v___y_4327_;
v___y_4305_ = v___y_4328_;
goto v___jp_4291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* v___x_4354_, lean_object* v_stx_4355_, lean_object* v___x_4356_, lean_object* v___x_4357_, lean_object* v___x_4358_, lean_object* v___x_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
uint8_t v___x_8025__boxed_4369_; uint8_t v___x_8026__boxed_4370_; lean_object* v_res_4371_; 
v___x_8025__boxed_4369_ = lean_unbox(v___x_4354_);
v___x_8026__boxed_4370_ = lean_unbox(v___x_4356_);
v_res_4371_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(v___x_8025__boxed_4369_, v_stx_4355_, v___x_8026__boxed_4370_, v___x_4357_, v___x_4358_, v___x_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v_stx_4355_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* v_stx_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___y_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0));
v___x_4389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1));
v___x_4390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2));
v___x_4391_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
lean_inc(v_stx_4378_);
v___x_4392_ = l_Lean_Syntax_isOfKind(v_stx_4378_, v___x_4391_);
v___x_4393_ = 1;
v___x_4394_ = lean_box(v___x_4392_);
v___x_4395_ = lean_box(v___x_4393_);
v___y_4396_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_4396_, 0, v___x_4394_);
lean_closure_set(v___y_4396_, 1, v_stx_4378_);
lean_closure_set(v___y_4396_, 2, v___x_4395_);
lean_closure_set(v___y_4396_, 3, v___x_4388_);
lean_closure_set(v___y_4396_, 4, v___x_4389_);
lean_closure_set(v___y_4396_, 5, v___x_4390_);
v___x_4397_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_4397_, 0, v___y_4396_);
v___x_4398_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_4397_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* v_stx_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_Elab_Tactic_evalDSimpTrace(v_stx_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4417_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4418_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1));
v___x_4419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4420_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
v___x_4421_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4417_, v___x_4418_, v___x_4419_, v___x_4420_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(lean_object* v_a_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1));
v___x_4451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6));
v___x_4452_ = l_Lean_addBuiltinDeclarationRanges(v___x_4450_, v___x_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
return v_res_4454_;
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
