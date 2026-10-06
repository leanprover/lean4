// Lean compiler output
// Module: Lean.IdentifierSuggestion
// Imports: public import Lean.Elab.DeclModifiers import all Lean.Elab.ErrorUtils import Init.Omega
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value;
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value;
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value;
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "identifierSuggestForAttr"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "existingToIncorrect"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_0),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value),LEAN_SCALAR_PTR_LITERAL(152, 194, 183, 202, 227, 26, 150, 37)}};
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_1),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6_value),LEAN_SCALAR_PTR_LITERAL(133, 152, 34, 126, 5, 52, 99, 232)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value;
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value;
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "incorrectToExisting"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_0),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value),LEAN_SCALAR_PTR_LITERAL(152, 194, 183, 202, 227, 26, 150, 37)}};
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_1),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 186, 146, 149, 115, 54, 93, 158)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Cannot make suggestions for private names"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid `[suggest_for]` attribute syntax "};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IdentifierSuggestion"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 155, 139, 72, 6, 50, 200, 229)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(95, 73, 25, 53, 228, 16, 190, 220)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value),LEAN_SCALAR_PTR_LITERAL(18, 130, 57, 193, 85, 113, 17, 183)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "identifierSuggestionsImpl"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 49, 207, 254, 142, 38, 130, 211)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggest_for"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 123, 198, 36, 120, 51, 50, 116)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "suggest other (incorrect, not-existing) identifiers that someone might use when they actually want this definition"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
static const lean_array_object l_Lean_getSuggestions___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__6_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__7_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_getSuggestions___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__3_value)}};
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_getSuggestions___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__9_value),((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__5_value),((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__6_value),((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__7_value)}};
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__10 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_getSuggestions___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__10_value),((lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__8_value)}};
static const lean_object* l_Lean_getSuggestions___redArg___lam__1___closed__11 = (const lean_object*)&l_Lean_getSuggestions___redArg___lam__1___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___closed__0 = (const lean_object*)&l_Lean_getSuggestions___redArg___closed__0_value;
static const lean_closure_object l_Lean_getSuggestions___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___closed__1 = (const lean_object*)&l_Lean_getSuggestions___redArg___closed__1_value;
static lean_once_cell_t l_Lean_getSuggestions___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getSuggestions___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Change to "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Unknown "};
static const lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3;
static const lean_string_object l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Perhaps you meant "};
static const lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4 = (const lean_object*)&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5;
static const lean_string_object l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6 = (const lean_object*)&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7;
static const lean_string_object l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " in place of `"};
static const lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8 = (const lean_object*)&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9;
static const lean_string_object l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "one of these"};
static const lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10 = (const lean_object*)&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10_value;
static lean_once_cell_t l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "• `"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "The identifier `"};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 181, .m_capacity = 181, .m_length = 180, .m_data = "` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be "};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", and "};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = " is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement."};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Perhaps you meant `"};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in place of `"};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`\?"};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Perhaps you meant one of these in place of `"};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16;
static const lean_string_object l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; size_t v___x_8_; size_t v___x_9_; 
v___x_6_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
lean_inc(v___x_6_);
v___x_7_ = l_Lean_NameSet_insert(v_b_4_, v___x_6_);
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_2_, v___x_8_);
v_i_2_ = v___x_9_;
v_b_4_ = v___x_7_;
goto _start;
}
else
{
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4___boxed(lean_object* v_as_11_, lean_object* v_i_12_, lean_object* v_stop_13_, lean_object* v_b_14_){
_start:
{
size_t v_i_boxed_15_; size_t v_stop_boxed_16_; lean_object* v_res_17_; 
v_i_boxed_15_ = lean_unbox_usize(v_i_12_);
lean_dec(v_i_12_);
v_stop_boxed_16_ = lean_unbox_usize(v_stop_13_);
lean_dec(v_stop_13_);
v_res_17_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_as_11_, v_i_boxed_15_, v_stop_boxed_16_, v_b_14_);
lean_dec_ref(v_as_11_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(lean_object* v_snd_18_, lean_object* v_old_19_){
_start:
{
lean_object* v___y_21_; 
if (lean_obj_tag(v_old_19_) == 0)
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_NameSet_empty;
v___y_21_ = v___x_36_;
goto v___jp_20_;
}
else
{
lean_object* v_val_37_; 
v_val_37_ = lean_ctor_get(v_old_19_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v_old_19_, 1);
v___y_21_ = v_val_37_;
goto v___jp_20_;
}
v___jp_20_:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_get_size(v_snd_18_);
v___x_24_ = lean_nat_dec_lt(v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v___y_21_);
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = lean_nat_dec_le(v___x_23_, v___x_23_);
if (v___x_26_ == 0)
{
if (v___x_24_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v___y_21_);
return v___x_27_;
}
else
{
size_t v___x_28_; size_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = ((size_t)0ULL);
v___x_29_ = lean_usize_of_nat(v___x_23_);
v___x_30_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_18_, v___x_28_, v___x_29_, v___y_21_);
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
else
{
size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = ((size_t)0ULL);
v___x_33_ = lean_usize_of_nat(v___x_23_);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_18_, v___x_32_, v___x_33_, v___y_21_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0___boxed(lean_object* v_snd_38_, lean_object* v_old_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_38_, v_old_39_);
lean_dec_ref(v_snd_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(lean_object* v_snd_41_, lean_object* v_k_42_, lean_object* v_t_43_){
_start:
{
if (lean_obj_tag(v_t_43_) == 0)
{
lean_object* v_size_44_; lean_object* v_k_45_; lean_object* v_v_46_; lean_object* v_l_47_; lean_object* v_r_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_63_; 
v_size_44_ = lean_ctor_get(v_t_43_, 0);
v_k_45_ = lean_ctor_get(v_t_43_, 1);
v_v_46_ = lean_ctor_get(v_t_43_, 2);
v_l_47_ = lean_ctor_get(v_t_43_, 3);
v_r_48_ = lean_ctor_get(v_t_43_, 4);
v_isSharedCheck_63_ = !lean_is_exclusive(v_t_43_);
if (v_isSharedCheck_63_ == 0)
{
v___x_50_ = v_t_43_;
v_isShared_51_ = v_isSharedCheck_63_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_r_48_);
lean_inc(v_l_47_);
lean_inc(v_v_46_);
lean_inc(v_k_45_);
lean_inc(v_size_44_);
lean_dec(v_t_43_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_63_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
uint8_t v___x_52_; 
v___x_52_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_42_, v_k_45_);
switch(v___x_52_)
{
case 0:
{
lean_object* v_impl_53_; lean_object* v___x_54_; 
lean_del_object(v___x_50_);
lean_dec(v_size_44_);
v_impl_53_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_41_, v_k_42_, v_l_47_);
v___x_54_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_45_, v_v_46_, v_impl_53_, v_r_48_);
return v___x_54_;
}
case 1:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_val_57_; lean_object* v___x_59_; 
lean_dec(v_k_45_);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_v_46_);
v___x_56_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_41_, v___x_55_);
v_val_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_val_57_);
lean_dec(v___x_56_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v_val_57_);
lean_ctor_set(v___x_50_, 1, v_k_42_);
v___x_59_ = v___x_50_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_size_44_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_k_42_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_val_57_);
lean_ctor_set(v_reuseFailAlloc_60_, 3, v_l_47_);
lean_ctor_set(v_reuseFailAlloc_60_, 4, v_r_48_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
default: 
{
lean_object* v_impl_61_; lean_object* v___x_62_; 
lean_del_object(v___x_50_);
lean_dec(v_size_44_);
v_impl_61_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_41_, v_k_42_, v_r_48_);
v___x_62_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_45_, v_v_46_, v_l_47_, v_impl_61_);
return v___x_62_;
}
}
}
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_val_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_64_ = lean_box(0);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_41_, v___x_64_);
v_val_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_val_66_);
lean_dec(v___x_65_);
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_k_42_);
lean_ctor_set(v___x_68_, 2, v_val_66_);
lean_ctor_set(v___x_68_, 3, v_t_43_);
lean_ctor_set(v___x_68_, 4, v_t_43_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___boxed(lean_object* v_snd_69_, lean_object* v_k_70_, lean_object* v_t_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_69_, v_k_70_, v_t_71_);
lean_dec_ref(v_snd_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__0(lean_object* v_table_73_, lean_object* v_x_74_){
_start:
{
lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v___x_77_; 
v_fst_75_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_fst_75_);
v_snd_76_ = lean_ctor_get(v_x_74_, 1);
lean_inc(v_snd_76_);
lean_dec_ref(v_x_74_);
v___x_77_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_76_, v_fst_75_, v_table_73_);
lean_dec(v_snd_76_);
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(lean_object* v_a_78_, lean_object* v_b_79_){
_start:
{
lean_object* v_fst_80_; lean_object* v_fst_81_; uint8_t v___x_82_; 
v_fst_80_ = lean_ctor_get(v_a_78_, 0);
v_fst_81_ = lean_ctor_get(v_b_79_, 0);
v___x_82_ = l_Lean_Name_quickLt(v_fst_80_, v_fst_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed(lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_83_, v_b_84_);
lean_dec_ref(v_b_84_);
lean_dec_ref(v_a_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(lean_object* v_hi_87_, lean_object* v_pivot_88_, lean_object* v_as_89_, lean_object* v_i_90_, lean_object* v_k_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_lt(v_k_91_, v_hi_87_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_k_91_);
v___x_93_ = lean_array_fswap(v_as_89_, v_i_90_, v_hi_87_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_i_90_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; lean_object* v_fst_96_; lean_object* v_fst_97_; uint8_t v___x_98_; 
v___x_95_ = lean_array_fget_borrowed(v_as_89_, v_k_91_);
v_fst_96_ = lean_ctor_get(v___x_95_, 0);
v_fst_97_ = lean_ctor_get(v_pivot_88_, 0);
v___x_98_ = l_Lean_Name_quickLt(v_fst_96_, v_fst_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_k_91_, v___x_99_);
lean_dec(v_k_91_);
v_k_91_ = v___x_100_;
goto _start;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_array_fswap(v_as_89_, v_i_90_, v_k_91_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_90_, v___x_103_);
lean_dec(v_i_90_);
v___x_105_ = lean_nat_add(v_k_91_, v___x_103_);
lean_dec(v_k_91_);
v_as_89_ = v___x_102_;
v_i_90_ = v___x_104_;
v_k_91_ = v___x_105_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg___boxed(lean_object* v_hi_107_, lean_object* v_pivot_108_, lean_object* v_as_109_, lean_object* v_i_110_, lean_object* v_k_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_107_, v_pivot_108_, v_as_109_, v_i_110_, v_k_111_);
lean_dec_ref(v_pivot_108_);
lean_dec(v_hi_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(lean_object* v_n_113_, lean_object* v_as_114_, lean_object* v_lo_115_, lean_object* v_hi_116_){
_start:
{
lean_object* v___y_118_; uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_lt(v_lo_115_, v_hi_116_);
if (v___x_128_ == 0)
{
lean_dec(v_lo_115_);
return v_as_114_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_mid_131_; lean_object* v___y_133_; lean_object* v___y_139_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_129_ = lean_nat_add(v_lo_115_, v_hi_116_);
v___x_130_ = lean_unsigned_to_nat(1u);
v_mid_131_ = lean_nat_shiftr(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v___x_144_ = lean_array_fget_borrowed(v_as_114_, v_mid_131_);
v___x_145_ = lean_array_fget_borrowed(v_as_114_, v_lo_115_);
v___x_146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
v___y_139_ = v_as_114_;
goto v___jp_138_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_array_fswap(v_as_114_, v_lo_115_, v_mid_131_);
v___y_139_ = v___x_147_;
goto v___jp_138_;
}
v___jp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = lean_array_fget_borrowed(v___y_133_, v_mid_131_);
v___x_135_ = lean_array_fget_borrowed(v___y_133_, v_hi_116_);
v___x_136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec(v_mid_131_);
v___y_118_ = v___y_133_;
goto v___jp_117_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_array_fswap(v___y_133_, v_mid_131_, v_hi_116_);
lean_dec(v_mid_131_);
v___y_118_ = v___x_137_;
goto v___jp_117_;
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = lean_array_fget_borrowed(v___y_139_, v_hi_116_);
v___x_141_ = lean_array_fget_borrowed(v___y_139_, v_lo_115_);
v___x_142_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
v___y_133_ = v___y_139_;
goto v___jp_132_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_array_fswap(v___y_139_, v_lo_115_, v_hi_116_);
v___y_133_ = v___x_143_;
goto v___jp_132_;
}
}
}
v___jp_117_:
{
lean_object* v_pivot_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; uint8_t v___x_123_; 
v_pivot_119_ = lean_array_fget(v___y_118_, v_hi_116_);
lean_inc_n(v_lo_115_, 2);
v___x_120_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_116_, v_pivot_119_, v___y_118_, v_lo_115_, v_lo_115_);
lean_dec(v_pivot_119_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_nat_dec_le(v_hi_116_, v_fst_121_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_113_, v_snd_122_, v_lo_115_, v_fst_121_);
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_fst_121_, v___x_125_);
lean_dec(v_fst_121_);
v_as_114_ = v___x_124_;
v_lo_115_ = v___x_126_;
goto _start;
}
else
{
lean_dec(v_fst_121_);
lean_dec(v_lo_115_);
return v_snd_122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___boxed(lean_object* v_n_148_, lean_object* v_as_149_, lean_object* v_lo_150_, lean_object* v_hi_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_148_, v_as_149_, v_lo_150_, v_hi_151_);
lean_dec(v_hi_151_);
lean_dec(v_n_148_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(lean_object* v_init_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v_k_155_; lean_object* v_l_156_; lean_object* v_r_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_k_155_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_k_155_);
v_l_156_ = lean_ctor_get(v_x_154_, 3);
lean_inc(v_l_156_);
v_r_157_ = lean_ctor_get(v_x_154_, 4);
lean_inc(v_r_157_);
lean_dec_ref_known(v_x_154_, 5);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_153_, v_l_156_);
v___x_159_ = lean_array_push(v___x_158_, v_k_155_);
v_init_153_ = v___x_159_;
v_x_154_ = v_r_157_;
goto _start;
}
else
{
return v_init_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(size_t v_sz_161_, size_t v_i_162_, lean_object* v_bs_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_164_ == 0)
{
return v_bs_163_;
}
else
{
lean_object* v_v_165_; lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_185_; 
v_v_165_ = lean_array_uget(v_bs_163_, v_i_162_);
v_fst_166_ = lean_ctor_get(v_v_165_, 0);
v_snd_167_ = lean_ctor_get(v_v_165_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_v_165_);
if (v_isSharedCheck_185_ == 0)
{
v___x_169_ = v_v_165_;
v_isShared_170_ = v_isSharedCheck_185_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snd_167_);
lean_inc(v_fst_166_);
lean_dec(v_v_165_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_185_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v_bs_x27_172_; lean_object* v___y_174_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v_bs_x27_172_ = lean_array_uset(v_bs_163_, v_i_162_, v___x_171_);
if (lean_obj_tag(v_snd_167_) == 0)
{
lean_object* v_size_184_; 
v_size_184_ = lean_ctor_get(v_snd_167_, 0);
lean_inc(v_size_184_);
v___y_174_ = v_size_184_;
goto v___jp_173_;
}
else
{
v___y_174_ = v___x_171_;
goto v___jp_173_;
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_175_ = lean_mk_empty_array_with_capacity(v___y_174_);
lean_dec(v___y_174_);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_175_, v_snd_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v___x_176_);
v___x_178_ = v___x_169_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_fst_166_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_183_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
size_t v___x_179_; size_t v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_add(v_i_162_, v___x_179_);
v___x_181_ = lean_array_uset(v_bs_x27_172_, v_i_162_, v___x_178_);
v_i_162_ = v___x_180_;
v_bs_163_ = v___x_181_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2___boxed(lean_object* v_sz_186_, lean_object* v_i_187_, lean_object* v_bs_188_){
_start:
{
size_t v_sz_boxed_189_; size_t v_i_boxed_190_; lean_object* v_res_191_; 
v_sz_boxed_189_ = lean_unbox_usize(v_sz_186_);
lean_dec(v_sz_186_);
v_i_boxed_190_ = lean_unbox_usize(v_i_187_);
lean_dec(v_i_187_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_boxed_189_, v_i_boxed_190_, v_bs_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(lean_object* v_init_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v_k_194_; lean_object* v_v_195_; lean_object* v_l_196_; lean_object* v_r_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_k_194_ = lean_ctor_get(v_x_193_, 1);
v_v_195_ = lean_ctor_get(v_x_193_, 2);
v_l_196_ = lean_ctor_get(v_x_193_, 3);
v_r_197_ = lean_ctor_get(v_x_193_, 4);
v___x_198_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_192_, v_l_196_);
lean_inc(v_v_195_);
lean_inc(v_k_194_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_k_194_);
lean_ctor_set(v___x_199_, 1, v_v_195_);
v___x_200_ = lean_array_push(v___x_198_, v___x_199_);
v_init_192_ = v___x_200_;
v_x_193_ = v_r_197_;
goto _start;
}
else
{
return v_init_192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2___boxed(lean_object* v_init_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_202_, v_x_203_);
lean_dec(v_x_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(lean_object* v_x_207_, lean_object* v_s_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; size_t v_sz_212_; size_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___y_217_; lean_object* v___y_218_; uint8_t v___x_221_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0));
v___x_211_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_210_, v_s_208_);
v_sz_212_ = lean_array_size(v___x_211_);
v___x_213_ = ((size_t)0ULL);
v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_212_, v___x_213_, v___x_211_);
v___x_215_ = lean_array_get_size(v___x_214_);
v___x_221_ = lean_nat_dec_eq(v___x_215_, v___x_209_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___y_225_; uint8_t v___x_227_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v___x_215_, v___x_222_);
v___x_227_ = lean_nat_dec_le(v___x_209_, v___x_223_);
if (v___x_227_ == 0)
{
lean_inc(v___x_223_);
v___y_225_ = v___x_223_;
goto v___jp_224_;
}
else
{
v___y_225_ = v___x_209_;
goto v___jp_224_;
}
v___jp_224_:
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_le(v___y_225_, v___x_223_);
if (v___x_226_ == 0)
{
lean_dec(v___x_223_);
lean_inc(v___y_225_);
v___y_217_ = v___y_225_;
v___y_218_ = v___y_225_;
goto v___jp_216_;
}
else
{
v___y_217_ = v___y_225_;
v___y_218_ = v___x_223_;
goto v___jp_216_;
}
}
}
else
{
lean_object* v___x_228_; 
lean_inc_ref_n(v___x_214_, 2);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v___x_214_);
lean_ctor_set(v___x_228_, 1, v___x_214_);
lean_ctor_set(v___x_228_, 2, v___x_214_);
return v___x_228_;
}
v___jp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_215_, v___x_214_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_inc_ref_n(v___x_219_, 2);
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed(lean_object* v_x_229_, lean_object* v_s_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(v_x_229_, v_s_230_);
lean_dec(v_s_230_);
lean_dec_ref(v_x_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed(lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(v_x_234_);
lean_dec(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(lean_object* v_table_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0));
v___x_239_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_238_, v_table_236_);
v_sz_240_ = lean_array_size(v___x_239_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_240_, v___x_241_, v___x_239_);
v___x_243_ = lean_array_get_size(v___x_242_);
v___x_244_ = lean_nat_dec_eq(v___x_243_, v___x_237_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___y_248_; uint8_t v___x_252_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_sub(v___x_243_, v___x_245_);
v___x_252_ = lean_nat_dec_le(v___x_237_, v___x_246_);
if (v___x_252_ == 0)
{
lean_inc(v___x_246_);
v___y_248_ = v___x_246_;
goto v___jp_247_;
}
else
{
v___y_248_ = v___x_237_;
goto v___jp_247_;
}
v___jp_247_:
{
uint8_t v___x_249_; 
v___x_249_ = lean_nat_dec_le(v___y_248_, v___x_246_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v___x_246_);
lean_inc(v___y_248_);
v___x_250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_243_, v___x_242_, v___y_248_, v___y_248_);
lean_dec(v___y_248_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_243_, v___x_242_, v___y_248_, v___x_246_);
lean_dec(v___x_246_);
return v___x_251_;
}
}
}
else
{
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed(lean_object* v_table_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(v_table_253_);
lean_dec(v_table_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(lean_object* v___x_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed(lean_object* v___x_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(v___x_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(lean_object* v___x_261_, lean_object* v_x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_261_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed(lean_object* v___x_266_, lean_object* v_x_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(v___x_266_, v_x_267_, v___y_268_);
lean_dec_ref(v___y_268_);
lean_dec_ref(v_x_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect(){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11));
v___x_301_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___boxed(lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0(lean_object* v_init_304_, lean_object* v_t_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_304_, v_t_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(lean_object* v_init_307_, lean_object* v_t_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_307_, v_t_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1___boxed(lean_object* v_init_310_, lean_object* v_t_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(v_init_310_, v_t_311_);
lean_dec(v_t_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(lean_object* v_n_313_, lean_object* v_as_314_, lean_object* v_lo_315_, lean_object* v_hi_316_, lean_object* v_w_317_, lean_object* v_hlo_318_, lean_object* v_hhi_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_313_, v_as_314_, v_lo_315_, v_hi_316_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___boxed(lean_object* v_n_321_, lean_object* v_as_322_, lean_object* v_lo_323_, lean_object* v_hi_324_, lean_object* v_w_325_, lean_object* v_hlo_326_, lean_object* v_hhi_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(v_n_321_, v_as_322_, v_lo_323_, v_hi_324_, v_w_325_, v_hlo_326_, v_hhi_327_);
lean_dec(v_hi_324_);
lean_dec(v_n_321_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(lean_object* v_snd_329_, lean_object* v_k_330_, lean_object* v_t_331_, lean_object* v_hl_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_329_, v_k_330_, v_t_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___boxed(lean_object* v_snd_334_, lean_object* v_k_335_, lean_object* v_t_336_, lean_object* v_hl_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(v_snd_334_, v_k_335_, v_t_336_, v_hl_337_);
lean_dec_ref(v_snd_334_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(lean_object* v_n_339_, lean_object* v_lo_340_, lean_object* v_hi_341_, lean_object* v_hhi_342_, lean_object* v_pivot_343_, lean_object* v_as_344_, lean_object* v_i_345_, lean_object* v_k_346_, lean_object* v_ilo_347_, lean_object* v_ik_348_, lean_object* v_w_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_341_, v_pivot_343_, v_as_344_, v_i_345_, v_k_346_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___boxed(lean_object* v_n_351_, lean_object* v_lo_352_, lean_object* v_hi_353_, lean_object* v_hhi_354_, lean_object* v_pivot_355_, lean_object* v_as_356_, lean_object* v_i_357_, lean_object* v_k_358_, lean_object* v_ilo_359_, lean_object* v_ik_360_, lean_object* v_w_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(v_n_351_, v_lo_352_, v_hi_353_, v_hhi_354_, v_pivot_355_, v_as_356_, v_i_357_, v_k_358_, v_ilo_359_, v_ik_360_, v_w_361_);
lean_dec_ref(v_pivot_355_);
lean_dec(v_hi_353_);
lean_dec(v_lo_352_);
lean_dec(v_n_351_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(lean_object* v_fst_363_, lean_object* v_old_364_){
_start:
{
lean_object* v___y_366_; 
if (lean_obj_tag(v_old_364_) == 0)
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_NameSet_empty;
v___y_366_ = v___x_369_;
goto v___jp_365_;
}
else
{
lean_object* v_val_370_; 
v_val_370_ = lean_ctor_get(v_old_364_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_old_364_, 1);
v___y_366_ = v_val_370_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = l_Lean_NameSet_insert(v___y_366_, v_fst_363_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(lean_object* v_fst_371_, lean_object* v_k_372_, lean_object* v_t_373_){
_start:
{
if (lean_obj_tag(v_t_373_) == 0)
{
lean_object* v_size_374_; lean_object* v_k_375_; lean_object* v_v_376_; lean_object* v_l_377_; lean_object* v_r_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_393_; 
v_size_374_ = lean_ctor_get(v_t_373_, 0);
v_k_375_ = lean_ctor_get(v_t_373_, 1);
v_v_376_ = lean_ctor_get(v_t_373_, 2);
v_l_377_ = lean_ctor_get(v_t_373_, 3);
v_r_378_ = lean_ctor_get(v_t_373_, 4);
v_isSharedCheck_393_ = !lean_is_exclusive(v_t_373_);
if (v_isSharedCheck_393_ == 0)
{
v___x_380_ = v_t_373_;
v_isShared_381_ = v_isSharedCheck_393_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_r_378_);
lean_inc(v_l_377_);
lean_inc(v_v_376_);
lean_inc(v_k_375_);
lean_inc(v_size_374_);
lean_dec(v_t_373_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_393_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_372_, v_k_375_);
switch(v___x_382_)
{
case 0:
{
lean_object* v_impl_383_; lean_object* v___x_384_; 
lean_del_object(v___x_380_);
lean_dec(v_size_374_);
v_impl_383_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_371_, v_k_372_, v_l_377_);
v___x_384_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_375_, v_v_376_, v_impl_383_, v_r_378_);
return v___x_384_;
}
case 1:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_val_387_; lean_object* v___x_389_; 
lean_dec(v_k_375_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_v_376_);
v___x_386_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_371_, v___x_385_);
v_val_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_387_);
lean_dec(v___x_386_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v_val_387_);
lean_ctor_set(v___x_380_, 1, v_k_372_);
v___x_389_ = v___x_380_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_size_374_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_k_372_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_val_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_l_377_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_r_378_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
default: 
{
lean_object* v_impl_391_; lean_object* v___x_392_; 
lean_del_object(v___x_380_);
lean_dec(v_size_374_);
v_impl_391_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_371_, v_k_372_, v_r_378_);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_375_, v_v_376_, v_l_377_, v_impl_391_);
return v___x_392_;
}
}
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_394_ = lean_box(0);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_371_, v___x_394_);
v_val_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_396_);
lean_dec(v___x_395_);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_k_372_);
lean_ctor_set(v___x_398_, 2, v_val_396_);
lean_ctor_set(v___x_398_, 3, v_t_373_);
lean_ctor_set(v___x_398_, 4, v_t_373_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(lean_object* v_fst_399_, lean_object* v_as_400_, size_t v_i_401_, size_t v_stop_402_, lean_object* v_b_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_eq(v_i_401_, v_stop_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; size_t v___x_407_; size_t v___x_408_; 
v___x_405_ = lean_array_uget_borrowed(v_as_400_, v_i_401_);
lean_inc(v___x_405_);
lean_inc(v_fst_399_);
v___x_406_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_399_, v___x_405_, v_b_403_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_401_, v___x_407_);
v_i_401_ = v___x_408_;
v_b_403_ = v___x_406_;
goto _start;
}
else
{
lean_dec(v_fst_399_);
return v_b_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1___boxed(lean_object* v_fst_410_, lean_object* v_as_411_, lean_object* v_i_412_, lean_object* v_stop_413_, lean_object* v_b_414_){
_start:
{
size_t v_i_boxed_415_; size_t v_stop_boxed_416_; lean_object* v_res_417_; 
v_i_boxed_415_ = lean_unbox_usize(v_i_412_);
lean_dec(v_i_412_);
v_stop_boxed_416_ = lean_unbox_usize(v_stop_413_);
lean_dec(v_stop_413_);
v_res_417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_410_, v_as_411_, v_i_boxed_415_, v_stop_boxed_416_, v_b_414_);
lean_dec_ref(v_as_411_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0(lean_object* v_table_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_fst_420_; lean_object* v_snd_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_fst_420_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_fst_420_);
v_snd_421_ = lean_ctor_get(v_x_419_, 1);
lean_inc(v_snd_421_);
lean_dec_ref(v_x_419_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_array_get_size(v_snd_421_);
v___x_424_ = lean_nat_dec_lt(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec(v_snd_421_);
lean_dec(v_fst_420_);
return v_table_418_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_le(v___x_423_, v___x_423_);
if (v___x_425_ == 0)
{
if (v___x_424_ == 0)
{
lean_dec(v_snd_421_);
lean_dec(v_fst_420_);
return v_table_418_;
}
else
{
size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((size_t)0ULL);
v___x_427_ = lean_usize_of_nat(v___x_423_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_420_, v_snd_421_, v___x_426_, v___x_427_, v_table_418_);
lean_dec(v_snd_421_);
return v___x_428_;
}
}
else
{
size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; 
v___x_429_ = ((size_t)0ULL);
v___x_430_ = lean_usize_of_nat(v___x_423_);
v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_420_, v_snd_421_, v___x_429_, v___x_430_, v_table_418_);
lean_dec(v_snd_421_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting(){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4));
v___x_453_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object* v_fst_456_, lean_object* v_k_457_, lean_object* v_t_458_, lean_object* v_hl_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_456_, v_k_457_, v_t_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v_addEntryFn_461_, lean_object* v___x_462_, lean_object* v_s_463_){
_start:
{
lean_object* v_importedEntries_464_; lean_object* v_state_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_473_; 
v_importedEntries_464_ = lean_ctor_get(v_s_463_, 0);
v_state_465_ = lean_ctor_get(v_s_463_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_s_463_);
if (v_isSharedCheck_473_ == 0)
{
v___x_467_ = v_s_463_;
v_isShared_468_ = v_isSharedCheck_473_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_state_465_);
lean_inc(v_importedEntries_464_);
lean_dec(v_s_463_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_473_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_state_469_; lean_object* v___x_471_; 
v_state_469_ = lean_apply_2(v_addEntryFn_461_, v_state_465_, v___x_462_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v_state_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_importedEntries_464_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_state_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_474_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_478_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
lean_ctor_set(v___x_480_, 3, v___x_479_);
lean_ctor_set(v___x_480_, 4, v___x_478_);
lean_ctor_set(v___x_480_, 5, v___x_478_);
lean_ctor_set(v___x_480_, 6, v___x_478_);
lean_ctor_set(v___x_480_, 7, v___x_478_);
lean_ctor_set(v___x_480_, 8, v___x_478_);
lean_ctor_set(v___x_480_, 9, v___x_478_);
lean_ctor_set(v___x_480_, 10, v___x_478_);
lean_ctor_set(v___x_480_, 11, v___x_477_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_unsigned_to_nat(32u);
v___x_482_ = lean_mk_empty_array_with_capacity(v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_484_ = ((size_t)5ULL);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_unsigned_to_nat(32u);
v___x_487_ = lean_mk_empty_array_with_capacity(v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_489_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_485_);
lean_ctor_set(v___x_489_, 3, v___x_485_);
lean_ctor_set_usize(v___x_489_, 4, v___x_484_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_box(1);
v___x_491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_492_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
lean_ctor_set(v___x_493_, 2, v___x_490_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_toCold_499_; lean_object* v_env_500_; lean_object* v_options_501_; uint8_t v___x_502_; lean_object* v_env_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_498_ = lean_st_ref_get(v___y_496_);
v_toCold_499_ = lean_ctor_get(v___y_495_, 0);
v_env_500_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_env_500_);
lean_dec(v___x_498_);
v_options_501_ = lean_ctor_get(v_toCold_499_, 2);
v___x_502_ = 0;
v_env_503_ = l_Lean_Environment_setRecordingDeps(v_env_500_, v___x_502_);
v___x_504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_505_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_501_);
v___x_506_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_506_, 0, v_env_503_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
lean_ctor_set(v___x_506_, 3, v_options_501_);
v___x_507_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_msgData_494_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_ref_518_; lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_ref_518_ = lean_ctor_get(v___y_515_, 2);
v___x_519_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msg_514_, v___y_515_, v___y_516_);
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_528_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_inc(v_ref_518_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_ref_518_);
lean_ctor_set(v___x_524_, 1, v_a_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 1);
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_533_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object* v_name_546_, uint8_t v_kind_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___y_557_; 
v___x_551_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_552_ = l_Lean_MessageData_ofName(v_name_546_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
switch(v_kind_547_)
{
case 0:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6));
v___y_557_ = v___x_564_;
goto v___jp_556_;
}
case 1:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7));
v___y_557_ = v___x_565_;
goto v___jp_556_;
}
default: 
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8));
v___y_557_ = v___x_566_;
goto v___jp_556_;
}
}
v___jp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_inc_ref(v___y_557_);
v___x_558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_558_, 0, v___y_557_);
v___x_559_ = l_Lean_MessageData_ofFormat(v___x_558_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_555_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_562_, v___y_548_, v___y_549_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_name_567_, lean_object* v_kind_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v_kind_boxed_572_; lean_object* v_res_573_; 
v_kind_boxed_572_ = lean_unbox(v_kind_568_);
v_res_573_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_567_, v_kind_boxed_572_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_577_ == 0)
{
return v_bs_576_;
}
else
{
lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v_bs_x27_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v_v_578_ = lean_array_uget(v_bs_576_, v_i_575_);
v___x_579_ = lean_unsigned_to_nat(0u);
v_bs_x27_580_ = lean_array_uset(v_bs_576_, v_i_575_, v___x_579_);
v___x_581_ = l_Lean_Syntax_getId(v_v_578_);
lean_dec(v_v_578_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_575_, v___x_582_);
v___x_584_ = lean_array_uset(v_bs_x27_580_, v_i_575_, v___x_581_);
v_i_575_ = v___x_583_;
v_bs_576_ = v___x_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_586_, lean_object* v_i_587_, lean_object* v_bs_588_){
_start:
{
size_t v_sz_boxed_589_; size_t v_i_boxed_590_; lean_object* v_res_591_; 
v_sz_boxed_589_ = lean_unbox_usize(v_sz_586_);
lean_dec(v_sz_586_);
v_i_boxed_590_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_boxed_589_, v_i_boxed_590_, v_bs_588_);
return v_res_591_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_601_ = l_Lean_stringToMessageData(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v_a_606_, lean_object* v___x_607_, lean_object* v_a_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_decl_613_, lean_object* v_stx_614_, uint8_t v_kind_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_nextMacroScope_620_; lean_object* v_ngen_621_; lean_object* v_auxDeclNGen_622_; lean_object* v_traceState_623_; lean_object* v_recordedDeps_624_; lean_object* v_messages_625_; lean_object* v_infoState_626_; lean_object* v_snapshotTasks_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_636_; lean_object* v_nextMacroScope_637_; lean_object* v_ngen_638_; lean_object* v_auxDeclNGen_639_; lean_object* v_traceState_640_; lean_object* v_recordedDeps_641_; lean_object* v_messages_642_; lean_object* v_infoState_643_; lean_object* v_snapshotTasks_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v_altSyntaxIds_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_705_; lean_object* v___y_706_; uint8_t v___x_779_; uint8_t v___x_780_; 
v___x_779_ = 0;
v___x_780_ = l_Lean_instBEqAttributeKind_beq(v_kind_615_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_stx_614_);
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___x_781_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v___x_612_, v_kind_615_, v___y_616_, v___y_617_);
return v___x_781_;
}
else
{
lean_dec(v___x_612_);
goto v___jp_720_;
}
v___jp_619_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_inc_ref(v___y_630_);
v___x_632_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_632_, 0, v___y_631_);
lean_ctor_set(v___x_632_, 1, v_nextMacroScope_620_);
lean_ctor_set(v___x_632_, 2, v_ngen_621_);
lean_ctor_set(v___x_632_, 3, v_auxDeclNGen_622_);
lean_ctor_set(v___x_632_, 4, v_traceState_623_);
lean_ctor_set(v___x_632_, 5, v___y_630_);
lean_ctor_set(v___x_632_, 6, v_recordedDeps_624_);
lean_ctor_set(v___x_632_, 7, v_messages_625_);
lean_ctor_set(v___x_632_, 8, v_infoState_626_);
lean_ctor_set(v___x_632_, 9, v_snapshotTasks_627_);
v___x_633_ = lean_st_ref_put(v___y_629_, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___y_628_);
return v___x_634_;
}
v___jp_635_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_toEnvExtension_651_; lean_object* v_env_652_; lean_object* v_nextMacroScope_653_; lean_object* v_ngen_654_; lean_object* v_auxDeclNGen_655_; lean_object* v_traceState_656_; lean_object* v_recordedDeps_657_; lean_object* v_messages_658_; lean_object* v_infoState_659_; lean_object* v_snapshotTasks_660_; lean_object* v_addEntryFn_661_; lean_object* v_asyncMode_662_; uint8_t v_logWrites_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___f_666_; uint8_t v___x_667_; 
v___x_647_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_648_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_648_, 0, v___y_646_);
lean_ctor_set(v___x_648_, 1, v_nextMacroScope_637_);
lean_ctor_set(v___x_648_, 2, v_ngen_638_);
lean_ctor_set(v___x_648_, 3, v_auxDeclNGen_639_);
lean_ctor_set(v___x_648_, 4, v_traceState_640_);
lean_ctor_set(v___x_648_, 5, v___x_647_);
lean_ctor_set(v___x_648_, 6, v_recordedDeps_641_);
lean_ctor_set(v___x_648_, 7, v_messages_642_);
lean_ctor_set(v___x_648_, 8, v_infoState_643_);
lean_ctor_set(v___x_648_, 9, v_snapshotTasks_644_);
v___x_649_ = lean_st_ref_put(v___y_636_, v___x_648_);
v___x_650_ = lean_st_ref_take(v___y_636_);
v_toEnvExtension_651_ = lean_ctor_get(v_a_606_, 0);
lean_inc_ref(v_toEnvExtension_651_);
v_env_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_env_652_);
v_nextMacroScope_653_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_nextMacroScope_653_);
v_ngen_654_ = lean_ctor_get(v___x_650_, 2);
lean_inc_ref(v_ngen_654_);
v_auxDeclNGen_655_ = lean_ctor_get(v___x_650_, 3);
lean_inc_ref(v_auxDeclNGen_655_);
v_traceState_656_ = lean_ctor_get(v___x_650_, 4);
lean_inc_ref(v_traceState_656_);
v_recordedDeps_657_ = lean_ctor_get(v___x_650_, 6);
lean_inc_ref(v_recordedDeps_657_);
v_messages_658_ = lean_ctor_get(v___x_650_, 7);
lean_inc_ref(v_messages_658_);
v_infoState_659_ = lean_ctor_get(v___x_650_, 8);
lean_inc_ref(v_infoState_659_);
v_snapshotTasks_660_ = lean_ctor_get(v___x_650_, 9);
lean_inc_ref(v_snapshotTasks_660_);
lean_dec(v___x_650_);
v_addEntryFn_661_ = lean_ctor_get(v_a_606_, 3);
lean_inc(v_addEntryFn_661_);
lean_dec_ref(v_a_606_);
v_asyncMode_662_ = lean_ctor_get(v_toEnvExtension_651_, 2);
lean_inc(v_asyncMode_662_);
v_logWrites_663_ = lean_ctor_get_uint8(v_toEnvExtension_651_, sizeof(void*)*6);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_decl_613_);
lean_ctor_set(v___x_665_, 1, v___y_645_);
v___f_666_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_666_, 0, v_addEntryFn_661_);
lean_closure_set(v___f_666_, 1, v___x_665_);
v___x_667_ = 1;
if (v_logWrites_663_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_651_, v_env_652_, v___f_666_, v_asyncMode_662_, v___x_607_, v___x_667_);
lean_dec(v_asyncMode_662_);
v_nextMacroScope_620_ = v_nextMacroScope_653_;
v_ngen_621_ = v_ngen_654_;
v_auxDeclNGen_622_ = v_auxDeclNGen_655_;
v_traceState_623_ = v_traceState_656_;
v_recordedDeps_624_ = v_recordedDeps_657_;
v_messages_625_ = v_messages_658_;
v_infoState_626_ = v_infoState_659_;
v_snapshotTasks_627_ = v_snapshotTasks_660_;
v___y_628_ = v___x_664_;
v___y_629_ = v___y_636_;
v___y_630_ = v___x_647_;
v___y_631_ = v___x_668_;
goto v___jp_619_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc_ref(v_toEnvExtension_651_);
v___x_669_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_651_, v_env_652_);
lean_dec_ref(v_env_652_);
v___x_670_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_651_, v___x_669_, v___f_666_, v_asyncMode_662_, v___x_607_, v___x_667_);
lean_dec(v_asyncMode_662_);
v_nextMacroScope_620_ = v_nextMacroScope_653_;
v_ngen_621_ = v_ngen_654_;
v_auxDeclNGen_622_ = v_auxDeclNGen_655_;
v_traceState_623_ = v_traceState_656_;
v_recordedDeps_624_ = v_recordedDeps_657_;
v_messages_625_ = v_messages_658_;
v_infoState_626_ = v_infoState_659_;
v_snapshotTasks_627_ = v_snapshotTasks_660_;
v___y_628_ = v___x_664_;
v___y_629_ = v___y_636_;
v___y_630_ = v___x_647_;
v___y_631_ = v___x_670_;
goto v___jp_619_;
}
}
v___jp_671_:
{
size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_toEnvExtension_678_; lean_object* v_env_679_; lean_object* v_nextMacroScope_680_; lean_object* v_ngen_681_; lean_object* v_auxDeclNGen_682_; lean_object* v_traceState_683_; lean_object* v_recordedDeps_684_; lean_object* v_messages_685_; lean_object* v_infoState_686_; lean_object* v_snapshotTasks_687_; lean_object* v_addEntryFn_688_; lean_object* v_asyncMode_689_; uint8_t v_logWrites_690_; lean_object* v___x_691_; lean_object* v___f_692_; uint8_t v___x_693_; 
v_sz_674_ = lean_array_size(v___y_672_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_674_, v___x_675_, v___y_672_);
v___x_677_ = lean_st_ref_take(v___y_673_);
v_toEnvExtension_678_ = lean_ctor_get(v_a_608_, 0);
lean_inc_ref(v_toEnvExtension_678_);
v_env_679_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_env_679_);
v_nextMacroScope_680_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_nextMacroScope_680_);
v_ngen_681_ = lean_ctor_get(v___x_677_, 2);
lean_inc_ref(v_ngen_681_);
v_auxDeclNGen_682_ = lean_ctor_get(v___x_677_, 3);
lean_inc_ref(v_auxDeclNGen_682_);
v_traceState_683_ = lean_ctor_get(v___x_677_, 4);
lean_inc_ref(v_traceState_683_);
v_recordedDeps_684_ = lean_ctor_get(v___x_677_, 6);
lean_inc_ref(v_recordedDeps_684_);
v_messages_685_ = lean_ctor_get(v___x_677_, 7);
lean_inc_ref(v_messages_685_);
v_infoState_686_ = lean_ctor_get(v___x_677_, 8);
lean_inc_ref(v_infoState_686_);
v_snapshotTasks_687_ = lean_ctor_get(v___x_677_, 9);
lean_inc_ref(v_snapshotTasks_687_);
lean_dec(v___x_677_);
v_addEntryFn_688_ = lean_ctor_get(v_a_608_, 3);
lean_inc(v_addEntryFn_688_);
lean_dec_ref(v_a_608_);
v_asyncMode_689_ = lean_ctor_get(v_toEnvExtension_678_, 2);
lean_inc(v_asyncMode_689_);
v_logWrites_690_ = lean_ctor_get_uint8(v_toEnvExtension_678_, sizeof(void*)*6);
lean_inc_ref(v___x_676_);
lean_inc(v_decl_613_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_decl_613_);
lean_ctor_set(v___x_691_, 1, v___x_676_);
v___f_692_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_692_, 0, v_addEntryFn_688_);
lean_closure_set(v___f_692_, 1, v___x_691_);
v___x_693_ = 1;
if (v_logWrites_690_ == 0)
{
lean_object* v___x_694_; 
lean_inc(v___x_607_);
v___x_694_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_678_, v_env_679_, v___f_692_, v_asyncMode_689_, v___x_607_, v___x_693_);
lean_dec(v_asyncMode_689_);
v___y_636_ = v___y_673_;
v_nextMacroScope_637_ = v_nextMacroScope_680_;
v_ngen_638_ = v_ngen_681_;
v_auxDeclNGen_639_ = v_auxDeclNGen_682_;
v_traceState_640_ = v_traceState_683_;
v_recordedDeps_641_ = v_recordedDeps_684_;
v_messages_642_ = v_messages_685_;
v_infoState_643_ = v_infoState_686_;
v_snapshotTasks_644_ = v_snapshotTasks_687_;
v___y_645_ = v___x_676_;
v___y_646_ = v___x_694_;
goto v___jp_635_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_inc_ref(v_toEnvExtension_678_);
v___x_695_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_678_, v_env_679_);
lean_dec_ref(v_env_679_);
lean_inc(v___x_607_);
v___x_696_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_678_, v___x_695_, v___f_692_, v_asyncMode_689_, v___x_607_, v___x_693_);
lean_dec(v_asyncMode_689_);
v___y_636_ = v___y_673_;
v_nextMacroScope_637_ = v_nextMacroScope_680_;
v_ngen_638_ = v_ngen_681_;
v_auxDeclNGen_639_ = v_auxDeclNGen_682_;
v_traceState_640_ = v_traceState_683_;
v_recordedDeps_641_ = v_recordedDeps_684_;
v_messages_642_ = v_messages_685_;
v_infoState_643_ = v_infoState_686_;
v_snapshotTasks_644_ = v_snapshotTasks_687_;
v___y_645_ = v___x_676_;
v___y_646_ = v___x_696_;
goto v___jp_635_;
}
}
v___jp_697_:
{
uint8_t v___x_701_; 
v___x_701_ = l_Lean_isPrivateName(v_decl_613_);
if (v___x_701_ == 0)
{
v___y_672_ = v_altSyntaxIds_698_;
v___y_673_ = v___y_700_;
goto v___jp_671_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v_altSyntaxIds_698_);
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___x_702_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_703_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_702_, v___y_699_, v___y_700_);
return v___x_703_;
}
}
v___jp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v___x_707_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_708_ = l_Lean_Syntax_instRepr_repr(v_stx_614_, v___x_609_);
v___x_709_ = l_Lean_MessageData_ofFormat(v___x_708_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_707_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_710_, v___y_705_, v___y_706_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
v___jp_720_:
{
if (lean_obj_tag(v_stx_614_) == 1)
{
lean_object* v_kind_721_; 
v_kind_721_ = lean_ctor_get(v_stx_614_, 1);
if (lean_obj_tag(v_kind_721_) == 1)
{
lean_object* v_pre_722_; 
v_pre_722_ = lean_ctor_get(v_kind_721_, 0);
if (lean_obj_tag(v_pre_722_) == 1)
{
lean_object* v_pre_723_; 
v_pre_723_ = lean_ctor_get(v_pre_722_, 0);
switch(lean_obj_tag(v_pre_723_))
{
case 0:
{
lean_object* v_args_724_; lean_object* v_str_725_; lean_object* v_str_726_; uint8_t v___x_727_; 
v_args_724_ = lean_ctor_get(v_stx_614_, 2);
v_str_725_ = lean_ctor_get(v_kind_721_, 1);
v_str_726_ = lean_ctor_get(v_pre_722_, 1);
v___x_727_ = lean_string_dec_eq(v_str_726_, v___x_610_);
if (v___x_727_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = lean_string_dec_eq(v_str_725_, v___x_611_);
if (v___x_728_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_array_get_size(v_args_724_);
v___x_730_ = lean_unsigned_to_nat(2u);
v___x_731_ = lean_nat_dec_eq(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_array_fget_borrowed(v_args_724_, v___x_609_);
if (lean_obj_tag(v___x_732_) == 2)
{
lean_object* v_val_733_; uint8_t v___x_734_; 
v_val_733_ = lean_ctor_get(v___x_732_, 1);
v___x_734_ = lean_string_dec_eq(v_val_733_, v___x_611_);
if (v___x_734_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_array_fget_borrowed(v_args_724_, v___x_735_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_kind_737_; 
v_kind_737_ = lean_ctor_get(v___x_736_, 1);
if (lean_obj_tag(v_kind_737_) == 1)
{
lean_object* v_pre_738_; 
v_pre_738_ = lean_ctor_get(v_kind_737_, 0);
if (lean_obj_tag(v_pre_738_) == 0)
{
lean_object* v_args_739_; lean_object* v_str_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_args_739_ = lean_ctor_get(v___x_736_, 2);
v_str_740_ = lean_ctor_get(v_kind_737_, 1);
v___x_741_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_742_ = lean_string_dec_eq(v_str_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_inc_ref(v_args_739_);
lean_dec_ref_known(v_stx_614_, 3);
v_altSyntaxIds_698_ = v_args_739_;
v___y_699_ = v___y_616_;
v___y_700_ = v___y_617_;
goto v___jp_697_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
}
}
}
case 1:
{
lean_object* v_pre_743_; 
v_pre_743_ = lean_ctor_get(v_pre_723_, 0);
if (lean_obj_tag(v_pre_743_) == 1)
{
lean_object* v_pre_744_; 
v_pre_744_ = lean_ctor_get(v_pre_743_, 0);
if (lean_obj_tag(v_pre_744_) == 0)
{
lean_object* v_args_745_; lean_object* v_str_746_; lean_object* v_str_747_; lean_object* v_str_748_; lean_object* v_str_749_; uint8_t v___x_750_; 
v_args_745_ = lean_ctor_get(v_stx_614_, 2);
v_str_746_ = lean_ctor_get(v_kind_721_, 1);
v_str_747_ = lean_ctor_get(v_pre_722_, 1);
v_str_748_ = lean_ctor_get(v_pre_723_, 1);
v_str_749_ = lean_ctor_get(v_pre_743_, 1);
v___x_750_ = lean_string_dec_eq(v_str_749_, v___x_610_);
if (v___x_750_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_752_ = lean_string_dec_eq(v_str_748_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_754_ = lean_string_dec_eq(v_str_747_, v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_756_ = lean_string_dec_eq(v_str_746_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_757_ = lean_array_get_size(v_args_745_);
v___x_758_ = lean_unsigned_to_nat(2u);
v___x_759_ = lean_nat_dec_eq(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = lean_array_fget_borrowed(v_args_745_, v___x_609_);
if (lean_obj_tag(v___x_760_) == 3)
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v___x_760_, 2);
if (lean_obj_tag(v_val_761_) == 1)
{
lean_object* v_pre_762_; 
v_pre_762_ = lean_ctor_get(v_val_761_, 0);
if (lean_obj_tag(v_pre_762_) == 0)
{
lean_object* v_preresolved_763_; lean_object* v_str_764_; uint8_t v___x_765_; 
v_preresolved_763_ = lean_ctor_get(v___x_760_, 3);
v_str_764_ = lean_ctor_get(v_val_761_, 1);
v___x_765_ = lean_string_dec_eq(v_str_764_, v___x_611_);
if (v___x_765_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
if (lean_obj_tag(v_preresolved_763_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_array_fget_borrowed(v_args_745_, v___x_766_);
if (lean_obj_tag(v___x_767_) == 1)
{
lean_object* v_kind_768_; 
v_kind_768_ = lean_ctor_get(v___x_767_, 1);
if (lean_obj_tag(v_kind_768_) == 1)
{
lean_object* v_pre_769_; 
v_pre_769_ = lean_ctor_get(v_kind_768_, 0);
if (lean_obj_tag(v_pre_769_) == 0)
{
lean_object* v_args_770_; lean_object* v_str_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_args_770_ = lean_ctor_get(v___x_767_, 2);
v_str_771_ = lean_ctor_get(v_kind_768_, 1);
v___x_772_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_773_ = lean_string_dec_eq(v_str_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_args_770_);
v___x_775_ = lean_nat_dec_eq(v___x_774_, v___x_766_);
if (v___x_775_ == 0)
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_ref(v_args_770_);
lean_dec_ref_known(v_stx_614_, 3);
v___x_776_ = lean_array_fget(v_args_770_, v___x_609_);
lean_dec_ref(v_args_770_);
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_766_);
v___x_778_ = lean_array_push(v___x_777_, v___x_776_);
v_altSyntaxIds_698_ = v___x_778_;
v___y_699_ = v___y_616_;
v___y_700_ = v___y_617_;
goto v___jp_697_;
}
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
default: 
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_decl_613_);
lean_dec_ref(v_a_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_606_);
v___y_705_ = v___y_616_;
v___y_706_ = v___y_617_;
goto v___jp_704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_782_, lean_object* v___x_783_, lean_object* v_a_784_, lean_object* v___x_785_, lean_object* v___x_786_, lean_object* v___x_787_, lean_object* v___x_788_, lean_object* v_decl_789_, lean_object* v_stx_790_, lean_object* v_kind_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v_kind_boxed_795_; lean_object* v_res_796_; 
v_kind_boxed_795_ = lean_unbox(v_kind_791_);
v_res_796_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v_a_782_, v___x_783_, v_a_784_, v___x_785_, v___x_786_, v___x_787_, v___x_788_, v_decl_789_, v_stx_790_, v_kind_boxed_795_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v___x_787_);
lean_dec_ref(v___x_786_);
lean_dec(v___x_785_);
return v_res_796_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v___x_803_, lean_object* v_decl_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_808_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_809_ = l_Lean_MessageData_ofName(v___x_803_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_812_, v___y_805_, v___y_806_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v___x_814_, lean_object* v_decl_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v___x_814_, v_decl_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v_decl_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_n(v_a_856_, 2);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = lean_box(0);
v___x_858_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4));
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_861_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
lean_inc(v_a_854_);
v___f_862_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed), 13, 7);
lean_closure_set(v___f_862_, 0, v_a_856_);
lean_closure_set(v___f_862_, 1, v___x_857_);
lean_closure_set(v___f_862_, 2, v_a_854_);
lean_closure_set(v___f_862_, 3, v___x_859_);
lean_closure_set(v___f_862_, 4, v___x_858_);
lean_closure_set(v___f_862_, 5, v___x_860_);
lean_closure_set(v___f_862_, 6, v___x_861_);
v___f_863_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_864_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___f_862_);
lean_ctor_set(v___x_865_, 2, v___f_863_);
v___x_866_ = l_Lean_registerBuiltinAttribute(v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_866_, 0);
lean_dec(v_unused_875_);
v___x_868_ = v___x_866_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_dec(v___x_866_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_a_854_);
lean_ctor_set(v___x_870_, 1, v_a_856_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
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
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_856_);
lean_dec(v_a_854_);
v_a_876_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_866_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_866_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
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
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_854_);
v_a_884_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_855_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_855_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_853_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_853_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_902_, lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_903_, v___y_904_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_908_, lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(v_00_u03b1_908_, v_msg_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b1_914_, lean_object* v_name_915_, uint8_t v_kind_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_915_, v_kind_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b1_921_, lean_object* v_name_922_, lean_object* v_kind_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v_kind_boxed_927_; lean_object* v_res_928_; 
v_kind_boxed_927_ = lean_unbox(v_kind_923_);
v_res_928_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(v_00_u03b1_921_, v_name_922_, v_kind_boxed_927_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1(lean_object* v_incorrectName_951_, lean_object* v___f_952_, lean_object* v___f_953_, lean_object* v_x1_954_, lean_object* v_x2_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_x2_955_);
v___x_958_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec_ref(v___f_953_);
lean_dec_ref(v___f_952_);
lean_dec(v_incorrectName_951_);
return v_x1_954_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_sub(v___x_957_, v___x_959_);
v___x_961_ = lean_nat_dec_le(v___x_956_, v___x_960_);
if (v___x_961_ == 0)
{
lean_dec(v___x_960_);
lean_dec_ref(v___f_953_);
lean_dec_ref(v___f_952_);
lean_dec(v_incorrectName_951_);
return v_x1_954_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_incorrectName_951_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_965_ = l_Array_binSearchAux___redArg(v___f_952_, v___x_964_, v_x2_955_, v___x_963_, v___x_956_, v___x_960_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref(v___f_953_);
return v_x1_954_;
}
else
{
lean_object* v_val_966_; lean_object* v_snd_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_val_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v___x_965_, 1);
v_snd_967_ = lean_ctor_get(v_val_966_, 1);
lean_inc(v_snd_967_);
lean_dec(v_val_966_);
v___x_968_ = lean_array_get_size(v_snd_967_);
v___x_969_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_970_ = lean_nat_dec_lt(v___x_956_, v___x_968_);
if (v___x_970_ == 0)
{
lean_dec(v_snd_967_);
lean_dec_ref(v___f_953_);
return v_x1_954_;
}
else
{
uint8_t v___x_971_; 
v___x_971_ = lean_nat_dec_le(v___x_968_, v___x_968_);
if (v___x_971_ == 0)
{
if (v___x_970_ == 0)
{
lean_dec(v_snd_967_);
lean_dec_ref(v___f_953_);
return v_x1_954_;
}
else
{
size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
v___x_972_ = ((size_t)0ULL);
v___x_973_ = lean_usize_of_nat(v___x_968_);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_969_, v___f_953_, v_snd_967_, v___x_972_, v___x_973_, v_x1_954_);
return v___x_974_;
}
}
else
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((size_t)0ULL);
v___x_976_ = lean_usize_of_nat(v___x_968_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_969_, v___f_953_, v_snd_967_, v___x_975_, v___x_976_, v_x1_954_);
return v___x_977_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1___boxed(lean_object* v_incorrectName_978_, lean_object* v___f_979_, lean_object* v___f_980_, lean_object* v_x1_981_, lean_object* v_x2_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_getSuggestions___redArg___lam__1(v_incorrectName_978_, v___f_979_, v___f_980_, v_x1_981_, v_x2_982_);
lean_dec_ref(v_x2_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0(lean_object* v___x_984_, lean_object* v_toPure_985_, lean_object* v___f_986_, lean_object* v_incorrectName_987_, lean_object* v_env_988_){
_start:
{
lean_object* v___x_989_; lean_object* v_snd_990_; lean_object* v_toEnvExtension_991_; lean_object* v_asyncMode_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v_importedEntries_996_; lean_object* v_state_997_; lean_object* v___y_999_; lean_object* v___x_1015_; 
v___x_989_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_990_ = lean_ctor_get(v___x_989_, 1);
v_toEnvExtension_991_ = lean_ctor_get(v_snd_990_, 0);
v_asyncMode_992_ = lean_ctor_get(v_toEnvExtension_991_, 2);
v___x_993_ = lean_box(0);
v___x_994_ = 0;
v___x_995_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_984_, v_toEnvExtension_991_, v_env_988_, v_asyncMode_992_, v___x_993_, v___x_994_);
v_importedEntries_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_importedEntries_996_);
v_state_997_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_state_997_);
lean_dec(v___x_995_);
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_997_, v_incorrectName_987_);
lean_dec(v_state_997_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_NameSet_empty;
v___y_999_ = v___x_1016_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1017_; 
v_val_1017_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v___x_1015_, 1);
v___y_999_ = v_val_1017_;
goto v___jp_998_;
}
v___jp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_array_get_size(v_importedEntries_996_);
v___x_1002_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1003_ = lean_nat_dec_lt(v___x_1000_, v___x_1001_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec_ref(v_importedEntries_996_);
lean_dec_ref(v___f_986_);
v___x_1004_ = lean_apply_2(v_toPure_985_, lean_box(0), v___y_999_);
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_nat_dec_le(v___x_1001_, v___x_1001_);
if (v___x_1005_ == 0)
{
if (v___x_1003_ == 0)
{
lean_object* v___x_1006_; 
lean_dec_ref(v_importedEntries_996_);
lean_dec_ref(v___f_986_);
v___x_1006_ = lean_apply_2(v_toPure_985_, lean_box(0), v___y_999_);
return v___x_1006_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1001_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1002_, v___f_986_, v_importedEntries_996_, v___x_1007_, v___x_1008_, v___y_999_);
v___x_1010_ = lean_apply_2(v_toPure_985_, lean_box(0), v___x_1009_);
return v___x_1010_;
}
}
else
{
size_t v___x_1011_; size_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = ((size_t)0ULL);
v___x_1012_ = lean_usize_of_nat(v___x_1001_);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1002_, v___f_986_, v_importedEntries_996_, v___x_1011_, v___x_1012_, v___y_999_);
v___x_1014_ = lean_apply_2(v_toPure_985_, lean_box(0), v___x_1013_);
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0___boxed(lean_object* v___x_1018_, lean_object* v_toPure_1019_, lean_object* v___f_1020_, lean_object* v_incorrectName_1021_, lean_object* v_env_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_getSuggestions___redArg___lam__0(v___x_1018_, v_toPure_1019_, v___f_1020_, v_incorrectName_1021_, v_env_1022_);
lean_dec(v_incorrectName_1021_);
lean_dec_ref(v___x_1018_);
return v_res_1023_;
}
}
static lean_object* _init_l_Lean_getSuggestions___redArg___closed__2(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(1);
v___x_1027_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg(lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_incorrectName_1030_){
_start:
{
lean_object* v_toApplicative_1031_; lean_object* v_toBind_1032_; lean_object* v_getEnv_1033_; lean_object* v_toPure_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; 
v_toApplicative_1031_ = lean_ctor_get(v_inst_1028_, 0);
lean_inc_ref(v_toApplicative_1031_);
v_toBind_1032_ = lean_ctor_get(v_inst_1028_, 1);
lean_inc(v_toBind_1032_);
lean_dec_ref(v_inst_1028_);
v_getEnv_1033_ = lean_ctor_get(v_inst_1029_, 0);
lean_inc(v_getEnv_1033_);
lean_dec_ref(v_inst_1029_);
v_toPure_1034_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_inc(v_toPure_1034_);
lean_dec_ref(v_toApplicative_1031_);
v___f_1035_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
v___f_1036_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__1));
lean_inc(v_incorrectName_1030_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1037_, 0, v_incorrectName_1030_);
lean_closure_set(v___f_1037_, 1, v___f_1035_);
lean_closure_set(v___f_1037_, 2, v___f_1036_);
v___x_1038_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1039_, 0, v___x_1038_);
lean_closure_set(v___f_1039_, 1, v_toPure_1034_);
lean_closure_set(v___f_1039_, 2, v___f_1037_);
lean_closure_set(v___f_1039_, 3, v_incorrectName_1030_);
v___x_1040_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v_getEnv_1033_, v___f_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions(lean_object* v_m_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_incorrectName_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_getSuggestions___redArg(v_inst_1042_, v_inst_1043_, v_incorrectName_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1(lean_object* v_trueName_1046_, lean_object* v___f_1047_, lean_object* v___f_1048_, lean_object* v_x1_1049_, lean_object* v_x2_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_array_get_size(v_x2_1050_);
v___x_1053_ = lean_nat_dec_lt(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v___f_1048_);
lean_dec_ref(v___f_1047_);
lean_dec(v_trueName_1046_);
return v_x1_1049_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_sub(v___x_1052_, v___x_1054_);
v___x_1056_ = lean_nat_dec_le(v___x_1051_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v___x_1055_);
lean_dec_ref(v___f_1048_);
lean_dec_ref(v___f_1047_);
lean_dec(v_trueName_1046_);
return v_x1_1049_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_trueName_1046_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_1060_ = l_Array_binSearchAux___redArg(v___f_1047_, v___x_1059_, v_x2_1050_, v___x_1058_, v___x_1051_, v___x_1055_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_dec_ref(v___f_1048_);
return v_x1_1049_;
}
else
{
lean_object* v_val_1061_; lean_object* v_snd_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_val_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v_snd_1062_ = lean_ctor_get(v_val_1061_, 1);
lean_inc(v_snd_1062_);
lean_dec(v_val_1061_);
v___x_1063_ = lean_array_get_size(v_snd_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1065_ = lean_nat_dec_lt(v___x_1051_, v___x_1063_);
if (v___x_1065_ == 0)
{
lean_dec(v_snd_1062_);
lean_dec_ref(v___f_1048_);
return v_x1_1049_;
}
else
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_le(v___x_1063_, v___x_1063_);
if (v___x_1066_ == 0)
{
if (v___x_1065_ == 0)
{
lean_dec(v_snd_1062_);
lean_dec_ref(v___f_1048_);
return v_x1_1049_;
}
else
{
size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = ((size_t)0ULL);
v___x_1068_ = lean_usize_of_nat(v___x_1063_);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1064_, v___f_1048_, v_snd_1062_, v___x_1067_, v___x_1068_, v_x1_1049_);
return v___x_1069_;
}
}
else
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = lean_usize_of_nat(v___x_1063_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1064_, v___f_1048_, v_snd_1062_, v___x_1070_, v___x_1071_, v_x1_1049_);
return v___x_1072_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1___boxed(lean_object* v_trueName_1073_, lean_object* v___f_1074_, lean_object* v___f_1075_, lean_object* v_x1_1076_, lean_object* v_x2_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_getStoredSuggestions___redArg___lam__1(v_trueName_1073_, v___f_1074_, v___f_1075_, v_x1_1076_, v_x2_1077_);
lean_dec_ref(v_x2_1077_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0(lean_object* v___x_1079_, lean_object* v_toPure_1080_, lean_object* v___f_1081_, lean_object* v_trueName_1082_, lean_object* v_env_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v_fst_1085_; lean_object* v_toEnvExtension_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v_importedEntries_1091_; lean_object* v_state_1092_; lean_object* v___y_1094_; lean_object* v___x_1110_; 
v___x_1084_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_fst_1085_ = lean_ctor_get(v___x_1084_, 0);
v_toEnvExtension_1086_ = lean_ctor_get(v_fst_1085_, 0);
v_asyncMode_1087_ = lean_ctor_get(v_toEnvExtension_1086_, 2);
v___x_1088_ = lean_box(0);
v___x_1089_ = 0;
v___x_1090_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1079_, v_toEnvExtension_1086_, v_env_1083_, v_asyncMode_1087_, v___x_1088_, v___x_1089_);
v_importedEntries_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc_ref(v_importedEntries_1091_);
v_state_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_state_1092_);
lean_dec(v___x_1090_);
v___x_1110_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1092_, v_trueName_1082_);
lean_dec(v_state_1092_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_NameSet_empty;
v___y_1094_ = v___x_1111_;
goto v___jp_1093_;
}
else
{
lean_object* v_val_1112_; 
v_val_1112_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v___x_1110_, 1);
v___y_1094_ = v_val_1112_;
goto v___jp_1093_;
}
v___jp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_array_get_size(v_importedEntries_1091_);
v___x_1097_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1098_ = lean_nat_dec_lt(v___x_1095_, v___x_1096_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v_importedEntries_1091_);
lean_dec_ref(v___f_1081_);
v___x_1099_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___y_1094_);
return v___x_1099_;
}
else
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_nat_dec_le(v___x_1096_, v___x_1096_);
if (v___x_1100_ == 0)
{
if (v___x_1098_ == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref(v_importedEntries_1091_);
lean_dec_ref(v___f_1081_);
v___x_1101_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___y_1094_);
return v___x_1101_;
}
else
{
size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = lean_usize_of_nat(v___x_1096_);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1097_, v___f_1081_, v_importedEntries_1091_, v___x_1102_, v___x_1103_, v___y_1094_);
v___x_1105_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___x_1104_);
return v___x_1105_;
}
}
else
{
size_t v___x_1106_; size_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = ((size_t)0ULL);
v___x_1107_ = lean_usize_of_nat(v___x_1096_);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1097_, v___f_1081_, v_importedEntries_1091_, v___x_1106_, v___x_1107_, v___y_1094_);
v___x_1109_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___x_1108_);
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0___boxed(lean_object* v___x_1113_, lean_object* v_toPure_1114_, lean_object* v___f_1115_, lean_object* v_trueName_1116_, lean_object* v_env_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_getStoredSuggestions___redArg___lam__0(v___x_1113_, v_toPure_1114_, v___f_1115_, v_trueName_1116_, v_env_1117_);
lean_dec(v_trueName_1116_);
lean_dec_ref(v___x_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_trueName_1121_){
_start:
{
lean_object* v_toApplicative_1122_; lean_object* v_toBind_1123_; lean_object* v_getEnv_1124_; lean_object* v_toPure_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v_toApplicative_1122_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc_ref(v_toApplicative_1122_);
v_toBind_1123_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc(v_toBind_1123_);
lean_dec_ref(v_inst_1119_);
v_getEnv_1124_ = lean_ctor_get(v_inst_1120_, 0);
lean_inc(v_getEnv_1124_);
lean_dec_ref(v_inst_1120_);
v_toPure_1125_ = lean_ctor_get(v_toApplicative_1122_, 1);
lean_inc(v_toPure_1125_);
lean_dec_ref(v_toApplicative_1122_);
v___f_1126_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
v___f_1127_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__1));
lean_inc(v_trueName_1121_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1128_, 0, v_trueName_1121_);
lean_closure_set(v___f_1128_, 1, v___f_1126_);
lean_closure_set(v___f_1128_, 2, v___f_1127_);
v___x_1129_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1130_, 0, v___x_1129_);
lean_closure_set(v___f_1130_, 1, v_toPure_1125_);
lean_closure_set(v___f_1130_, 2, v___f_1128_);
lean_closure_set(v___f_1130_, 3, v_trueName_1121_);
v___x_1131_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v_getEnv_1124_, v___f_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions(lean_object* v_m_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_trueName_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_getStoredSuggestions___redArg(v_inst_1133_, v_inst_1134_, v_trueName_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object* v_as_1137_, lean_object* v_k_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_m_1143_; lean_object* v_a_1144_; uint8_t v___x_1145_; 
v___x_1141_ = lean_nat_add(v_x_1139_, v_x_1140_);
v___x_1142_ = lean_unsigned_to_nat(1u);
v_m_1143_ = lean_nat_shiftr(v___x_1141_, v___x_1142_);
lean_dec(v___x_1141_);
v_a_1144_ = lean_array_fget_borrowed(v_as_1137_, v_m_1143_);
v___x_1145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_1144_, v_k_1138_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; 
lean_dec(v_x_1140_);
v___x_1146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_k_1138_, v_a_1144_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec(v_m_1143_);
lean_dec(v_x_1139_);
lean_inc(v_a_1144_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1144_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_nat_dec_eq(v_m_1143_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_nat_sub(v_m_1143_, v___x_1142_);
lean_dec(v_m_1143_);
v___x_1151_ = lean_nat_dec_lt(v___x_1150_, v_x_1139_);
if (v___x_1151_ == 0)
{
v_x_1140_ = v___x_1150_;
goto _start;
}
else
{
lean_object* v___x_1153_; 
lean_dec(v___x_1150_);
lean_dec(v_x_1139_);
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
}
else
{
lean_object* v___x_1154_; 
lean_dec(v_m_1143_);
lean_dec(v_x_1139_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
}
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
lean_dec(v_x_1139_);
v___x_1155_ = lean_nat_add(v_m_1143_, v___x_1142_);
lean_dec(v_m_1143_);
v___x_1156_ = lean_nat_dec_le(v___x_1155_, v_x_1140_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v___x_1155_);
lean_dec(v_x_1140_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
v_x_1139_ = v___x_1155_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object* v_as_1159_, lean_object* v_k_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1159_, v_k_1160_, v_x_1161_, v_x_1162_);
lean_dec_ref(v_k_1160_);
lean_dec_ref(v_as_1159_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object* v_incorrectName_1164_, lean_object* v_as_1165_, size_t v_i_1166_, size_t v_stop_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v___y_1170_; uint8_t v___x_1174_; 
v___x_1174_ = lean_usize_dec_eq(v_i_1166_, v_stop_1167_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1175_ = lean_array_uget_borrowed(v_as_1165_, v_i_1166_);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_array_get_size(v___x_1175_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
v___y_1170_ = v_b_1168_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_sub(v___x_1177_, v___x_1179_);
v___x_1181_ = lean_nat_dec_le(v___x_1176_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v___x_1180_);
v___y_1170_ = v_b_1168_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
lean_inc(v_incorrectName_1164_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_incorrectName_1164_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v___x_1175_, v___x_1183_, v___x_1176_, v___x_1180_);
lean_dec_ref_known(v___x_1183_, 2);
if (lean_obj_tag(v___x_1184_) == 0)
{
v___y_1170_ = v_b_1168_;
goto v___jp_1169_;
}
else
{
lean_object* v_val_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_val_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v_snd_1186_ = lean_ctor_get(v_val_1185_, 1);
lean_inc(v_snd_1186_);
lean_dec(v_val_1185_);
v___x_1187_ = lean_array_get_size(v_snd_1186_);
v___x_1188_ = lean_nat_dec_lt(v___x_1176_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_dec(v_snd_1186_);
v___y_1170_ = v_b_1168_;
goto v___jp_1169_;
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1187_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1186_, v___x_1189_, v___x_1190_, v_b_1168_);
lean_dec(v_snd_1186_);
v___y_1170_ = v___x_1191_;
goto v___jp_1169_;
}
}
}
}
}
else
{
lean_dec(v_incorrectName_1164_);
return v_b_1168_;
}
v___jp_1169_:
{
size_t v___x_1171_; size_t v___x_1172_; 
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_add(v_i_1166_, v___x_1171_);
v_i_1166_ = v___x_1172_;
v_b_1168_ = v___y_1170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object* v_incorrectName_1192_, lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_stop_1195_, lean_object* v_b_1196_){
_start:
{
size_t v_i_boxed_1197_; size_t v_stop_boxed_1198_; lean_object* v_res_1199_; 
v_i_boxed_1197_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_stop_boxed_1198_ = lean_unbox_usize(v_stop_1195_);
lean_dec(v_stop_1195_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1192_, v_as_1193_, v_i_boxed_1197_, v_stop_boxed_1198_, v_b_1196_);
lean_dec_ref(v_as_1193_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object* v_incorrectName_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_env_1205_; lean_object* v___x_1206_; lean_object* v_snd_1207_; lean_object* v_toEnvExtension_1208_; lean_object* v_asyncMode_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v_importedEntries_1213_; lean_object* v_state_1214_; lean_object* v___y_1216_; lean_object* v___x_1225_; 
v___x_1203_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___x_1204_ = lean_st_ref_get(v___y_1201_);
v_env_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_ref(v_env_1205_);
lean_dec(v___x_1204_);
v___x_1206_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_1207_ = lean_ctor_get(v___x_1206_, 1);
v_toEnvExtension_1208_ = lean_ctor_get(v_snd_1207_, 0);
v_asyncMode_1209_ = lean_ctor_get(v_toEnvExtension_1208_, 2);
v___x_1210_ = lean_box(0);
v___x_1211_ = 0;
v___x_1212_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1203_, v_toEnvExtension_1208_, v_env_1205_, v_asyncMode_1209_, v___x_1210_, v___x_1211_);
v_importedEntries_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_importedEntries_1213_);
v_state_1214_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_state_1214_);
lean_dec(v___x_1212_);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1214_, v_incorrectName_1200_);
lean_dec(v_state_1214_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_NameSet_empty;
v___y_1216_ = v___x_1226_;
goto v___jp_1215_;
}
else
{
lean_object* v_val_1227_; 
v_val_1227_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v___x_1225_, 1);
v___y_1216_ = v_val_1227_;
goto v___jp_1215_;
}
v___jp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_array_get_size(v_importedEntries_1213_);
v___x_1219_ = lean_nat_dec_lt(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
lean_dec_ref(v_importedEntries_1213_);
lean_dec(v_incorrectName_1200_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1216_);
return v___x_1220_;
}
else
{
size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = lean_usize_of_nat(v___x_1218_);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1200_, v_importedEntries_1213_, v___x_1221_, v___x_1222_, v___y_1216_);
lean_dec_ref(v_importedEntries_1213_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object* v_incorrectName_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1228_, v___y_1229_);
lean_dec(v___y_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object* v_x_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0));
v___x_1235_ = lean_string_append(v___x_1234_, v_x_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object* v_x_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(v_x_1236_);
lean_dec_ref(v_x_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, size_t v_sz_1246_, size_t v_i_1247_, lean_object* v_bs_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_usize_dec_lt(v_i_1247_, v_sz_1246_);
if (v___x_1249_ == 0)
{
lean_dec(v___x_1245_);
lean_dec(v___x_1244_);
lean_dec_ref(v___x_1243_);
return v_bs_1248_;
}
else
{
lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v_v_1252_; lean_object* v_bs_x27_1253_; lean_object* v___y_1255_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_nat_dec_eq(v___x_1241_, v___x_1250_);
v_v_1252_ = lean_array_uget(v_bs_1248_, v_i_1247_);
v_bs_x27_1253_ = lean_array_uset(v_bs_1248_, v_i_1247_, v___x_1250_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_inc(v_v_1252_);
v___y_1255_ = v_v_1252_;
goto v___jp_1254_;
}
else
{
lean_object* v_val_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_val_1272_ = lean_ctor_get(v___x_1242_, 0);
v___x_1273_ = lean_box(0);
lean_inc(v_v_1252_);
v___x_1274_ = l_Lean_Name_replacePrefix(v_v_1252_, v_val_1272_, v___x_1273_);
v___x_1275_ = l_Lean_Options_empty;
lean_inc(v___x_1274_);
lean_inc(v___x_1245_);
lean_inc(v___x_1244_);
lean_inc_ref(v___x_1243_);
v___x_1276_ = l_Lean_ResolveName_resolveGlobalName(v___x_1243_, v___x_1275_, v___x_1244_, v___x_1245_, v___x_1274_);
v___x_1277_ = l_List_lengthTR___redArg(v___x_1276_);
lean_dec(v___x_1276_);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_dec_eq(v___x_1277_, v___x_1278_);
lean_dec(v___x_1277_);
if (v___x_1279_ == 0)
{
lean_dec(v___x_1274_);
lean_inc(v_v_1252_);
v___y_1255_ = v_v_1252_;
goto v___jp_1254_;
}
else
{
v___y_1255_ = v___x_1274_;
goto v___jp_1254_;
}
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_1255_, v___x_1249_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1260_ = l_Lean_MessageData_ofConstName(v_v_1252_, v___x_1251_);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1259_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1));
v___x_1265_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1257_);
lean_ctor_set(v___x_1265_, 1, v___x_1258_);
lean_ctor_set(v___x_1265_, 2, v___x_1258_);
lean_ctor_set(v___x_1265_, 3, v___x_1258_);
lean_ctor_set(v___x_1265_, 4, v___x_1263_);
lean_ctor_set(v___x_1265_, 5, v___x_1264_);
v___x_1266_ = 0;
v___x_1267_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1258_);
lean_ctor_set(v___x_1267_, 2, v___x_1258_);
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*3, v___x_1266_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_i_1247_, v___x_1268_);
v___x_1270_ = lean_array_uset(v_bs_x27_1253_, v_i_1247_, v___x_1267_);
v_i_1247_ = v___x_1269_;
v_bs_1248_ = v___x_1270_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object* v___x_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v___x_1283_, lean_object* v___x_1284_, lean_object* v_sz_1285_, lean_object* v_i_1286_, lean_object* v_bs_1287_){
_start:
{
size_t v_sz_boxed_1288_; size_t v_i_boxed_1289_; lean_object* v_res_1290_; 
v_sz_boxed_1288_ = lean_unbox_usize(v_sz_1285_);
lean_dec(v_sz_1285_);
v_i_boxed_1289_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_res_1290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_1280_, v___x_1281_, v___x_1282_, v___x_1283_, v___x_1284_, v_sz_boxed_1288_, v_i_boxed_1289_, v_bs_1287_);
lean_dec(v___x_1281_);
lean_dec(v___x_1280_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(lean_object* v_msgData_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v_env_1298_; uint8_t v___x_1299_; lean_object* v_env_1300_; lean_object* v___x_1301_; lean_object* v_toCold_1302_; lean_object* v_mctx_1303_; lean_object* v_lctx_1304_; lean_object* v_options_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1297_ = lean_st_ref_get(v___y_1295_);
v_env_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref(v_env_1298_);
lean_dec(v___x_1297_);
v___x_1299_ = 0;
v_env_1300_ = l_Lean_Environment_setRecordingDeps(v_env_1298_, v___x_1299_);
v___x_1301_ = lean_st_ref_get(v___y_1293_);
v_toCold_1302_ = lean_ctor_get(v___y_1294_, 0);
v_mctx_1303_ = lean_ctor_get(v___x_1301_, 0);
lean_inc_ref(v_mctx_1303_);
lean_dec(v___x_1301_);
v_lctx_1304_ = lean_ctor_get(v___y_1292_, 2);
v_options_1305_ = lean_ctor_get(v_toCold_1302_, 2);
lean_inc_ref(v_options_1305_);
lean_inc_ref(v_lctx_1304_);
v___x_1306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1306_, 0, v_env_1300_);
lean_ctor_set(v___x_1306_, 1, v_mctx_1303_);
lean_ctor_set(v___x_1306_, 2, v_lctx_1304_);
lean_ctor_set(v___x_1306_, 3, v_options_1305_);
v___x_1307_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v_msgData_1291_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1315_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_box(1);
v___x_1317_ = l_Lean_MessageData_ofFormat(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2));
v___x_1322_ = l_Lean_MessageData_ofFormat(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
return v_x_1323_;
}
else
{
lean_object* v_head_1325_; lean_object* v_tail_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1348_; 
v_head_1325_ = lean_ctor_get(v_x_1324_, 0);
v_tail_1326_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1328_ = v_x_1324_;
v_isShared_1329_ = v_isSharedCheck_1348_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_tail_1326_);
lean_inc(v_head_1325_);
lean_dec(v_x_1324_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1348_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_before_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1346_; 
v_before_1330_ = lean_ctor_get(v_head_1325_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_head_1325_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_head_1325_, 1);
lean_dec(v_unused_1347_);
v___x_1332_ = v_head_1325_;
v_isShared_1333_ = v_isSharedCheck_1346_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_before_1330_);
lean_dec(v_head_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1346_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 7);
lean_ctor_set(v___x_1332_, 1, v___x_1334_);
lean_ctor_set(v___x_1332_, 0, v_x_1323_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_x_1323_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3);
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 7);
lean_ctor_set(v___x_1328_, 1, v___x_1337_);
lean_ctor_set(v___x_1328_, 0, v___x_1336_);
v___x_1339_ = v___x_1328_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = l_Lean_MessageData_ofSyntax(v_before_1330_);
v___x_1341_ = l_Lean_indentD(v___x_1340_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1339_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v_x_1323_ = v___x_1342_;
v_x_1324_ = v_tail_1326_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(lean_object* v_opts_1349_, lean_object* v_opt_1350_){
_start:
{
lean_object* v_name_1351_; lean_object* v_defValue_1352_; lean_object* v_map_1353_; lean_object* v___x_1354_; 
v_name_1351_ = lean_ctor_get(v_opt_1350_, 0);
v_defValue_1352_ = lean_ctor_get(v_opt_1350_, 1);
v_map_1353_ = lean_ctor_get(v_opts_1349_, 0);
v___x_1354_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1353_, v_name_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_unbox(v_defValue_1352_);
return v___x_1355_;
}
else
{
lean_object* v_val_1356_; 
v_val_1356_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1354_, 1);
if (lean_obj_tag(v_val_1356_) == 1)
{
uint8_t v_v_1357_; 
v_v_1357_ = lean_ctor_get_uint8(v_val_1356_, 0);
lean_dec_ref_known(v_val_1356_, 0);
return v_v_1357_;
}
else
{
uint8_t v___x_1358_; 
lean_dec(v_val_1356_);
v___x_1358_ = lean_unbox(v_defValue_1352_);
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(lean_object* v_opts_1359_, lean_object* v_opt_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_1359_, v_opt_1360_);
lean_dec_ref(v_opt_1360_);
lean_dec_ref(v_opts_1359_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1));
v___x_1367_ = l_Lean_MessageData_ofFormat(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(lean_object* v_msgData_1368_, lean_object* v_macroStack_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1370_);
v___x_1373_ = l_Lean_Elab_pp_macroStack;
v___x_1374_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v___x_1372_, v___x_1373_);
lean_dec_ref(v___x_1372_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v_macroStack_1369_);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_msgData_1368_);
return v___x_1375_;
}
else
{
if (lean_obj_tag(v_macroStack_1369_) == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_msgData_1368_);
return v___x_1376_;
}
else
{
lean_object* v_head_1377_; lean_object* v_after_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1393_; 
v_head_1377_ = lean_ctor_get(v_macroStack_1369_, 0);
lean_inc(v_head_1377_);
v_after_1378_ = lean_ctor_get(v_head_1377_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_head_1377_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v_head_1377_, 0);
lean_dec(v_unused_1394_);
v___x_1380_ = v_head_1377_;
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_after_1378_);
lean_dec(v_head_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 7);
lean_ctor_set(v___x_1380_, 1, v___x_1382_);
lean_ctor_set(v___x_1380_, 0, v_msgData_1368_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_msgData_1368_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_msgData_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1385_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = l_Lean_MessageData_ofSyntax(v_after_1378_);
v___x_1388_ = l_Lean_indentD(v___x_1387_);
v_msgData_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1389_, 0, v___x_1386_);
lean_ctor_set(v_msgData_1389_, 1, v___x_1388_);
v___x_1390_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(v_msgData_1389_, v_macroStack_1369_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_1395_, lean_object* v_macroStack_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1395_, v_macroStack_1396_, v___y_1397_);
lean_dec_ref(v___y_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(lean_object* v_msg_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_ref_1408_; lean_object* v_macroStack_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_ref_1408_ = lean_ctor_get(v___y_1405_, 2);
v_macroStack_1409_ = lean_ctor_get(v___y_1401_, 1);
v___x_1410_ = l_Lean_Elab_getBetterRef(v_ref_1408_, v_macroStack_1409_);
v___x_1411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msg_1400_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
lean_inc(v_macroStack_1409_);
v___x_1413_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_a_1412_, v_macroStack_1409_, v___y_1405_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1410_);
lean_ctor_set(v___x_1418_, 1, v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(lean_object* v_ref_1432_, lean_object* v_msg_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_toCold_1441_; lean_object* v_currRecDepth_1442_; lean_object* v_ref_1443_; uint16_t v_optionFlags_1444_; uint8_t v_suppressElabErrors_1445_; uint8_t v_isRecordingDeps_1446_; lean_object* v_ref_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_toCold_1441_ = lean_ctor_get(v___y_1438_, 0);
v_currRecDepth_1442_ = lean_ctor_get(v___y_1438_, 1);
v_ref_1443_ = lean_ctor_get(v___y_1438_, 2);
v_optionFlags_1444_ = lean_ctor_get_uint16(v___y_1438_, sizeof(void*)*3);
v_suppressElabErrors_1445_ = lean_ctor_get_uint8(v___y_1438_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1446_ = lean_ctor_get_uint8(v___y_1438_, sizeof(void*)*3 + 3);
v_ref_1447_ = l_Lean_replaceRef(v_ref_1432_, v_ref_1443_);
lean_inc(v_currRecDepth_1442_);
lean_inc_ref(v_toCold_1441_);
v___x_1448_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1448_, 0, v_toCold_1441_);
lean_ctor_set(v___x_1448_, 1, v_currRecDepth_1442_);
lean_ctor_set(v___x_1448_, 2, v_ref_1447_);
lean_ctor_set_uint16(v___x_1448_, sizeof(void*)*3, v_optionFlags_1444_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*3 + 2, v_suppressElabErrors_1445_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*3 + 3, v_isRecordingDeps_1446_);
v___x_1449_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___x_1448_, v___y_1439_);
lean_dec_ref_known(v___x_1448_, 3);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1450_, lean_object* v_msg_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1450_, v_msg_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v_ref_1450_);
return v_res_1459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2));
v___x_1465_ = l_Lean_stringToMessageData(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4));
v___x_1468_ = l_Lean_stringToMessageData(v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(lean_object* v_msg_1481_, lean_object* v_declHint_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_env_1487_; uint8_t v___x_1488_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_st_ref_get(v___y_1483_);
v_env_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_ref(v_env_1487_);
lean_dec(v___x_1486_);
v___x_1488_ = l_Lean_Name_isAnonymous(v_declHint_1482_);
if (v___x_1488_ == 0)
{
uint8_t v_isExporting_1489_; 
v_isExporting_1489_ = lean_ctor_get_uint8(v_env_1487_, sizeof(void*)*13);
if (v_isExporting_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec_ref(v_env_1487_);
lean_dec(v_declHint_1482_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_msg_1481_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
lean_inc_ref(v_env_1487_);
v___x_1491_ = l_Lean_Environment_setExporting(v_env_1487_, v___x_1488_);
lean_inc(v_declHint_1482_);
lean_inc_ref(v___x_1491_);
v___x_1492_ = l_Lean_Environment_contains(v___x_1491_, v_declHint_1482_, v_isExporting_1489_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v___x_1491_);
lean_dec_ref(v_env_1487_);
lean_dec(v_declHint_1482_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_msg_1481_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_c_1499_; lean_object* v___x_1500_; 
v___x_1494_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1495_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1496_ = l_Lean_Options_empty;
v___x_1497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1491_);
lean_ctor_set(v___x_1497_, 1, v___x_1494_);
lean_ctor_set(v___x_1497_, 2, v___x_1495_);
lean_ctor_set(v___x_1497_, 3, v___x_1496_);
lean_inc(v_declHint_1482_);
v___x_1498_ = l_Lean_MessageData_ofConstName(v_declHint_1482_, v___x_1488_);
v_c_1499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1499_, 0, v___x_1497_);
lean_ctor_set(v_c_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1487_, v_declHint_1482_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v_env_1487_);
lean_dec(v_declHint_1482_);
v___x_1501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v_c_1499_);
v___x_1503_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_MessageData_note(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_msg_1481_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
else
{
lean_object* v_val_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1542_; 
v_val_1508_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1510_ = v___x_1500_;
v_isShared_1511_ = v_isSharedCheck_1542_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_val_1508_);
lean_dec(v___x_1500_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1542_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_mod_1514_; uint8_t v___x_1515_; 
v___x_1512_ = l_Lean_Environment_header(v_env_1487_);
lean_dec_ref(v_env_1487_);
v___x_1513_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1512_);
v_mod_1514_ = lean_array_get(v___x_1485_, v___x_1513_, v_val_1508_);
lean_dec(v_val_1508_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = l_Lean_isPrivateName(v_declHint_1482_);
lean_dec(v_declHint_1482_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v_c_1499_);
v___x_1518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_MessageData_ofName(v_mod_1514_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_MessageData_note(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_msg_1481_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1525_);
v___x_1527_ = v___x_1510_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1529_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_c_1499_);
v___x_1531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_MessageData_ofName(v_mod_1514_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_MessageData_note(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_msg_1481_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1538_);
v___x_1540_ = v___x_1510_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1543_; 
lean_dec_ref(v_env_1487_);
lean_dec(v_declHint_1482_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_msg_1481_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1544_, lean_object* v_declHint_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1544_, v_declHint_1545_, v___y_1546_);
lean_dec(v___y_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(lean_object* v_msg_1549_, lean_object* v_declHint_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1568_; 
v___x_1558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1549_, v_declHint_1550_, v___y_1556_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = l_Lean_unknownIdentifierMessageTag;
v___x_1564_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(lean_object* v_msg_1569_, lean_object* v_declHint_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1569_, v_declHint_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(lean_object* v_ref_1579_, lean_object* v_msg_1580_, lean_object* v_declHint_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1591_; 
v___x_1589_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1580_, v_declHint_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1579_, v_a_1590_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(lean_object* v_ref_1592_, lean_object* v_msg_1593_, lean_object* v_declHint_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1592_, v_msg_1593_, v_declHint_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v_ref_1592_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2));
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg(lean_object* v_constName_1621_, lean_object* v_idOrConst_1622_, lean_object* v_declHint_1623_, lean_object* v_ref_x3f_1624_, lean_object* v_extraMsg_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___y_1634_; lean_object* v_hint_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___x_1704_; lean_object* v_a_1705_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1729_; 
lean_inc(v_constName_1621_);
v___x_1704_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_constName_1621_, v_a_1631_);
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref(v___x_1704_);
if (lean_obj_tag(v_a_1705_) == 0)
{
lean_object* v_size_1734_; 
v_size_1734_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_size_1734_);
v___y_1729_ = v_size_1734_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___y_1729_ = v___x_1735_;
goto v___jp_1728_;
}
v___jp_1633_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1642_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1);
v___x_1643_ = l_Lean_stringToMessageData(v_idOrConst_1622_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = 0;
v___x_1648_ = l_Lean_MessageData_ofConstName(v_constName_1621_, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_extraMsg_1625_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v_hint_1635_);
v___x_1654_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v___y_1634_, v___x_1653_, v_declHint_1623_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1634_);
return v___x_1654_;
}
v___jp_1655_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; size_t v_sz_1671_; size_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1666_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v___y_1660_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___y_1665_);
v___x_1669_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v_sz_1671_ = lean_array_size(v___y_1664_);
v___x_1672_ = ((size_t)0ULL);
lean_inc(v___y_1663_);
lean_inc(v___y_1662_);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___y_1656_, v___y_1659_, v___y_1657_, v___y_1662_, v___y_1663_, v_sz_1671_, v___x_1672_, v___y_1664_);
lean_dec(v___y_1659_);
lean_dec(v___y_1656_);
lean_inc(v___y_1658_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1658_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l_Lean_MessageData_hint(v___x_1670_, v___x_1673_, v___x_1674_, v___x_1675_, v___y_1661_, v_a_1630_, v_a_1631_);
lean_dec_ref(v___x_1673_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___y_1634_ = v___y_1658_;
v_hint_1635_ = v_a_1677_;
v___y_1636_ = v_a_1626_;
v___y_1637_ = v_a_1627_;
v___y_1638_ = v_a_1628_;
v___y_1639_ = v_a_1629_;
v___y_1640_ = v_a_1630_;
v___y_1641_ = v_a_1631_;
goto v___jp_1633_;
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v___y_1658_);
lean_dec_ref(v_extraMsg_1625_);
lean_dec(v_declHint_1623_);
lean_dec_ref(v_idOrConst_1622_);
lean_dec(v_constName_1621_);
v_a_1678_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1676_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1676_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
v___jp_1686_:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Lean_Name_isAnonymous(v___y_1687_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1698_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9);
v___x_1699_ = l_Lean_MessageData_ofName(v___y_1687_);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___y_1656_ = v___y_1688_;
v___y_1657_ = v___y_1689_;
v___y_1658_ = v___y_1691_;
v___y_1659_ = v___y_1690_;
v___y_1660_ = v___y_1696_;
v___y_1661_ = v___y_1692_;
v___y_1662_ = v___y_1693_;
v___y_1663_ = v___y_1695_;
v___y_1664_ = v___y_1694_;
v___y_1665_ = v___x_1702_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1703_; 
lean_dec(v___y_1687_);
v___x_1703_ = l_Lean_MessageData_nil;
v___y_1656_ = v___y_1688_;
v___y_1657_ = v___y_1689_;
v___y_1658_ = v___y_1691_;
v___y_1659_ = v___y_1690_;
v___y_1660_ = v___y_1696_;
v___y_1661_ = v___y_1692_;
v___y_1662_ = v___y_1693_;
v___y_1663_ = v___y_1695_;
v___y_1664_ = v___y_1694_;
v___y_1665_ = v___x_1703_;
goto v___jp_1655_;
}
}
v___jp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1709_ = lean_array_get_size(v___y_1707_);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_nat_dec_eq(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_toCold_1714_; lean_object* v_env_1715_; lean_object* v_currNamespace_1716_; lean_object* v_openDecls_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1712_ = l_Lean_Syntax_getId(v___y_1708_);
v___x_1713_ = lean_st_ref_get(v_a_1631_);
v_toCold_1714_ = lean_ctor_get(v_a_1630_, 0);
v_env_1715_ = lean_ctor_get(v___x_1713_, 0);
lean_inc_ref(v_env_1715_);
lean_dec(v___x_1713_);
v_currNamespace_1716_ = lean_ctor_get(v_toCold_1714_, 4);
v_openDecls_1717_ = lean_ctor_get(v_toCold_1714_, 5);
lean_inc(v_constName_1621_);
v___x_1718_ = l_Lean_Name_eraseSuffix_x3f(v_constName_1621_, v___x_1712_);
v___x_1719_ = lean_unsigned_to_nat(1u);
v___x_1720_ = lean_nat_dec_eq(v___x_1709_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11);
v___y_1687_ = v___x_1712_;
v___y_1688_ = v___x_1709_;
v___y_1689_ = v_env_1715_;
v___y_1690_ = v___x_1718_;
v___y_1691_ = v___y_1708_;
v___y_1692_ = v___x_1711_;
v___y_1693_ = v_currNamespace_1716_;
v___y_1694_ = v___y_1707_;
v___y_1695_ = v_openDecls_1717_;
v___y_1696_ = v___x_1721_;
goto v___jp_1686_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1722_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1723_ = lean_array_fget_borrowed(v___y_1707_, v___x_1710_);
lean_inc(v___x_1723_);
v___x_1724_ = l_Lean_MessageData_ofConstName(v___x_1723_, v___x_1711_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1722_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v___x_1722_);
v___y_1687_ = v___x_1712_;
v___y_1688_ = v___x_1709_;
v___y_1689_ = v_env_1715_;
v___y_1690_ = v___x_1718_;
v___y_1691_ = v___y_1708_;
v___y_1692_ = v___x_1711_;
v___y_1693_ = v_currNamespace_1716_;
v___y_1694_ = v___y_1707_;
v___y_1695_ = v_openDecls_1717_;
v___y_1696_ = v___x_1726_;
goto v___jp_1686_;
}
}
else
{
lean_object* v___x_1727_; 
lean_dec_ref(v___y_1707_);
v___x_1727_ = l_Lean_MessageData_nil;
v___y_1634_ = v___y_1708_;
v_hint_1635_ = v___x_1727_;
v___y_1636_ = v_a_1626_;
v___y_1637_ = v_a_1627_;
v___y_1638_ = v_a_1628_;
v___y_1639_ = v_a_1629_;
v___y_1640_ = v_a_1630_;
v___y_1641_ = v_a_1631_;
goto v___jp_1633_;
}
}
v___jp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_mk_empty_array_with_capacity(v___y_1729_);
lean_dec(v___y_1729_);
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_1730_, v_a_1705_);
if (lean_obj_tag(v_ref_x3f_1624_) == 0)
{
lean_object* v_ref_1732_; 
v_ref_1732_ = lean_ctor_get(v_a_1630_, 2);
lean_inc(v_ref_1732_);
v___y_1707_ = v___x_1731_;
v___y_1708_ = v_ref_1732_;
goto v___jp_1706_;
}
else
{
lean_object* v_val_1733_; 
v_val_1733_ = lean_ctor_get(v_ref_x3f_1624_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v_ref_x3f_1624_, 1);
v___y_1707_ = v___x_1731_;
v___y_1708_ = v_val_1733_;
goto v___jp_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(lean_object* v_constName_1736_, lean_object* v_idOrConst_1737_, lean_object* v_declHint_1738_, lean_object* v_ref_x3f_1739_, lean_object* v_extraMsg_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1736_, v_idOrConst_1737_, v_declHint_1738_, v_ref_x3f_1739_, v_extraMsg_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions(lean_object* v_00_u03b1_1749_, lean_object* v_constName_1750_, lean_object* v_idOrConst_1751_, lean_object* v_declHint_1752_, lean_object* v_ref_x3f_1753_, lean_object* v_extraMsg_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1750_, v_idOrConst_1751_, v_declHint_1752_, v_ref_x3f_1753_, v_extraMsg_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_constName_1764_, lean_object* v_idOrConst_1765_, lean_object* v_declHint_1766_, lean_object* v_ref_x3f_1767_, lean_object* v_extraMsg_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_throwUnknownNameWithSuggestions(v_00_u03b1_1763_, v_constName_1764_, v_idOrConst_1765_, v_declHint_1766_, v_ref_x3f_1767_, v_extraMsg_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(lean_object* v_incorrectName_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1777_, v___y_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(lean_object* v_incorrectName_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(v_incorrectName_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_object* v_00_u03b1_1795_, lean_object* v_ref_1796_, lean_object* v_msg_1797_, lean_object* v_declHint_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1796_, v_msg_1797_, v_declHint_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_ref_1808_, lean_object* v_msg_1809_, lean_object* v_declHint_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(v_00_u03b1_1807_, v_ref_1808_, v_msg_1809_, v_declHint_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v_ref_1808_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(lean_object* v_as_1819_, lean_object* v_k_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1819_, v_k_1820_, v_x_1821_, v_x_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(lean_object* v_as_1825_, lean_object* v_k_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(v_as_1825_, v_k_1826_, v_x_1827_, v_x_1828_, v_x_1829_);
lean_dec_ref(v_k_1826_);
lean_dec_ref(v_as_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(lean_object* v_msg_1831_, lean_object* v_declHint_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1831_, v_declHint_1832_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1841_, lean_object* v_declHint_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_1841_, v_declHint_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_object* v_00_u03b1_1851_, lean_object* v_ref_1852_, lean_object* v_msg_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1852_, v_msg_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1862_, lean_object* v_ref_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(v_00_u03b1_1862_, v_ref_1863_, v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_ref_1863_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1873_, lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(v_00_u03b1_1883_, v_msg_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(lean_object* v_msgData_1893_, lean_object* v_macroStack_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1893_, v_macroStack_1894_, v___y_1899_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(lean_object* v_msgData_1903_, lean_object* v_macroStack_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_1903_, v_macroStack_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1912_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(lean_object* v_exp_1913_, lean_object* v_as_1914_, size_t v_i_1915_, size_t v_stop_1916_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_eq(v_i_1915_, v_stop_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = lean_array_uget_borrowed(v_as_1914_, v_i_1915_);
v___x_1919_ = lean_expr_eqv(v___x_1918_, v_exp_1913_);
if (v___x_1919_ == 0)
{
size_t v___x_1920_; size_t v___x_1921_; 
v___x_1920_ = ((size_t)1ULL);
v___x_1921_ = lean_usize_add(v_i_1915_, v___x_1920_);
v_i_1915_ = v___x_1921_;
goto _start;
}
else
{
return v___x_1919_;
}
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = 0;
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(lean_object* v_exp_1924_, lean_object* v_as_1925_, lean_object* v_i_1926_, lean_object* v_stop_1927_){
_start:
{
size_t v_i_boxed_1928_; size_t v_stop_boxed_1929_; uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_i_boxed_1928_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_stop_boxed_1929_ = lean_unbox_usize(v_stop_1927_);
lean_dec(v_stop_1927_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1924_, v_as_1925_, v_i_boxed_1928_, v_stop_boxed_1929_);
lean_dec_ref(v_as_1925_);
lean_dec_ref(v_exp_1924_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(lean_object* v_exp_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v_cs_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_cs_1934_ = lean_ctor_get(v_x_1933_, 0);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_array_get_size(v_cs_1934_);
v___x_1937_ = lean_nat_dec_lt(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
return v___x_1937_;
}
else
{
if (v___x_1937_ == 0)
{
return v___x_1937_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1936_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1932_, v_cs_1934_, v___x_1938_, v___x_1939_);
return v___x_1940_;
}
}
}
else
{
lean_object* v_vs_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_vs_1941_ = lean_ctor_get(v_x_1933_, 0);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_array_get_size(v_vs_1941_);
v___x_1944_ = lean_nat_dec_lt(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
return v___x_1944_;
}
else
{
if (v___x_1944_ == 0)
{
return v___x_1944_;
}
else
{
size_t v___x_1945_; size_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = lean_usize_of_nat(v___x_1943_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1932_, v_vs_1941_, v___x_1945_, v___x_1946_);
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(lean_object* v_exp_1948_, lean_object* v_as_1949_, size_t v_i_1950_, size_t v_stop_1951_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_usize_dec_eq(v_i_1950_, v_stop_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1953_ = lean_array_uget_borrowed(v_as_1949_, v_i_1950_);
v___x_1954_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1948_, v___x_1953_);
if (v___x_1954_ == 0)
{
size_t v___x_1955_; size_t v___x_1956_; 
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1950_, v___x_1955_);
v_i_1950_ = v___x_1956_;
goto _start;
}
else
{
return v___x_1954_;
}
}
else
{
uint8_t v___x_1958_; 
v___x_1958_ = 0;
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(lean_object* v_exp_1959_, lean_object* v_as_1960_, lean_object* v_i_1961_, lean_object* v_stop_1962_){
_start:
{
size_t v_i_boxed_1963_; size_t v_stop_boxed_1964_; uint8_t v_res_1965_; lean_object* v_r_1966_; 
v_i_boxed_1963_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_stop_boxed_1964_ = lean_unbox_usize(v_stop_1962_);
lean_dec(v_stop_1962_);
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1959_, v_as_1960_, v_i_boxed_1963_, v_stop_boxed_1964_);
lean_dec_ref(v_as_1960_);
lean_dec_ref(v_exp_1959_);
v_r_1966_ = lean_box(v_res_1965_);
return v_r_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(lean_object* v_exp_1967_, lean_object* v_x_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1967_, v_x_1968_);
lean_dec_ref(v_x_1968_);
lean_dec_ref(v_exp_1967_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(lean_object* v_exp_1971_, lean_object* v_t_1972_){
_start:
{
lean_object* v_root_1973_; lean_object* v_tail_1974_; uint8_t v___x_1975_; 
v_root_1973_ = lean_ctor_get(v_t_1972_, 0);
v_tail_1974_ = lean_ctor_get(v_t_1972_, 1);
v___x_1975_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1971_, v_root_1973_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_array_get_size(v_tail_1974_);
v___x_1978_ = lean_nat_dec_lt(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
return v___x_1978_;
}
else
{
if (v___x_1978_ == 0)
{
return v___x_1978_;
}
else
{
size_t v___x_1979_; size_t v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = lean_usize_of_nat(v___x_1977_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1971_, v_tail_1974_, v___x_1979_, v___x_1980_);
return v___x_1981_;
}
}
}
else
{
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(lean_object* v_exp_1982_, lean_object* v_t_1983_){
_start:
{
uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_res_1984_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_1982_, v_t_1983_);
lean_dec_ref(v_t_1983_);
lean_dec_ref(v_exp_1982_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(lean_object* v_init_1986_, lean_object* v_x_1987_){
_start:
{
if (lean_obj_tag(v_x_1987_) == 0)
{
lean_object* v_k_1988_; lean_object* v_l_1989_; lean_object* v_r_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_k_1988_ = lean_ctor_get(v_x_1987_, 1);
v_l_1989_ = lean_ctor_get(v_x_1987_, 3);
v_r_1990_ = lean_ctor_get(v_x_1987_, 4);
v___x_1991_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1986_, v_r_1990_);
lean_inc(v_k_1988_);
v___x_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_k_1988_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v_init_1986_ = v___x_1992_;
v_x_1987_ = v_l_1989_;
goto _start;
}
else
{
return v_init_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(lean_object* v_init_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1994_, v_x_1995_);
lean_dec(v_x_1995_);
return v_res_1996_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0));
v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = l_List_reverse___redArg(v_a_2001_);
return v___x_2002_;
}
else
{
lean_object* v_head_2003_; lean_object* v_tail_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2019_; 
v_head_2003_ = lean_ctor_get(v_a_2000_, 0);
v_tail_2004_ = lean_ctor_get(v_a_2000_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2006_ = v_a_2000_;
v_isShared_2007_ = v_isSharedCheck_2019_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_tail_2004_);
lean_inc(v_head_2003_);
lean_dec(v_a_2000_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2019_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2008_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1);
v___x_2009_ = 0;
v___x_2010_ = l_Lean_MessageData_ofConstName(v_head_2003_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2008_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Lean_indentD(v___x_2013_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v_a_2001_);
lean_ctor_set(v___x_2006_, 0, v___x_2014_);
v___x_2016_ = v___x_2006_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_a_2001_);
v___x_2016_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v_a_2000_ = v_tail_2004_;
v_a_2001_ = v___x_2016_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0));
v___x_2022_ = l_Lean_stringToMessageData(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15));
v___x_2045_ = l_Lean_stringToMessageData(v___x_2044_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(lean_object* v_exp_2049_, lean_object* v_expected_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_autoBoundImplicitContext_2059_; 
v_autoBoundImplicitContext_2059_ = lean_ctor_get(v_a_2051_, 2);
if (lean_obj_tag(v_autoBoundImplicitContext_2059_) == 0)
{
lean_dec_ref(v_expected_2050_);
goto v___jp_2056_;
}
else
{
lean_object* v_val_2060_; uint8_t v___x_2061_; 
v_val_2060_ = lean_ctor_get(v_autoBoundImplicitContext_2059_, 0);
v___x_2061_ = l_Lean_Expr_isFVar(v_exp_2049_);
if (v___x_2061_ == 0)
{
lean_dec_ref(v_expected_2050_);
goto v___jp_2056_;
}
else
{
lean_object* v_boundVariables_2062_; uint8_t v___x_2063_; 
v_boundVariables_2062_ = lean_ctor_get(v_val_2060_, 0);
v___x_2063_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_2049_, v_boundVariables_2062_);
if (v___x_2063_ == 0)
{
lean_dec_ref(v_expected_2050_);
goto v___jp_2056_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = l_Lean_Expr_fvarId_x21(v_exp_2049_);
v___x_2065_ = l_Lean_FVarId_getUserName___redArg(v___x_2064_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2124_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_n(v_a_2066_, 2);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1);
v___x_2068_ = l_Lean_MessageData_ofName(v_a_2066_);
lean_inc_ref(v___x_2068_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_stringToMessageData(v_expected_2050_);
lean_inc_ref(v___x_2072_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2072_);
v___x_2077_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_a_2066_, v_a_2054_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2124_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2124_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___y_2085_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v___x_2091_, v_a_2080_);
lean_dec(v_a_2080_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v___x_2068_);
v___x_2093_ = l_Lean_MessageData_nil;
v___y_2085_ = v___x_2093_;
goto v___jp_2084_;
}
else
{
lean_object* v_tail_2094_; 
v_tail_2094_ = lean_ctor_get(v___x_2092_, 1);
if (lean_obj_tag(v_tail_2094_) == 0)
{
lean_object* v_head_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2112_; 
v_head_2095_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v___x_2092_, 1);
lean_dec(v_unused_2113_);
v___x_2097_ = v___x_2092_;
v_isShared_2098_ = v_isSharedCheck_2112_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_head_2095_);
lean_dec(v___x_2092_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2112_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2099_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2100_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10);
v___x_2101_ = 0;
v___x_2102_ = l_Lean_MessageData_ofConstName(v_head_2095_, v___x_2101_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 7);
lean_ctor_set(v___x_2097_, 1, v___x_2102_);
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2104_ = v___x_2097_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2105_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2068_);
v___x_2108_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2099_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___y_2085_ = v___x_2110_;
goto v___jp_2084_;
}
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2114_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2115_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2068_);
v___x_2117_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2114_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(v___x_2092_, v___x_2091_);
v___x_2121_ = l_Lean_MessageData_nil;
v___x_2122_ = l_Lean_MessageData_joinSep(v___x_2120_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2119_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___y_2085_ = v___x_2123_;
goto v___jp_2084_;
}
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2078_);
lean_ctor_set(v___x_2086_, 1, v___y_2085_);
v___x_2087_ = l_Lean_MessageData_hint_x27(v___x_2086_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2087_);
v___x_2089_ = v___x_2082_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_expected_2050_);
v_a_2125_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2065_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2065_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = l_Lean_MessageData_nil;
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(lean_object* v_exp_2133_, lean_object* v_expected_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2133_, v_expected_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec_ref(v_exp_2133_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure(lean_object* v_exp_2141_, lean_object* v_expected_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2141_, v_expected_2142_, v_a_2143_, v_a_2145_, v_a_2147_, v_a_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(lean_object* v_exp_2151_, lean_object* v_expected_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Elab_Term_hintAutoImplicitFailure(v_exp_2151_, v_expected_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_exp_2151_);
return v_res_2160_;
}
}
lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ErrorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_IdentifierSuggestion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_IdentifierSuggestion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin);
lean_object* initialize_Lean_Elab_ErrorUtils(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_IdentifierSuggestion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ErrorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_IdentifierSuggestion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_IdentifierSuggestion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_IdentifierSuggestion(builtin);
}
#ifdef __cplusplus
}
#endif
