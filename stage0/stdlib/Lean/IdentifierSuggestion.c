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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__21;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_11_;
v_res_11_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_as_1_, v_i_2_, v_stop_3_, v_b_4_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4___boxed(lean_object* v_as_12_, lean_object* v_i_13_, lean_object* v_stop_14_, lean_object* v_b_15_){
_start:
{
size_t v_i_boxed_16_; size_t v_stop_boxed_17_; lean_object* v_res_18_; 
v_i_boxed_16_ = lean_unbox_usize(v_i_13_);
lean_dec(v_i_13_);
v_stop_boxed_17_ = lean_unbox_usize(v_stop_14_);
lean_dec(v_stop_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_as_12_, v_i_boxed_16_, v_stop_boxed_17_, v_b_15_);
lean_dec_ref(v_as_12_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(lean_object* v_snd_19_, lean_object* v_old_20_){
_start:
{
lean_object* v___y_22_; 
if (lean_obj_tag(v_old_20_) == 0)
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_NameSet_empty;
v___y_22_ = v___x_37_;
goto v___jp_21_;
}
else
{
lean_object* v_val_38_; 
v_val_38_ = lean_ctor_get(v_old_20_, 0);
lean_inc(v_val_38_);
lean_dec_ref_known(v_old_20_, 1);
v___y_22_ = v_val_38_;
goto v___jp_21_;
}
v___jp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_array_get_size(v_snd_19_);
v___x_25_ = lean_nat_dec_lt(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___y_22_);
return v___x_26_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_le(v___x_24_, v___x_24_);
if (v___x_27_ == 0)
{
if (v___x_25_ == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___y_22_);
return v___x_28_;
}
else
{
size_t v___x_29_; size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_29_ = ((size_t)0ULL);
v___x_30_ = lean_usize_of_nat(v___x_24_);
v___x_31_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_19_, v___x_29_, v___x_30_, v___y_22_);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
else
{
size_t v___x_33_; size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_33_ = ((size_t)0ULL);
v___x_34_ = lean_usize_of_nat(v___x_24_);
v___x_35_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_19_, v___x_33_, v___x_34_, v___y_22_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0___boxed(lean_object* v_snd_39_, lean_object* v_old_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_39_, v_old_40_);
lean_dec_ref(v_snd_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(lean_object* v_snd_42_, lean_object* v_k_43_, lean_object* v_t_44_){
_start:
{
if (lean_obj_tag(v_t_44_) == 0)
{
lean_object* v_size_45_; lean_object* v_k_46_; lean_object* v_v_47_; lean_object* v_l_48_; lean_object* v_r_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_64_; 
v_size_45_ = lean_ctor_get(v_t_44_, 0);
v_k_46_ = lean_ctor_get(v_t_44_, 1);
v_v_47_ = lean_ctor_get(v_t_44_, 2);
v_l_48_ = lean_ctor_get(v_t_44_, 3);
v_r_49_ = lean_ctor_get(v_t_44_, 4);
v_isSharedCheck_64_ = !lean_is_exclusive(v_t_44_);
if (v_isSharedCheck_64_ == 0)
{
v___x_51_ = v_t_44_;
v_isShared_52_ = v_isSharedCheck_64_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_r_49_);
lean_inc(v_l_48_);
lean_inc(v_v_47_);
lean_inc(v_k_46_);
lean_inc(v_size_45_);
lean_dec(v_t_44_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_64_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; 
v___x_53_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_43_, v_k_46_);
switch(v___x_53_)
{
case 0:
{
lean_object* v_impl_54_; lean_object* v___x_55_; 
lean_del_object(v___x_51_);
lean_dec(v_size_45_);
v_impl_54_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_42_, v_k_43_, v_l_48_);
v___x_55_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_46_, v_v_47_, v_impl_54_, v_r_49_);
return v___x_55_;
}
case 1:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v_val_58_; lean_object* v___x_60_; 
lean_dec(v_k_46_);
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v_v_47_);
v___x_57_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_42_, v___x_56_);
v_val_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_val_58_);
lean_dec(v___x_57_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 2, v_val_58_);
lean_ctor_set(v___x_51_, 1, v_k_43_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_size_45_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_k_43_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v_val_58_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v_l_48_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v_r_49_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
default: 
{
lean_object* v_impl_62_; lean_object* v___x_63_; 
lean_del_object(v___x_51_);
lean_dec(v_size_45_);
v_impl_62_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_42_, v_k_43_, v_r_49_);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_46_, v_v_47_, v_l_48_, v_impl_62_);
return v___x_63_;
}
}
}
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_val_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = lean_box(0);
v___x_66_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_42_, v___x_65_);
v_val_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_67_);
lean_dec(v___x_66_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_k_43_);
lean_ctor_set(v___x_69_, 2, v_val_67_);
lean_ctor_set(v___x_69_, 3, v_t_44_);
lean_ctor_set(v___x_69_, 4, v_t_44_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___boxed(lean_object* v_snd_70_, lean_object* v_k_71_, lean_object* v_t_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_70_, v_k_71_, v_t_72_);
lean_dec_ref(v_snd_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__0(lean_object* v_table_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v___x_78_; 
v_fst_76_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_fst_76_);
v_snd_77_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_snd_77_);
lean_dec_ref(v_x_75_);
v___x_78_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_77_, v_fst_76_, v_table_74_);
lean_dec(v_snd_77_);
return v___x_78_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
lean_object* v_fst_81_; lean_object* v_fst_82_; uint8_t v___x_83_; 
v_fst_81_ = lean_ctor_get(v_a_79_, 0);
v_fst_82_ = lean_ctor_get(v_b_80_, 0);
v___x_83_ = l_Lean_Name_quickLt(v_fst_81_, v_fst_82_);
return v___x_83_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_79_ = stack[0].m_obj;
lean_object* v_b_80_ = stack[1].m_obj;
uint8_t v_res_84_;
v_res_84_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_79_, v_b_80_);
stack->m_num = v_res_84_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed(lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_85_, v_b_86_);
lean_dec_ref(v_b_86_);
lean_dec_ref(v_a_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(lean_object* v_hi_89_, lean_object* v_pivot_90_, lean_object* v_as_91_, lean_object* v_i_92_, lean_object* v_k_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_lt(v_k_93_, v_hi_89_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_k_93_);
v___x_95_ = lean_array_fswap(v_as_91_, v_i_92_, v_hi_89_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_i_92_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v_fst_98_; lean_object* v_fst_99_; uint8_t v___x_100_; 
v___x_97_ = lean_array_fget_borrowed(v_as_91_, v_k_93_);
v_fst_98_ = lean_ctor_get(v___x_97_, 0);
v_fst_99_ = lean_ctor_get(v_pivot_90_, 0);
v___x_100_ = l_Lean_Name_quickLt(v_fst_98_, v_fst_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_k_93_, v___x_101_);
lean_dec(v_k_93_);
v_k_93_ = v___x_102_;
goto _start;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_array_fswap(v_as_91_, v_i_92_, v_k_93_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_i_92_, v___x_105_);
lean_dec(v_i_92_);
v___x_107_ = lean_nat_add(v_k_93_, v___x_105_);
lean_dec(v_k_93_);
v_as_91_ = v___x_104_;
v_i_92_ = v___x_106_;
v_k_93_ = v___x_107_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg___boxed(lean_object* v_hi_109_, lean_object* v_pivot_110_, lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_k_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_109_, v_pivot_110_, v_as_111_, v_i_112_, v_k_113_);
lean_dec_ref(v_pivot_110_);
lean_dec(v_hi_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(lean_object* v_n_115_, lean_object* v_as_116_, lean_object* v_lo_117_, lean_object* v_hi_118_){
_start:
{
lean_object* v___y_120_; uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_lt(v_lo_117_, v_hi_118_);
if (v___x_130_ == 0)
{
lean_dec(v_lo_117_);
return v_as_116_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_mid_133_; lean_object* v___y_135_; lean_object* v___y_141_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_131_ = lean_nat_add(v_lo_117_, v_hi_118_);
v___x_132_ = lean_unsigned_to_nat(1u);
v_mid_133_ = lean_nat_shiftr(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
v___x_146_ = lean_array_fget_borrowed(v_as_116_, v_mid_133_);
v___x_147_ = lean_array_fget_borrowed(v_as_116_, v_lo_117_);
v___x_148_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
v___y_141_ = v_as_116_;
goto v___jp_140_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_array_fswap(v_as_116_, v_lo_117_, v_mid_133_);
v___y_141_ = v___x_149_;
goto v___jp_140_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_array_fget_borrowed(v___y_135_, v_mid_133_);
v___x_137_ = lean_array_fget_borrowed(v___y_135_, v_hi_118_);
v___x_138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_dec(v_mid_133_);
v___y_120_ = v___y_135_;
goto v___jp_119_;
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_array_fswap(v___y_135_, v_mid_133_, v_hi_118_);
lean_dec(v_mid_133_);
v___y_120_ = v___x_139_;
goto v___jp_119_;
}
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_142_ = lean_array_fget_borrowed(v___y_141_, v_hi_118_);
v___x_143_ = lean_array_fget_borrowed(v___y_141_, v_lo_117_);
v___x_144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
v___y_135_ = v___y_141_;
goto v___jp_134_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_array_fswap(v___y_141_, v_lo_117_, v_hi_118_);
v___y_135_ = v___x_145_;
goto v___jp_134_;
}
}
}
v___jp_119_:
{
lean_object* v_pivot_121_; lean_object* v___x_122_; lean_object* v_fst_123_; lean_object* v_snd_124_; uint8_t v___x_125_; 
v_pivot_121_ = lean_array_fget(v___y_120_, v_hi_118_);
lean_inc_n(v_lo_117_, 2);
v___x_122_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_118_, v_pivot_121_, v___y_120_, v_lo_117_, v_lo_117_);
lean_dec(v_pivot_121_);
v_fst_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_fst_123_);
v_snd_124_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_snd_124_);
lean_dec_ref(v___x_122_);
v___x_125_ = lean_nat_dec_le(v_hi_118_, v_fst_123_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_115_, v_snd_124_, v_lo_117_, v_fst_123_);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_fst_123_, v___x_127_);
lean_dec(v_fst_123_);
v_as_116_ = v___x_126_;
v_lo_117_ = v___x_128_;
goto _start;
}
else
{
lean_dec(v_fst_123_);
lean_dec(v_lo_117_);
return v_snd_124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___boxed(lean_object* v_n_150_, lean_object* v_as_151_, lean_object* v_lo_152_, lean_object* v_hi_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_150_, v_as_151_, v_lo_152_, v_hi_153_);
lean_dec(v_hi_153_);
lean_dec(v_n_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(lean_object* v_init_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v_k_157_; lean_object* v_l_158_; lean_object* v_r_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_k_157_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_k_157_);
v_l_158_ = lean_ctor_get(v_x_156_, 3);
lean_inc(v_l_158_);
v_r_159_ = lean_ctor_get(v_x_156_, 4);
lean_inc(v_r_159_);
lean_dec_ref_known(v_x_156_, 5);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_155_, v_l_158_);
v___x_161_ = lean_array_push(v___x_160_, v_k_157_);
v_init_155_ = v___x_161_;
v_x_156_ = v_r_159_;
goto _start;
}
else
{
return v_init_155_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(size_t v_sz_163_, size_t v_i_164_, lean_object* v_bs_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_lt(v_i_164_, v_sz_163_);
if (v___x_166_ == 0)
{
return v_bs_165_;
}
else
{
lean_object* v_v_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_187_; 
v_v_167_ = lean_array_uget(v_bs_165_, v_i_164_);
v_fst_168_ = lean_ctor_get(v_v_167_, 0);
v_snd_169_ = lean_ctor_get(v_v_167_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_v_167_);
if (v_isSharedCheck_187_ == 0)
{
v___x_171_ = v_v_167_;
v_isShared_172_ = v_isSharedCheck_187_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_snd_169_);
lean_inc(v_fst_168_);
lean_dec(v_v_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_187_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v_bs_x27_174_; lean_object* v___y_176_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v_bs_x27_174_ = lean_array_uset(v_bs_165_, v_i_164_, v___x_173_);
if (lean_obj_tag(v_snd_169_) == 0)
{
lean_object* v_size_186_; 
v_size_186_ = lean_ctor_get(v_snd_169_, 0);
lean_inc(v_size_186_);
v___y_176_ = v_size_186_;
goto v___jp_175_;
}
else
{
v___y_176_ = v___x_173_;
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = lean_mk_empty_array_with_capacity(v___y_176_);
lean_dec(v___y_176_);
v___x_178_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_177_, v_snd_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_178_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_fst_168_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_185_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((size_t)1ULL);
v___x_182_ = lean_usize_add(v_i_164_, v___x_181_);
v___x_183_ = lean_array_uset(v_bs_x27_174_, v_i_164_, v___x_180_);
v_i_164_ = v___x_182_;
v_bs_165_ = v___x_183_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_163_ = stack[0].m_num;
size_t v_i_164_ = stack[1].m_num;
lean_object* v_bs_165_ = stack[2].m_obj;
lean_object* v_res_188_;
v_res_188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_163_, v_i_164_, v_bs_165_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2___boxed(lean_object* v_sz_189_, lean_object* v_i_190_, lean_object* v_bs_191_){
_start:
{
size_t v_sz_boxed_192_; size_t v_i_boxed_193_; lean_object* v_res_194_; 
v_sz_boxed_192_ = lean_unbox_usize(v_sz_189_);
lean_dec(v_sz_189_);
v_i_boxed_193_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_boxed_192_, v_i_boxed_193_, v_bs_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(lean_object* v_init_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_k_197_; lean_object* v_v_198_; lean_object* v_l_199_; lean_object* v_r_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_k_197_ = lean_ctor_get(v_x_196_, 1);
v_v_198_ = lean_ctor_get(v_x_196_, 2);
v_l_199_ = lean_ctor_get(v_x_196_, 3);
v_r_200_ = lean_ctor_get(v_x_196_, 4);
v___x_201_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_195_, v_l_199_);
lean_inc(v_v_198_);
lean_inc(v_k_197_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_k_197_);
lean_ctor_set(v___x_202_, 1, v_v_198_);
v___x_203_ = lean_array_push(v___x_201_, v___x_202_);
v_init_195_ = v___x_203_;
v_x_196_ = v_r_200_;
goto _start;
}
else
{
return v_init_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2___boxed(lean_object* v_init_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_205_, v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(lean_object* v_x_210_, lean_object* v_s_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; size_t v_sz_215_; size_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___x_224_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0));
v___x_214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_213_, v_s_211_);
v_sz_215_ = lean_array_size(v___x_214_);
v___x_216_ = ((size_t)0ULL);
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_215_, v___x_216_, v___x_214_);
v___x_218_ = lean_array_get_size(v___x_217_);
v___x_224_ = lean_nat_dec_eq(v___x_218_, v___x_212_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___y_228_; uint8_t v___x_230_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_sub(v___x_218_, v___x_225_);
v___x_230_ = lean_nat_dec_le(v___x_212_, v___x_226_);
if (v___x_230_ == 0)
{
lean_inc(v___x_226_);
v___y_228_ = v___x_226_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___x_212_;
goto v___jp_227_;
}
v___jp_227_:
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_le(v___y_228_, v___x_226_);
if (v___x_229_ == 0)
{
lean_dec(v___x_226_);
lean_inc(v___y_228_);
v___y_220_ = v___y_228_;
v___y_221_ = v___y_228_;
goto v___jp_219_;
}
else
{
v___y_220_ = v___y_228_;
v___y_221_ = v___x_226_;
goto v___jp_219_;
}
}
}
else
{
lean_object* v___x_231_; 
lean_inc_ref_n(v___x_217_, 2);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_217_);
lean_ctor_set(v___x_231_, 1, v___x_217_);
lean_ctor_set(v___x_231_, 2, v___x_217_);
return v___x_231_;
}
v___jp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_218_, v___x_217_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_inc_ref_n(v___x_222_, 2);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed(lean_object* v_x_232_, lean_object* v_s_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(v_x_232_, v_s_233_);
lean_dec(v_s_233_);
lean_dec_ref(v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed(lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(v_x_237_);
lean_dec(v_x_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(lean_object* v_table_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; size_t v_sz_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0));
v___x_242_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_241_, v_table_239_);
v_sz_243_ = lean_array_size(v___x_242_);
v___x_244_ = ((size_t)0ULL);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_243_, v___x_244_, v___x_242_);
v___x_246_ = lean_array_get_size(v___x_245_);
v___x_247_ = lean_nat_dec_eq(v___x_246_, v___x_240_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___y_251_; uint8_t v___x_255_; 
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_sub(v___x_246_, v___x_248_);
v___x_255_ = lean_nat_dec_le(v___x_240_, v___x_249_);
if (v___x_255_ == 0)
{
lean_inc(v___x_249_);
v___y_251_ = v___x_249_;
goto v___jp_250_;
}
else
{
v___y_251_ = v___x_240_;
goto v___jp_250_;
}
v___jp_250_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_le(v___y_251_, v___x_249_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v___x_249_);
lean_inc(v___y_251_);
v___x_253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_246_, v___x_245_, v___y_251_, v___y_251_);
lean_dec(v___y_251_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_246_, v___x_245_, v___y_251_, v___x_249_);
lean_dec(v___x_249_);
return v___x_254_;
}
}
}
else
{
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed(lean_object* v_table_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(v_table_256_);
lean_dec(v_table_256_);
return v_res_257_;
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(lean_object* v___x_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
return v___x_260_;
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_258_ = stack[0].m_obj;
lean_object* v_res_261_;
v_res_261_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(v___x_258_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed(lean_object* v___x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(v___x_262_);
return v_res_264_;
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(lean_object* v___x_265_, lean_object* v_x_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_265_);
return v___x_269_;
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_265_ = stack[0].m_obj;
lean_object* v_x_266_ = stack[1].m_obj;
lean_object* v___y_267_ = stack[2].m_obj;
lean_object* v_res_270_;
v_res_270_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(v___x_265_, v_x_266_, v___y_267_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed(lean_object* v___x_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(v___x_271_, v_x_272_, v___y_273_);
lean_dec_ref(v___y_273_);
lean_dec_ref(v_x_272_);
return v_res_275_;
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11));
v___x_306_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_307_;
v_res_307_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___boxed(lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0(lean_object* v_init_310_, lean_object* v_t_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_310_, v_t_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(lean_object* v_init_313_, lean_object* v_t_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_313_, v_t_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1___boxed(lean_object* v_init_316_, lean_object* v_t_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(v_init_316_, v_t_317_);
lean_dec(v_t_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(lean_object* v_n_319_, lean_object* v_as_320_, lean_object* v_lo_321_, lean_object* v_hi_322_, lean_object* v_w_323_, lean_object* v_hlo_324_, lean_object* v_hhi_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_319_, v_as_320_, v_lo_321_, v_hi_322_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___boxed(lean_object* v_n_327_, lean_object* v_as_328_, lean_object* v_lo_329_, lean_object* v_hi_330_, lean_object* v_w_331_, lean_object* v_hlo_332_, lean_object* v_hhi_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(v_n_327_, v_as_328_, v_lo_329_, v_hi_330_, v_w_331_, v_hlo_332_, v_hhi_333_);
lean_dec(v_hi_330_);
lean_dec(v_n_327_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(lean_object* v_snd_335_, lean_object* v_k_336_, lean_object* v_t_337_, lean_object* v_hl_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_335_, v_k_336_, v_t_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___boxed(lean_object* v_snd_340_, lean_object* v_k_341_, lean_object* v_t_342_, lean_object* v_hl_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(v_snd_340_, v_k_341_, v_t_342_, v_hl_343_);
lean_dec_ref(v_snd_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(lean_object* v_n_345_, lean_object* v_lo_346_, lean_object* v_hi_347_, lean_object* v_hhi_348_, lean_object* v_pivot_349_, lean_object* v_as_350_, lean_object* v_i_351_, lean_object* v_k_352_, lean_object* v_ilo_353_, lean_object* v_ik_354_, lean_object* v_w_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_347_, v_pivot_349_, v_as_350_, v_i_351_, v_k_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___boxed(lean_object* v_n_357_, lean_object* v_lo_358_, lean_object* v_hi_359_, lean_object* v_hhi_360_, lean_object* v_pivot_361_, lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_k_364_, lean_object* v_ilo_365_, lean_object* v_ik_366_, lean_object* v_w_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(v_n_357_, v_lo_358_, v_hi_359_, v_hhi_360_, v_pivot_361_, v_as_362_, v_i_363_, v_k_364_, v_ilo_365_, v_ik_366_, v_w_367_);
lean_dec_ref(v_pivot_361_);
lean_dec(v_hi_359_);
lean_dec(v_lo_358_);
lean_dec(v_n_357_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(lean_object* v_fst_369_, lean_object* v_old_370_){
_start:
{
lean_object* v___y_372_; 
if (lean_obj_tag(v_old_370_) == 0)
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_NameSet_empty;
v___y_372_ = v___x_375_;
goto v___jp_371_;
}
else
{
lean_object* v_val_376_; 
v_val_376_ = lean_ctor_get(v_old_370_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_old_370_, 1);
v___y_372_ = v_val_376_;
goto v___jp_371_;
}
v___jp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_Lean_NameSet_insert(v___y_372_, v_fst_369_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(lean_object* v_fst_377_, lean_object* v_k_378_, lean_object* v_t_379_){
_start:
{
if (lean_obj_tag(v_t_379_) == 0)
{
lean_object* v_size_380_; lean_object* v_k_381_; lean_object* v_v_382_; lean_object* v_l_383_; lean_object* v_r_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_399_; 
v_size_380_ = lean_ctor_get(v_t_379_, 0);
v_k_381_ = lean_ctor_get(v_t_379_, 1);
v_v_382_ = lean_ctor_get(v_t_379_, 2);
v_l_383_ = lean_ctor_get(v_t_379_, 3);
v_r_384_ = lean_ctor_get(v_t_379_, 4);
v_isSharedCheck_399_ = !lean_is_exclusive(v_t_379_);
if (v_isSharedCheck_399_ == 0)
{
v___x_386_ = v_t_379_;
v_isShared_387_ = v_isSharedCheck_399_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_r_384_);
lean_inc(v_l_383_);
lean_inc(v_v_382_);
lean_inc(v_k_381_);
lean_inc(v_size_380_);
lean_dec(v_t_379_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_399_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint8_t v___x_388_; 
v___x_388_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_378_, v_k_381_);
switch(v___x_388_)
{
case 0:
{
lean_object* v_impl_389_; lean_object* v___x_390_; 
lean_del_object(v___x_386_);
lean_dec(v_size_380_);
v_impl_389_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_377_, v_k_378_, v_l_383_);
v___x_390_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_381_, v_v_382_, v_impl_389_, v_r_384_);
return v___x_390_;
}
case 1:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_val_393_; lean_object* v___x_395_; 
lean_dec(v_k_381_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_v_382_);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_377_, v___x_391_);
v_val_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_393_);
lean_dec(v___x_392_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v_val_393_);
lean_ctor_set(v___x_386_, 1, v_k_378_);
v___x_395_ = v___x_386_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_size_380_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_378_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_val_393_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_l_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_r_384_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
default: 
{
lean_object* v_impl_397_; lean_object* v___x_398_; 
lean_del_object(v___x_386_);
lean_dec(v_size_380_);
v_impl_397_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_377_, v_k_378_, v_r_384_);
v___x_398_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_381_, v_v_382_, v_l_383_, v_impl_397_);
return v___x_398_;
}
}
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_val_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_400_ = lean_box(0);
v___x_401_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_377_, v___x_400_);
v_val_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_val_402_);
lean_dec(v___x_401_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_k_378_);
lean_ctor_set(v___x_404_, 2, v_val_402_);
lean_ctor_set(v___x_404_, 3, v_t_379_);
lean_ctor_set(v___x_404_, 4, v_t_379_);
return v___x_404_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(lean_object* v_fst_405_, lean_object* v_as_406_, size_t v_i_407_, size_t v_stop_408_, lean_object* v_b_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = lean_usize_dec_eq(v_i_407_, v_stop_408_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; 
v___x_411_ = lean_array_uget_borrowed(v_as_406_, v_i_407_);
lean_inc(v___x_411_);
lean_inc(v_fst_405_);
v___x_412_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_405_, v___x_411_, v_b_409_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_407_, v___x_413_);
v_i_407_ = v___x_414_;
v_b_409_ = v___x_412_;
goto _start;
}
else
{
lean_dec(v_fst_405_);
return v_b_409_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_405_ = stack[0].m_obj;
lean_object* v_as_406_ = stack[1].m_obj;
size_t v_i_407_ = stack[2].m_num;
size_t v_stop_408_ = stack[3].m_num;
lean_object* v_b_409_ = stack[4].m_obj;
lean_object* v_res_416_;
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_405_, v_as_406_, v_i_407_, v_stop_408_, v_b_409_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1___boxed(lean_object* v_fst_417_, lean_object* v_as_418_, lean_object* v_i_419_, lean_object* v_stop_420_, lean_object* v_b_421_){
_start:
{
size_t v_i_boxed_422_; size_t v_stop_boxed_423_; lean_object* v_res_424_; 
v_i_boxed_422_ = lean_unbox_usize(v_i_419_);
lean_dec(v_i_419_);
v_stop_boxed_423_ = lean_unbox_usize(v_stop_420_);
lean_dec(v_stop_420_);
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_417_, v_as_418_, v_i_boxed_422_, v_stop_boxed_423_, v_b_421_);
lean_dec_ref(v_as_418_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0(lean_object* v_table_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_fst_427_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v_x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v_x_426_);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_array_get_size(v_snd_428_);
v___x_431_ = lean_nat_dec_lt(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_dec(v_snd_428_);
lean_dec(v_fst_427_);
return v_table_425_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_le(v___x_430_, v___x_430_);
if (v___x_432_ == 0)
{
if (v___x_431_ == 0)
{
lean_dec(v_snd_428_);
lean_dec(v_fst_427_);
return v_table_425_;
}
else
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((size_t)0ULL);
v___x_434_ = lean_usize_of_nat(v___x_430_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_427_, v_snd_428_, v___x_433_, v___x_434_, v_table_425_);
lean_dec(v_snd_428_);
return v___x_435_;
}
}
else
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lean_usize_of_nat(v___x_430_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_427_, v_snd_428_, v___x_436_, v___x_437_, v_table_425_);
lean_dec(v_snd_428_);
return v___x_438_;
}
}
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4));
v___x_460_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object* v_fst_464_, lean_object* v_k_465_, lean_object* v_t_466_, lean_object* v_hl_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_464_, v_k_465_, v_t_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v_addEntryFn_469_, lean_object* v___x_470_, lean_object* v_s_471_){
_start:
{
lean_object* v_importedEntries_472_; lean_object* v_state_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_importedEntries_472_ = lean_ctor_get(v_s_471_, 0);
v_state_473_ = lean_ctor_get(v_s_471_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_s_471_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v_s_471_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_state_473_);
lean_inc(v_importedEntries_472_);
lean_dec(v_s_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_state_477_; lean_object* v___x_479_; 
v_state_477_ = lean_apply_2(v_addEntryFn_469_, v_state_473_, v___x_470_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_state_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_importedEntries_472_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_state_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_482_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_486_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
lean_ctor_set(v___x_488_, 3, v___x_487_);
lean_ctor_set(v___x_488_, 4, v___x_486_);
lean_ctor_set(v___x_488_, 5, v___x_486_);
lean_ctor_set(v___x_488_, 6, v___x_486_);
lean_ctor_set(v___x_488_, 7, v___x_486_);
lean_ctor_set(v___x_488_, 8, v___x_486_);
lean_ctor_set(v___x_488_, 9, v___x_486_);
lean_ctor_set(v___x_488_, 10, v___x_486_);
lean_ctor_set(v___x_488_, 11, v___x_485_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(32u);
v___x_490_ = lean_mk_empty_array_with_capacity(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_492_ = ((size_t)5ULL);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_unsigned_to_nat(32u);
v___x_495_ = lean_mk_empty_array_with_capacity(v___x_494_);
v___x_496_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_497_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
lean_ctor_set(v___x_497_, 2, v___x_493_);
lean_ctor_set(v___x_497_, 3, v___x_493_);
lean_ctor_set_usize(v___x_497_, 4, v___x_492_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_box(1);
v___x_499_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_500_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
lean_ctor_set(v___x_501_, 2, v___x_498_);
return v___x_501_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; lean_object* v_toCold_507_; lean_object* v_env_508_; lean_object* v_options_509_; uint8_t v___x_510_; lean_object* v_env_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_506_ = lean_st_ref_get(v___y_504_);
v_toCold_507_ = lean_ctor_get(v___y_503_, 0);
v_env_508_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_506_);
v_options_509_ = lean_ctor_get(v_toCold_507_, 2);
v___x_510_ = 0;
v_env_511_ = l_Lean_Environment_setRecordingDeps(v_env_508_, v___x_510_);
v___x_512_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_513_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_509_);
v___x_514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_514_, 0, v_env_511_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
lean_ctor_set(v___x_514_, 3, v_options_509_);
v___x_515_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_msgData_502_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_502_ = stack[0].m_obj;
lean_object* v___y_503_ = stack[1].m_obj;
lean_object* v___y_504_ = stack[2].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_522_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_ref_527_; lean_object* v___x_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_ref_527_ = lean_ctor_get(v___y_524_, 2);
v___x_528_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msg_523_, v___y_524_, v___y_525_);
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
lean_inc(v_ref_527_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_ref_527_);
lean_ctor_set(v___x_533_, 1, v_a_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 1);
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_523_ = stack[0].m_obj;
lean_object* v___y_524_ = stack[1].m_obj;
lean_object* v___y_525_ = stack[2].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_523_, v___y_524_, v___y_525_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_543_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4));
v___x_552_ = l_Lean_stringToMessageData(v___x_551_);
return v___x_552_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object* v_name_556_, uint8_t v_kind_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___y_567_; 
v___x_561_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_562_ = l_Lean_MessageData_ofName(v_name_556_);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
switch(v_kind_557_)
{
case 0:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6));
v___y_567_ = v___x_574_;
goto v___jp_566_;
}
case 1:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7));
v___y_567_ = v___x_575_;
goto v___jp_566_;
}
default: 
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8));
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_inc_ref(v___y_567_);
v___x_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_568_, 0, v___y_567_);
v___x_569_ = l_Lean_MessageData_ofFormat(v___x_568_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_565_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_572_, v___y_558_, v___y_559_);
return v___x_573_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_556_ = stack[0].m_obj;
uint8_t v_kind_557_ = stack[1].m_num;
lean_object* v___y_558_ = stack[2].m_obj;
lean_object* v___y_559_ = stack[3].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_556_, v_kind_557_, v___y_558_, v___y_559_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_name_578_, lean_object* v_kind_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_kind_boxed_583_; lean_object* v_res_584_; 
v_kind_boxed_583_ = lean_unbox(v_kind_579_);
v_res_584_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_578_, v_kind_boxed_583_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_584_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t v_sz_585_, size_t v_i_586_, lean_object* v_bs_587_){
_start:
{
uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_lt(v_i_586_, v_sz_585_);
if (v___x_588_ == 0)
{
return v_bs_587_;
}
else
{
lean_object* v_v_589_; lean_object* v___x_590_; lean_object* v_bs_x27_591_; lean_object* v___x_592_; size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v_v_589_ = lean_array_uget(v_bs_587_, v_i_586_);
v___x_590_ = lean_unsigned_to_nat(0u);
v_bs_x27_591_ = lean_array_uset(v_bs_587_, v_i_586_, v___x_590_);
v___x_592_ = l_Lean_Syntax_getId(v_v_589_);
lean_dec(v_v_589_);
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_586_, v___x_593_);
v___x_595_ = lean_array_uset(v_bs_x27_591_, v_i_586_, v___x_592_);
v_i_586_ = v___x_594_;
v_bs_587_ = v___x_595_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_585_ = stack[0].m_num;
size_t v_i_586_ = stack[1].m_num;
lean_object* v_bs_587_ = stack[2].m_obj;
lean_object* v_res_597_;
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_585_, v_i_586_, v_bs_587_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_598_, lean_object* v_i_599_, lean_object* v_bs_600_){
_start:
{
size_t v_sz_boxed_601_; size_t v_i_boxed_602_; lean_object* v_res_603_; 
v_sz_boxed_601_ = lean_unbox_usize(v_sz_598_);
lean_dec(v_sz_598_);
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_boxed_601_, v_i_boxed_602_, v_bs_600_);
return v_res_603_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_610_ = l_Lean_stringToMessageData(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v_a_618_, lean_object* v___x_619_, lean_object* v_a_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v___x_624_, lean_object* v_decl_625_, lean_object* v_stx_626_, uint8_t v_kind_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v_nextMacroScope_635_; lean_object* v_ngen_636_; lean_object* v_auxDeclNGen_637_; lean_object* v_traceState_638_; lean_object* v_recordedDeps_639_; lean_object* v_messages_640_; lean_object* v_infoState_641_; lean_object* v_snapshotTasks_642_; lean_object* v___y_643_; lean_object* v_nextMacroScope_648_; lean_object* v_ngen_649_; lean_object* v_auxDeclNGen_650_; lean_object* v_traceState_651_; lean_object* v_recordedDeps_652_; lean_object* v_messages_653_; lean_object* v_infoState_654_; lean_object* v_snapshotTasks_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v_altSyntaxIds_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___x_791_; uint8_t v___x_792_; 
v___x_791_ = 0;
v___x_792_ = l_Lean_instBEqAttributeKind_beq(v_kind_627_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v_stx_626_);
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___x_793_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v___x_624_, v_kind_627_, v___y_628_, v___y_629_);
return v___x_793_;
}
else
{
lean_dec(v___x_624_);
goto v___jp_732_;
}
v___jp_631_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc_ref(v___y_634_);
v___x_644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_644_, 0, v___y_643_);
lean_ctor_set(v___x_644_, 1, v_nextMacroScope_635_);
lean_ctor_set(v___x_644_, 2, v_ngen_636_);
lean_ctor_set(v___x_644_, 3, v_auxDeclNGen_637_);
lean_ctor_set(v___x_644_, 4, v_traceState_638_);
lean_ctor_set(v___x_644_, 5, v___y_634_);
lean_ctor_set(v___x_644_, 6, v_recordedDeps_639_);
lean_ctor_set(v___x_644_, 7, v_messages_640_);
lean_ctor_set(v___x_644_, 8, v_infoState_641_);
lean_ctor_set(v___x_644_, 9, v_snapshotTasks_642_);
v___x_645_ = lean_st_ref_put(v___y_633_, v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___y_632_);
return v___x_646_;
}
v___jp_647_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_toEnvExtension_663_; lean_object* v_env_664_; lean_object* v_nextMacroScope_665_; lean_object* v_ngen_666_; lean_object* v_auxDeclNGen_667_; lean_object* v_traceState_668_; lean_object* v_recordedDeps_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v_addEntryFn_673_; lean_object* v_asyncMode_674_; uint8_t v_logWrites_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___f_678_; uint8_t v___x_679_; 
v___x_659_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_660_, 0, v___y_658_);
lean_ctor_set(v___x_660_, 1, v_nextMacroScope_648_);
lean_ctor_set(v___x_660_, 2, v_ngen_649_);
lean_ctor_set(v___x_660_, 3, v_auxDeclNGen_650_);
lean_ctor_set(v___x_660_, 4, v_traceState_651_);
lean_ctor_set(v___x_660_, 5, v___x_659_);
lean_ctor_set(v___x_660_, 6, v_recordedDeps_652_);
lean_ctor_set(v___x_660_, 7, v_messages_653_);
lean_ctor_set(v___x_660_, 8, v_infoState_654_);
lean_ctor_set(v___x_660_, 9, v_snapshotTasks_655_);
v___x_661_ = lean_st_ref_put(v___y_656_, v___x_660_);
v___x_662_ = lean_st_ref_take(v___y_656_);
v_toEnvExtension_663_ = lean_ctor_get(v_a_618_, 0);
lean_inc_ref(v_toEnvExtension_663_);
v_env_664_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_env_664_);
v_nextMacroScope_665_ = lean_ctor_get(v___x_662_, 1);
lean_inc(v_nextMacroScope_665_);
v_ngen_666_ = lean_ctor_get(v___x_662_, 2);
lean_inc_ref(v_ngen_666_);
v_auxDeclNGen_667_ = lean_ctor_get(v___x_662_, 3);
lean_inc_ref(v_auxDeclNGen_667_);
v_traceState_668_ = lean_ctor_get(v___x_662_, 4);
lean_inc_ref(v_traceState_668_);
v_recordedDeps_669_ = lean_ctor_get(v___x_662_, 6);
lean_inc_ref(v_recordedDeps_669_);
v_messages_670_ = lean_ctor_get(v___x_662_, 7);
lean_inc_ref(v_messages_670_);
v_infoState_671_ = lean_ctor_get(v___x_662_, 8);
lean_inc_ref(v_infoState_671_);
v_snapshotTasks_672_ = lean_ctor_get(v___x_662_, 9);
lean_inc_ref(v_snapshotTasks_672_);
lean_dec(v___x_662_);
v_addEntryFn_673_ = lean_ctor_get(v_a_618_, 3);
lean_inc(v_addEntryFn_673_);
lean_dec_ref(v_a_618_);
v_asyncMode_674_ = lean_ctor_get(v_toEnvExtension_663_, 2);
lean_inc(v_asyncMode_674_);
v_logWrites_675_ = lean_ctor_get_uint8(v_toEnvExtension_663_, sizeof(void*)*6);
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_decl_625_);
lean_ctor_set(v___x_677_, 1, v___y_657_);
v___f_678_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_678_, 0, v_addEntryFn_673_);
lean_closure_set(v___f_678_, 1, v___x_677_);
v___x_679_ = 1;
if (v_logWrites_675_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_663_, v_env_664_, v___f_678_, v_asyncMode_674_, v___x_619_, v___x_679_);
lean_dec(v_asyncMode_674_);
v___y_632_ = v___x_676_;
v___y_633_ = v___y_656_;
v___y_634_ = v___x_659_;
v_nextMacroScope_635_ = v_nextMacroScope_665_;
v_ngen_636_ = v_ngen_666_;
v_auxDeclNGen_637_ = v_auxDeclNGen_667_;
v_traceState_638_ = v_traceState_668_;
v_recordedDeps_639_ = v_recordedDeps_669_;
v_messages_640_ = v_messages_670_;
v_infoState_641_ = v_infoState_671_;
v_snapshotTasks_642_ = v_snapshotTasks_672_;
v___y_643_ = v___x_680_;
goto v___jp_631_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc_ref(v_toEnvExtension_663_);
v___x_681_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_663_, v_env_664_);
lean_dec_ref(v_env_664_);
v___x_682_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_663_, v___x_681_, v___f_678_, v_asyncMode_674_, v___x_619_, v___x_679_);
lean_dec(v_asyncMode_674_);
v___y_632_ = v___x_676_;
v___y_633_ = v___y_656_;
v___y_634_ = v___x_659_;
v_nextMacroScope_635_ = v_nextMacroScope_665_;
v_ngen_636_ = v_ngen_666_;
v_auxDeclNGen_637_ = v_auxDeclNGen_667_;
v_traceState_638_ = v_traceState_668_;
v_recordedDeps_639_ = v_recordedDeps_669_;
v_messages_640_ = v_messages_670_;
v_infoState_641_ = v_infoState_671_;
v_snapshotTasks_642_ = v_snapshotTasks_672_;
v___y_643_ = v___x_682_;
goto v___jp_631_;
}
}
v___jp_683_:
{
size_t v_sz_686_; size_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_toEnvExtension_690_; lean_object* v_env_691_; lean_object* v_nextMacroScope_692_; lean_object* v_ngen_693_; lean_object* v_auxDeclNGen_694_; lean_object* v_traceState_695_; lean_object* v_recordedDeps_696_; lean_object* v_messages_697_; lean_object* v_infoState_698_; lean_object* v_snapshotTasks_699_; lean_object* v_addEntryFn_700_; lean_object* v_asyncMode_701_; uint8_t v_logWrites_702_; lean_object* v___x_703_; lean_object* v___f_704_; uint8_t v___x_705_; 
v_sz_686_ = lean_array_size(v___y_684_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_686_, v___x_687_, v___y_684_);
v___x_689_ = lean_st_ref_take(v___y_685_);
v_toEnvExtension_690_ = lean_ctor_get(v_a_620_, 0);
lean_inc_ref(v_toEnvExtension_690_);
v_env_691_ = lean_ctor_get(v___x_689_, 0);
lean_inc_ref(v_env_691_);
v_nextMacroScope_692_ = lean_ctor_get(v___x_689_, 1);
lean_inc(v_nextMacroScope_692_);
v_ngen_693_ = lean_ctor_get(v___x_689_, 2);
lean_inc_ref(v_ngen_693_);
v_auxDeclNGen_694_ = lean_ctor_get(v___x_689_, 3);
lean_inc_ref(v_auxDeclNGen_694_);
v_traceState_695_ = lean_ctor_get(v___x_689_, 4);
lean_inc_ref(v_traceState_695_);
v_recordedDeps_696_ = lean_ctor_get(v___x_689_, 6);
lean_inc_ref(v_recordedDeps_696_);
v_messages_697_ = lean_ctor_get(v___x_689_, 7);
lean_inc_ref(v_messages_697_);
v_infoState_698_ = lean_ctor_get(v___x_689_, 8);
lean_inc_ref(v_infoState_698_);
v_snapshotTasks_699_ = lean_ctor_get(v___x_689_, 9);
lean_inc_ref(v_snapshotTasks_699_);
lean_dec(v___x_689_);
v_addEntryFn_700_ = lean_ctor_get(v_a_620_, 3);
lean_inc(v_addEntryFn_700_);
lean_dec_ref(v_a_620_);
v_asyncMode_701_ = lean_ctor_get(v_toEnvExtension_690_, 2);
lean_inc(v_asyncMode_701_);
v_logWrites_702_ = lean_ctor_get_uint8(v_toEnvExtension_690_, sizeof(void*)*6);
lean_inc_ref(v___x_688_);
lean_inc(v_decl_625_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_decl_625_);
lean_ctor_set(v___x_703_, 1, v___x_688_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_704_, 0, v_addEntryFn_700_);
lean_closure_set(v___f_704_, 1, v___x_703_);
v___x_705_ = 1;
if (v_logWrites_702_ == 0)
{
lean_object* v___x_706_; 
lean_inc(v___x_619_);
v___x_706_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_690_, v_env_691_, v___f_704_, v_asyncMode_701_, v___x_619_, v___x_705_);
lean_dec(v_asyncMode_701_);
v_nextMacroScope_648_ = v_nextMacroScope_692_;
v_ngen_649_ = v_ngen_693_;
v_auxDeclNGen_650_ = v_auxDeclNGen_694_;
v_traceState_651_ = v_traceState_695_;
v_recordedDeps_652_ = v_recordedDeps_696_;
v_messages_653_ = v_messages_697_;
v_infoState_654_ = v_infoState_698_;
v_snapshotTasks_655_ = v_snapshotTasks_699_;
v___y_656_ = v___y_685_;
v___y_657_ = v___x_688_;
v___y_658_ = v___x_706_;
goto v___jp_647_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_inc_ref(v_toEnvExtension_690_);
v___x_707_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_690_, v_env_691_);
lean_dec_ref(v_env_691_);
lean_inc(v___x_619_);
v___x_708_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_690_, v___x_707_, v___f_704_, v_asyncMode_701_, v___x_619_, v___x_705_);
lean_dec(v_asyncMode_701_);
v_nextMacroScope_648_ = v_nextMacroScope_692_;
v_ngen_649_ = v_ngen_693_;
v_auxDeclNGen_650_ = v_auxDeclNGen_694_;
v_traceState_651_ = v_traceState_695_;
v_recordedDeps_652_ = v_recordedDeps_696_;
v_messages_653_ = v_messages_697_;
v_infoState_654_ = v_infoState_698_;
v_snapshotTasks_655_ = v_snapshotTasks_699_;
v___y_656_ = v___y_685_;
v___y_657_ = v___x_688_;
v___y_658_ = v___x_708_;
goto v___jp_647_;
}
}
v___jp_709_:
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_isPrivateName(v_decl_625_);
if (v___x_713_ == 0)
{
v___y_684_ = v_altSyntaxIds_710_;
v___y_685_ = v___y_712_;
goto v___jp_683_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec_ref(v_altSyntaxIds_710_);
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___x_714_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_715_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_714_, v___y_711_, v___y_712_);
return v___x_715_;
}
}
v___jp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v___x_719_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_720_ = l_Lean_Syntax_instRepr_repr(v_stx_626_, v___x_621_);
v___x_721_ = l_Lean_MessageData_ofFormat(v___x_720_);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_719_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_722_, v___y_717_, v___y_718_);
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
v___jp_732_:
{
if (lean_obj_tag(v_stx_626_) == 1)
{
lean_object* v_kind_733_; 
v_kind_733_ = lean_ctor_get(v_stx_626_, 1);
if (lean_obj_tag(v_kind_733_) == 1)
{
lean_object* v_pre_734_; 
v_pre_734_ = lean_ctor_get(v_kind_733_, 0);
if (lean_obj_tag(v_pre_734_) == 1)
{
lean_object* v_pre_735_; 
v_pre_735_ = lean_ctor_get(v_pre_734_, 0);
switch(lean_obj_tag(v_pre_735_))
{
case 0:
{
lean_object* v_args_736_; lean_object* v_str_737_; lean_object* v_str_738_; uint8_t v___x_739_; 
v_args_736_ = lean_ctor_get(v_stx_626_, 2);
v_str_737_ = lean_ctor_get(v_kind_733_, 1);
v_str_738_ = lean_ctor_get(v_pre_734_, 1);
v___x_739_ = lean_string_dec_eq(v_str_738_, v___x_622_);
if (v___x_739_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
uint8_t v___x_740_; 
v___x_740_ = lean_string_dec_eq(v_str_737_, v___x_623_);
if (v___x_740_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_array_get_size(v_args_736_);
v___x_742_ = lean_unsigned_to_nat(2u);
v___x_743_ = lean_nat_dec_eq(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_744_; 
v___x_744_ = lean_array_fget_borrowed(v_args_736_, v___x_621_);
if (lean_obj_tag(v___x_744_) == 2)
{
lean_object* v_val_745_; uint8_t v___x_746_; 
v_val_745_ = lean_ctor_get(v___x_744_, 1);
v___x_746_ = lean_string_dec_eq(v_val_745_, v___x_623_);
if (v___x_746_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_array_fget_borrowed(v_args_736_, v___x_747_);
if (lean_obj_tag(v___x_748_) == 1)
{
lean_object* v_kind_749_; 
v_kind_749_ = lean_ctor_get(v___x_748_, 1);
if (lean_obj_tag(v_kind_749_) == 1)
{
lean_object* v_pre_750_; 
v_pre_750_ = lean_ctor_get(v_kind_749_, 0);
if (lean_obj_tag(v_pre_750_) == 0)
{
lean_object* v_args_751_; lean_object* v_str_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_args_751_ = lean_ctor_get(v___x_748_, 2);
v_str_752_ = lean_ctor_get(v_kind_749_, 1);
v___x_753_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_754_ = lean_string_dec_eq(v_str_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_inc_ref(v_args_751_);
lean_dec_ref_known(v_stx_626_, 3);
v_altSyntaxIds_710_ = v_args_751_;
v___y_711_ = v___y_628_;
v___y_712_ = v___y_629_;
goto v___jp_709_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
}
}
}
case 1:
{
lean_object* v_pre_755_; 
v_pre_755_ = lean_ctor_get(v_pre_735_, 0);
if (lean_obj_tag(v_pre_755_) == 1)
{
lean_object* v_pre_756_; 
v_pre_756_ = lean_ctor_get(v_pre_755_, 0);
if (lean_obj_tag(v_pre_756_) == 0)
{
lean_object* v_args_757_; lean_object* v_str_758_; lean_object* v_str_759_; lean_object* v_str_760_; lean_object* v_str_761_; uint8_t v___x_762_; 
v_args_757_ = lean_ctor_get(v_stx_626_, 2);
v_str_758_ = lean_ctor_get(v_kind_733_, 1);
v_str_759_ = lean_ctor_get(v_pre_734_, 1);
v_str_760_ = lean_ctor_get(v_pre_735_, 1);
v_str_761_ = lean_ctor_get(v_pre_755_, 1);
v___x_762_ = lean_string_dec_eq(v_str_761_, v___x_622_);
if (v___x_762_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_764_ = lean_string_dec_eq(v_str_760_, v___x_763_);
if (v___x_764_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_766_ = lean_string_dec_eq(v_str_759_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_768_ = lean_string_dec_eq(v_str_758_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_array_get_size(v_args_757_);
v___x_770_ = lean_unsigned_to_nat(2u);
v___x_771_ = lean_nat_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_772_; 
v___x_772_ = lean_array_fget_borrowed(v_args_757_, v___x_621_);
if (lean_obj_tag(v___x_772_) == 3)
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_772_, 2);
if (lean_obj_tag(v_val_773_) == 1)
{
lean_object* v_pre_774_; 
v_pre_774_ = lean_ctor_get(v_val_773_, 0);
if (lean_obj_tag(v_pre_774_) == 0)
{
lean_object* v_preresolved_775_; lean_object* v_str_776_; uint8_t v___x_777_; 
v_preresolved_775_ = lean_ctor_get(v___x_772_, 3);
v_str_776_ = lean_ctor_get(v_val_773_, 1);
v___x_777_ = lean_string_dec_eq(v_str_776_, v___x_623_);
if (v___x_777_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
if (lean_obj_tag(v_preresolved_775_) == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_array_fget_borrowed(v_args_757_, v___x_778_);
if (lean_obj_tag(v___x_779_) == 1)
{
lean_object* v_kind_780_; 
v_kind_780_ = lean_ctor_get(v___x_779_, 1);
if (lean_obj_tag(v_kind_780_) == 1)
{
lean_object* v_pre_781_; 
v_pre_781_ = lean_ctor_get(v_kind_780_, 0);
if (lean_obj_tag(v_pre_781_) == 0)
{
lean_object* v_args_782_; lean_object* v_str_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_args_782_ = lean_ctor_get(v___x_779_, 2);
v_str_783_ = lean_ctor_get(v_kind_780_, 1);
v___x_784_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_785_ = lean_string_dec_eq(v_str_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_array_get_size(v_args_782_);
v___x_787_ = lean_nat_dec_eq(v___x_786_, v___x_778_);
if (v___x_787_ == 0)
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref(v_args_782_);
lean_dec_ref_known(v_stx_626_, 3);
v___x_788_ = lean_array_fget(v_args_782_, v___x_621_);
lean_dec_ref(v_args_782_);
v___x_789_ = lean_mk_empty_array_with_capacity(v___x_778_);
v___x_790_ = lean_array_push(v___x_789_, v___x_788_);
v_altSyntaxIds_710_ = v___x_790_;
v___y_711_ = v___y_628_;
v___y_712_ = v___y_629_;
goto v___jp_709_;
}
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
default: 
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_decl_625_);
lean_dec_ref(v_a_620_);
lean_dec(v___x_619_);
lean_dec_ref(v_a_618_);
v___y_717_ = v___y_628_;
v___y_718_ = v___y_629_;
goto v___jp_716_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_a_618_ = stack[0].m_obj;
lean_object* v___x_619_ = stack[1].m_obj;
lean_object* v_a_620_ = stack[2].m_obj;
lean_object* v___x_621_ = stack[3].m_obj;
lean_object* v___x_622_ = stack[4].m_obj;
lean_object* v___x_623_ = stack[5].m_obj;
lean_object* v___x_624_ = stack[6].m_obj;
lean_object* v_decl_625_ = stack[7].m_obj;
lean_object* v_stx_626_ = stack[8].m_obj;
uint8_t v_kind_627_ = stack[9].m_num;
lean_object* v___y_628_ = stack[10].m_obj;
lean_object* v___y_629_ = stack[11].m_obj;
lean_object* v_res_794_;
v_res_794_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v_a_618_, v___x_619_, v_a_620_, v___x_621_, v___x_622_, v___x_623_, v___x_624_, v_decl_625_, v_stx_626_, v_kind_627_, v___y_628_, v___y_629_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_795_, lean_object* v___x_796_, lean_object* v_a_797_, lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v_decl_802_, lean_object* v_stx_803_, lean_object* v_kind_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v_kind_boxed_808_; lean_object* v_res_809_; 
v_kind_boxed_808_ = lean_unbox(v_kind_804_);
v_res_809_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v_a_795_, v___x_796_, v_a_797_, v___x_798_, v___x_799_, v___x_800_, v___x_801_, v_decl_802_, v_stx_803_, v_kind_boxed_808_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v___x_800_);
lean_dec_ref(v___x_799_);
lean_dec(v___x_798_);
return v_res_809_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v___x_816_, lean_object* v_decl_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_821_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_822_ = l_Lean_MessageData_ofName(v___x_816_);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_825_, v___y_818_, v___y_819_);
return v___x_826_;
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_816_ = stack[0].m_obj;
lean_object* v_decl_817_ = stack[1].m_obj;
lean_object* v___y_818_ = stack[2].m_obj;
lean_object* v___y_819_ = stack[3].m_obj;
lean_object* v_res_827_;
v_res_827_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v___x_816_, v_decl_817_, v___y_818_, v___y_819_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v___x_828_, lean_object* v_decl_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v___x_828_, v_decl_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v_decl_829_);
return v_res_833_;
}
}
lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_n(v_a_870_, 2);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = lean_box(0);
v___x_872_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4));
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_875_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
lean_inc(v_a_868_);
v___f_876_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed), 13, 7);
lean_closure_set(v___f_876_, 0, v_a_870_);
lean_closure_set(v___f_876_, 1, v___x_871_);
lean_closure_set(v___f_876_, 2, v_a_868_);
lean_closure_set(v___f_876_, 3, v___x_873_);
lean_closure_set(v___f_876_, 4, v___x_872_);
lean_closure_set(v___f_876_, 5, v___x_874_);
lean_closure_set(v___f_876_, 6, v___x_875_);
v___f_877_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_878_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___f_876_);
lean_ctor_set(v___x_879_, 2, v___f_877_);
v___x_880_ = l_Lean_registerBuiltinAttribute(v___x_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_889_);
v___x_882_ = v___x_880_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_dec(v___x_880_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_a_868_);
lean_ctor_set(v___x_884_, 1, v_a_870_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_a_870_);
lean_dec(v_a_868_);
v_a_890_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_880_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_880_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_a_868_);
v_a_898_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_869_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_869_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_906_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_867_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_867_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_914_;
v_res_914_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
return v_res_916_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_917_, lean_object* v_msg_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_918_, v___y_919_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_918_ = stack[1].m_obj;
lean_object* v___y_919_ = stack[2].m_obj;
lean_object* v___y_920_ = stack[3].m_obj;
lean_object* v_res_923_;
v_res_923_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_918_, v___y_919_, v___y_920_);
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_924_, lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(v_00_u03b1_924_, v_msg_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_929_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b1_930_, lean_object* v_name_931_, uint8_t v_kind_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_931_, v_kind_932_, v___y_933_, v___y_934_);
return v___x_936_;
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_931_ = stack[1].m_obj;
uint8_t v_kind_932_ = stack[2].m_num;
lean_object* v___y_933_ = stack[3].m_obj;
lean_object* v___y_934_ = stack[4].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_box(0), v_name_931_, v_kind_932_, v___y_933_, v___y_934_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b1_938_, lean_object* v_name_939_, lean_object* v_kind_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v_kind_boxed_944_; lean_object* v_res_945_; 
v_kind_boxed_944_ = lean_unbox(v_kind_940_);
v_res_945_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(v_00_u03b1_938_, v_name_939_, v_kind_boxed_944_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1(lean_object* v_incorrectName_968_, lean_object* v___f_969_, lean_object* v___f_970_, lean_object* v_x1_971_, lean_object* v_x2_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_array_get_size(v_x2_972_);
v___x_975_ = lean_nat_dec_lt(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_dec_ref(v___f_970_);
lean_dec_ref(v___f_969_);
lean_dec(v_incorrectName_968_);
return v_x1_971_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_sub(v___x_974_, v___x_976_);
v___x_978_ = lean_nat_dec_le(v___x_973_, v___x_977_);
if (v___x_978_ == 0)
{
lean_dec(v___x_977_);
lean_dec_ref(v___f_970_);
lean_dec_ref(v___f_969_);
lean_dec(v_incorrectName_968_);
return v_x1_971_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_979_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_incorrectName_968_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_982_ = l_Array_binSearchAux___redArg(v___f_969_, v___x_981_, v_x2_972_, v___x_980_, v___x_973_, v___x_977_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref(v___f_970_);
return v_x1_971_;
}
else
{
lean_object* v_val_983_; lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v_snd_984_ = lean_ctor_get(v_val_983_, 1);
lean_inc(v_snd_984_);
lean_dec(v_val_983_);
v___x_985_ = lean_array_get_size(v_snd_984_);
v___x_986_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_987_ = lean_nat_dec_lt(v___x_973_, v___x_985_);
if (v___x_987_ == 0)
{
lean_dec(v_snd_984_);
lean_dec_ref(v___f_970_);
return v_x1_971_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = lean_nat_dec_le(v___x_985_, v___x_985_);
if (v___x_988_ == 0)
{
if (v___x_987_ == 0)
{
lean_dec(v_snd_984_);
lean_dec_ref(v___f_970_);
return v_x1_971_;
}
else
{
size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_985_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_986_, v___f_970_, v_snd_984_, v___x_989_, v___x_990_, v_x1_971_);
return v___x_991_;
}
}
else
{
size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_992_ = ((size_t)0ULL);
v___x_993_ = lean_usize_of_nat(v___x_985_);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_986_, v___f_970_, v_snd_984_, v___x_992_, v___x_993_, v_x1_971_);
return v___x_994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1___boxed(lean_object* v_incorrectName_995_, lean_object* v___f_996_, lean_object* v___f_997_, lean_object* v_x1_998_, lean_object* v_x2_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_getSuggestions___redArg___lam__1(v_incorrectName_995_, v___f_996_, v___f_997_, v_x1_998_, v_x2_999_);
lean_dec_ref(v_x2_999_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0(lean_object* v___x_1001_, lean_object* v_toPure_1002_, lean_object* v___f_1003_, lean_object* v_incorrectName_1004_, lean_object* v_env_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v_snd_1007_; lean_object* v_toEnvExtension_1008_; lean_object* v_asyncMode_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v_importedEntries_1013_; lean_object* v_state_1014_; lean_object* v___y_1016_; lean_object* v___x_1032_; 
v___x_1006_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_1007_ = lean_ctor_get(v___x_1006_, 1);
v_toEnvExtension_1008_ = lean_ctor_get(v_snd_1007_, 0);
v_asyncMode_1009_ = lean_ctor_get(v_toEnvExtension_1008_, 2);
v___x_1010_ = lean_box(0);
v___x_1011_ = 0;
v___x_1012_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1001_, v_toEnvExtension_1008_, v_env_1005_, v_asyncMode_1009_, v___x_1010_, v___x_1011_);
v_importedEntries_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_ref(v_importedEntries_1013_);
v_state_1014_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_state_1014_);
lean_dec(v___x_1012_);
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1014_, v_incorrectName_1004_);
lean_dec(v_state_1014_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_NameSet_empty;
v___y_1016_ = v___x_1033_;
goto v___jp_1015_;
}
else
{
lean_object* v_val_1034_; 
v_val_1034_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_val_1034_);
lean_dec_ref_known(v___x_1032_, 1);
v___y_1016_ = v_val_1034_;
goto v___jp_1015_;
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_array_get_size(v_importedEntries_1013_);
v___x_1019_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1020_ = lean_nat_dec_lt(v___x_1017_, v___x_1018_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_importedEntries_1013_);
lean_dec_ref(v___f_1003_);
v___x_1021_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___y_1016_);
return v___x_1021_;
}
else
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_nat_dec_le(v___x_1018_, v___x_1018_);
if (v___x_1022_ == 0)
{
if (v___x_1020_ == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref(v_importedEntries_1013_);
lean_dec_ref(v___f_1003_);
v___x_1023_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___y_1016_);
return v___x_1023_;
}
else
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = lean_usize_of_nat(v___x_1018_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1019_, v___f_1003_, v_importedEntries_1013_, v___x_1024_, v___x_1025_, v___y_1016_);
v___x_1027_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___x_1026_);
return v___x_1027_;
}
}
else
{
size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = lean_usize_of_nat(v___x_1018_);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1019_, v___f_1003_, v_importedEntries_1013_, v___x_1028_, v___x_1029_, v___y_1016_);
v___x_1031_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___x_1030_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0___boxed(lean_object* v___x_1035_, lean_object* v_toPure_1036_, lean_object* v___f_1037_, lean_object* v_incorrectName_1038_, lean_object* v_env_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_getSuggestions___redArg___lam__0(v___x_1035_, v_toPure_1036_, v___f_1037_, v_incorrectName_1038_, v_env_1039_);
lean_dec(v_incorrectName_1038_);
lean_dec_ref(v___x_1035_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_getSuggestions___redArg___closed__2(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_box(1);
v___x_1044_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg(lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_incorrectName_1047_){
_start:
{
lean_object* v_toApplicative_1048_; lean_object* v_toBind_1049_; lean_object* v_getEnv_1050_; lean_object* v_toPure_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; 
v_toApplicative_1048_ = lean_ctor_get(v_inst_1045_, 0);
lean_inc_ref(v_toApplicative_1048_);
v_toBind_1049_ = lean_ctor_get(v_inst_1045_, 1);
lean_inc(v_toBind_1049_);
lean_dec_ref(v_inst_1045_);
v_getEnv_1050_ = lean_ctor_get(v_inst_1046_, 0);
lean_inc(v_getEnv_1050_);
lean_dec_ref(v_inst_1046_);
v_toPure_1051_ = lean_ctor_get(v_toApplicative_1048_, 1);
lean_inc(v_toPure_1051_);
lean_dec_ref(v_toApplicative_1048_);
v___f_1052_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
v___f_1053_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__1));
lean_inc(v_incorrectName_1047_);
v___f_1054_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1054_, 0, v_incorrectName_1047_);
lean_closure_set(v___f_1054_, 1, v___f_1052_);
lean_closure_set(v___f_1054_, 2, v___f_1053_);
v___x_1055_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___f_1056_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1056_, 0, v___x_1055_);
lean_closure_set(v___f_1056_, 1, v_toPure_1051_);
lean_closure_set(v___f_1056_, 2, v___f_1054_);
lean_closure_set(v___f_1056_, 3, v_incorrectName_1047_);
v___x_1057_ = lean_apply_4(v_toBind_1049_, lean_box(0), lean_box(0), v_getEnv_1050_, v___f_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions(lean_object* v_m_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_incorrectName_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_getSuggestions___redArg(v_inst_1059_, v_inst_1060_, v_incorrectName_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1(lean_object* v_trueName_1063_, lean_object* v___f_1064_, lean_object* v___f_1065_, lean_object* v_x1_1066_, lean_object* v_x2_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_array_get_size(v_x2_1067_);
v___x_1070_ = lean_nat_dec_lt(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v___f_1065_);
lean_dec_ref(v___f_1064_);
lean_dec(v_trueName_1063_);
return v_x1_1066_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_sub(v___x_1069_, v___x_1071_);
v___x_1073_ = lean_nat_dec_le(v___x_1068_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v___x_1072_);
lean_dec_ref(v___f_1065_);
lean_dec_ref(v___f_1064_);
lean_dec(v_trueName_1063_);
return v_x1_1066_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_trueName_1063_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_1077_ = l_Array_binSearchAux___redArg(v___f_1064_, v___x_1076_, v_x2_1067_, v___x_1075_, v___x_1068_, v___x_1072_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_dec_ref(v___f_1065_);
return v_x1_1066_;
}
else
{
lean_object* v_val_1078_; lean_object* v_snd_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_val_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v_snd_1079_ = lean_ctor_get(v_val_1078_, 1);
lean_inc(v_snd_1079_);
lean_dec(v_val_1078_);
v___x_1080_ = lean_array_get_size(v_snd_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1082_ = lean_nat_dec_lt(v___x_1068_, v___x_1080_);
if (v___x_1082_ == 0)
{
lean_dec(v_snd_1079_);
lean_dec_ref(v___f_1065_);
return v_x1_1066_;
}
else
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_le(v___x_1080_, v___x_1080_);
if (v___x_1083_ == 0)
{
if (v___x_1082_ == 0)
{
lean_dec(v_snd_1079_);
lean_dec_ref(v___f_1065_);
return v_x1_1066_;
}
else
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1080_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1081_, v___f_1065_, v_snd_1079_, v___x_1084_, v___x_1085_, v_x1_1066_);
return v___x_1086_;
}
}
else
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1080_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1081_, v___f_1065_, v_snd_1079_, v___x_1087_, v___x_1088_, v_x1_1066_);
return v___x_1089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1___boxed(lean_object* v_trueName_1090_, lean_object* v___f_1091_, lean_object* v___f_1092_, lean_object* v_x1_1093_, lean_object* v_x2_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_getStoredSuggestions___redArg___lam__1(v_trueName_1090_, v___f_1091_, v___f_1092_, v_x1_1093_, v_x2_1094_);
lean_dec_ref(v_x2_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0(lean_object* v___x_1096_, lean_object* v_toPure_1097_, lean_object* v___f_1098_, lean_object* v_trueName_1099_, lean_object* v_env_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v_fst_1102_; lean_object* v_toEnvExtension_1103_; lean_object* v_asyncMode_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v_importedEntries_1108_; lean_object* v_state_1109_; lean_object* v___y_1111_; lean_object* v___x_1127_; 
v___x_1101_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_fst_1102_ = lean_ctor_get(v___x_1101_, 0);
v_toEnvExtension_1103_ = lean_ctor_get(v_fst_1102_, 0);
v_asyncMode_1104_ = lean_ctor_get(v_toEnvExtension_1103_, 2);
v___x_1105_ = lean_box(0);
v___x_1106_ = 0;
v___x_1107_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1096_, v_toEnvExtension_1103_, v_env_1100_, v_asyncMode_1104_, v___x_1105_, v___x_1106_);
v_importedEntries_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_importedEntries_1108_);
v_state_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_state_1109_);
lean_dec(v___x_1107_);
v___x_1127_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1109_, v_trueName_1099_);
lean_dec(v_state_1109_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_NameSet_empty;
v___y_1111_ = v___x_1128_;
goto v___jp_1110_;
}
else
{
lean_object* v_val_1129_; 
v_val_1129_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1129_);
lean_dec_ref_known(v___x_1127_, 1);
v___y_1111_ = v_val_1129_;
goto v___jp_1110_;
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_array_get_size(v_importedEntries_1108_);
v___x_1114_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1115_ = lean_nat_dec_lt(v___x_1112_, v___x_1113_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v_importedEntries_1108_);
lean_dec_ref(v___f_1098_);
v___x_1116_ = lean_apply_2(v_toPure_1097_, lean_box(0), v___y_1111_);
return v___x_1116_;
}
else
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_nat_dec_le(v___x_1113_, v___x_1113_);
if (v___x_1117_ == 0)
{
if (v___x_1115_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v_importedEntries_1108_);
lean_dec_ref(v___f_1098_);
v___x_1118_ = lean_apply_2(v_toPure_1097_, lean_box(0), v___y_1111_);
return v___x_1118_;
}
else
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = lean_usize_of_nat(v___x_1113_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1114_, v___f_1098_, v_importedEntries_1108_, v___x_1119_, v___x_1120_, v___y_1111_);
v___x_1122_ = lean_apply_2(v_toPure_1097_, lean_box(0), v___x_1121_);
return v___x_1122_;
}
}
else
{
size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = ((size_t)0ULL);
v___x_1124_ = lean_usize_of_nat(v___x_1113_);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1114_, v___f_1098_, v_importedEntries_1108_, v___x_1123_, v___x_1124_, v___y_1111_);
v___x_1126_ = lean_apply_2(v_toPure_1097_, lean_box(0), v___x_1125_);
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0___boxed(lean_object* v___x_1130_, lean_object* v_toPure_1131_, lean_object* v___f_1132_, lean_object* v_trueName_1133_, lean_object* v_env_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_getStoredSuggestions___redArg___lam__0(v___x_1130_, v_toPure_1131_, v___f_1132_, v_trueName_1133_, v_env_1134_);
lean_dec(v_trueName_1133_);
lean_dec_ref(v___x_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_trueName_1138_){
_start:
{
lean_object* v_toApplicative_1139_; lean_object* v_toBind_1140_; lean_object* v_getEnv_1141_; lean_object* v_toPure_1142_; lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; 
v_toApplicative_1139_ = lean_ctor_get(v_inst_1136_, 0);
lean_inc_ref(v_toApplicative_1139_);
v_toBind_1140_ = lean_ctor_get(v_inst_1136_, 1);
lean_inc(v_toBind_1140_);
lean_dec_ref(v_inst_1136_);
v_getEnv_1141_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc(v_getEnv_1141_);
lean_dec_ref(v_inst_1137_);
v_toPure_1142_ = lean_ctor_get(v_toApplicative_1139_, 1);
lean_inc(v_toPure_1142_);
lean_dec_ref(v_toApplicative_1139_);
v___f_1143_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
v___f_1144_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__1));
lean_inc(v_trueName_1138_);
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1145_, 0, v_trueName_1138_);
lean_closure_set(v___f_1145_, 1, v___f_1143_);
lean_closure_set(v___f_1145_, 2, v___f_1144_);
v___x_1146_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1147_, 0, v___x_1146_);
lean_closure_set(v___f_1147_, 1, v_toPure_1142_);
lean_closure_set(v___f_1147_, 2, v___f_1145_);
lean_closure_set(v___f_1147_, 3, v_trueName_1138_);
v___x_1148_ = lean_apply_4(v_toBind_1140_, lean_box(0), lean_box(0), v_getEnv_1141_, v___f_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions(lean_object* v_m_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_trueName_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_getStoredSuggestions___redArg(v_inst_1150_, v_inst_1151_, v_trueName_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object* v_as_1154_, lean_object* v_k_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_m_1160_; lean_object* v_a_1161_; uint8_t v___x_1162_; 
v___x_1158_ = lean_nat_add(v_x_1156_, v_x_1157_);
v___x_1159_ = lean_unsigned_to_nat(1u);
v_m_1160_ = lean_nat_shiftr(v___x_1158_, v___x_1159_);
lean_dec(v___x_1158_);
v_a_1161_ = lean_array_fget_borrowed(v_as_1154_, v_m_1160_);
v___x_1162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_1161_, v_k_1155_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; 
lean_dec(v_x_1157_);
v___x_1163_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_k_1155_, v_a_1161_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec(v_m_1160_);
lean_dec(v_x_1156_);
lean_inc(v_a_1161_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1161_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_nat_dec_eq(v_m_1160_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_nat_sub(v_m_1160_, v___x_1159_);
lean_dec(v_m_1160_);
v___x_1168_ = lean_nat_dec_lt(v___x_1167_, v_x_1156_);
if (v___x_1168_ == 0)
{
v_x_1157_ = v___x_1167_;
goto _start;
}
else
{
lean_object* v___x_1170_; 
lean_dec(v___x_1167_);
lean_dec(v_x_1156_);
v___x_1170_ = lean_box(0);
return v___x_1170_;
}
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_m_1160_);
lean_dec(v_x_1156_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
}
}
else
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
lean_dec(v_x_1156_);
v___x_1172_ = lean_nat_add(v_m_1160_, v___x_1159_);
lean_dec(v_m_1160_);
v___x_1173_ = lean_nat_dec_le(v___x_1172_, v_x_1157_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec(v___x_1172_);
lean_dec(v_x_1157_);
v___x_1174_ = lean_box(0);
return v___x_1174_;
}
else
{
v_x_1156_ = v___x_1172_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object* v_as_1176_, lean_object* v_k_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1176_, v_k_1177_, v_x_1178_, v_x_1179_);
lean_dec_ref(v_k_1177_);
lean_dec_ref(v_as_1176_);
return v_res_1180_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object* v_incorrectName_1181_, lean_object* v_as_1182_, size_t v_i_1183_, size_t v_stop_1184_, lean_object* v_b_1185_){
_start:
{
lean_object* v___y_1187_; uint8_t v___x_1191_; 
v___x_1191_ = lean_usize_dec_eq(v_i_1183_, v_stop_1184_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1192_ = lean_array_uget_borrowed(v_as_1182_, v_i_1183_);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_array_get_size(v___x_1192_);
v___x_1195_ = lean_nat_dec_lt(v___x_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
v___y_1187_ = v_b_1185_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_sub(v___x_1194_, v___x_1196_);
v___x_1198_ = lean_nat_dec_le(v___x_1193_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec(v___x_1197_);
v___y_1187_ = v_b_1185_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
lean_inc(v_incorrectName_1181_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_incorrectName_1181_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v___x_1192_, v___x_1200_, v___x_1193_, v___x_1197_);
lean_dec_ref_known(v___x_1200_, 2);
if (lean_obj_tag(v___x_1201_) == 0)
{
v___y_1187_ = v_b_1185_;
goto v___jp_1186_;
}
else
{
lean_object* v_val_1202_; lean_object* v_snd_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_val_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v___x_1201_, 1);
v_snd_1203_ = lean_ctor_get(v_val_1202_, 1);
lean_inc(v_snd_1203_);
lean_dec(v_val_1202_);
v___x_1204_ = lean_array_get_size(v_snd_1203_);
v___x_1205_ = lean_nat_dec_lt(v___x_1193_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec(v_snd_1203_);
v___y_1187_ = v_b_1185_;
goto v___jp_1186_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1204_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1203_, v___x_1206_, v___x_1207_, v_b_1185_);
lean_dec(v_snd_1203_);
v___y_1187_ = v___x_1208_;
goto v___jp_1186_;
}
}
}
}
}
else
{
lean_dec(v_incorrectName_1181_);
return v_b_1185_;
}
v___jp_1186_:
{
size_t v___x_1188_; size_t v___x_1189_; 
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_add(v_i_1183_, v___x_1188_);
v_i_1183_ = v___x_1189_;
v_b_1185_ = v___y_1187_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_incorrectName_1181_ = stack[0].m_obj;
lean_object* v_as_1182_ = stack[1].m_obj;
size_t v_i_1183_ = stack[2].m_num;
size_t v_stop_1184_ = stack[3].m_num;
lean_object* v_b_1185_ = stack[4].m_obj;
lean_object* v_res_1209_;
v_res_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1181_, v_as_1182_, v_i_1183_, v_stop_1184_, v_b_1185_);
stack->m_obj
 = v_res_1209_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object* v_incorrectName_1210_, lean_object* v_as_1211_, lean_object* v_i_1212_, lean_object* v_stop_1213_, lean_object* v_b_1214_){
_start:
{
size_t v_i_boxed_1215_; size_t v_stop_boxed_1216_; lean_object* v_res_1217_; 
v_i_boxed_1215_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_stop_boxed_1216_ = lean_unbox_usize(v_stop_1213_);
lean_dec(v_stop_1213_);
v_res_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1210_, v_as_1211_, v_i_boxed_1215_, v_stop_boxed_1216_, v_b_1214_);
lean_dec_ref(v_as_1211_);
return v_res_1217_;
}
}
lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object* v_incorrectName_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v___x_1224_; lean_object* v_snd_1225_; lean_object* v_toEnvExtension_1226_; lean_object* v_asyncMode_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v_importedEntries_1231_; lean_object* v_state_1232_; lean_object* v___y_1234_; lean_object* v___x_1243_; 
v___x_1221_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___x_1222_ = lean_st_ref_get(v___y_1219_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_1225_ = lean_ctor_get(v___x_1224_, 1);
v_toEnvExtension_1226_ = lean_ctor_get(v_snd_1225_, 0);
v_asyncMode_1227_ = lean_ctor_get(v_toEnvExtension_1226_, 2);
v___x_1228_ = lean_box(0);
v___x_1229_ = 0;
v___x_1230_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1221_, v_toEnvExtension_1226_, v_env_1223_, v_asyncMode_1227_, v___x_1228_, v___x_1229_);
v_importedEntries_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_importedEntries_1231_);
v_state_1232_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_state_1232_);
lean_dec(v___x_1230_);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1232_, v_incorrectName_1218_);
lean_dec(v_state_1232_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_NameSet_empty;
v___y_1234_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
lean_object* v_val_1245_; 
v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1243_, 1);
v___y_1234_ = v_val_1245_;
goto v___jp_1233_;
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_array_get_size(v_importedEntries_1231_);
v___x_1237_ = lean_nat_dec_lt(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec_ref(v_importedEntries_1231_);
lean_dec(v_incorrectName_1218_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___y_1234_);
return v___x_1238_;
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1236_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1218_, v_importedEntries_1231_, v___x_1239_, v___x_1240_, v___y_1234_);
lean_dec_ref(v_importedEntries_1231_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT void l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_incorrectName_1218_ = stack[0].m_obj;
lean_object* v___y_1219_ = stack[1].m_obj;
lean_object* v_res_1246_;
v_res_1246_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1218_, v___y_1219_);
stack->m_obj
 = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object* v_incorrectName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1247_, v___y_1248_);
lean_dec(v___y_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object* v_x_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0));
v___x_1254_ = lean_string_append(v___x_1253_, v_x_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object* v_x_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(v_x_1255_);
lean_dec_ref(v_x_1255_);
return v_res_1256_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, size_t v_sz_1265_, size_t v_i_1266_, lean_object* v_bs_1267_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_usize_dec_lt(v_i_1266_, v_sz_1265_);
if (v___x_1268_ == 0)
{
lean_dec(v___x_1264_);
lean_dec(v___x_1263_);
lean_dec_ref(v___x_1262_);
return v_bs_1267_;
}
else
{
lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v_v_1271_; lean_object* v_bs_x27_1272_; lean_object* v___y_1274_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_nat_dec_eq(v___x_1260_, v___x_1269_);
v_v_1271_ = lean_array_uget(v_bs_1267_, v_i_1266_);
v_bs_x27_1272_ = lean_array_uset(v_bs_1267_, v_i_1266_, v___x_1269_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_inc(v_v_1271_);
v___y_1274_ = v_v_1271_;
goto v___jp_1273_;
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_val_1291_ = lean_ctor_get(v___x_1261_, 0);
v___x_1292_ = lean_box(0);
lean_inc(v_v_1271_);
v___x_1293_ = l_Lean_Name_replacePrefix(v_v_1271_, v_val_1291_, v___x_1292_);
v___x_1294_ = l_Lean_Options_empty;
lean_inc(v___x_1293_);
lean_inc(v___x_1264_);
lean_inc(v___x_1263_);
lean_inc_ref(v___x_1262_);
v___x_1295_ = l_Lean_ResolveName_resolveGlobalName(v___x_1262_, v___x_1294_, v___x_1263_, v___x_1264_, v___x_1293_);
v___x_1296_ = l_List_lengthTR___redArg(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_dec_eq(v___x_1296_, v___x_1297_);
lean_dec(v___x_1296_);
if (v___x_1298_ == 0)
{
lean_dec(v___x_1293_);
lean_inc(v_v_1271_);
v___y_1274_ = v_v_1271_;
goto v___jp_1273_;
}
else
{
v___y_1274_ = v___x_1293_;
goto v___jp_1273_;
}
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_1274_, v___x_1268_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1279_ = l_Lean_MessageData_ofConstName(v_v_1271_, v___x_1270_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1278_);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
v___x_1283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1));
v___x_1284_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1276_);
lean_ctor_set(v___x_1284_, 1, v___x_1277_);
lean_ctor_set(v___x_1284_, 2, v___x_1277_);
lean_ctor_set(v___x_1284_, 3, v___x_1277_);
lean_ctor_set(v___x_1284_, 4, v___x_1282_);
lean_ctor_set(v___x_1284_, 5, v___x_1283_);
v___x_1285_ = 0;
v___x_1286_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1277_);
lean_ctor_set(v___x_1286_, 2, v___x_1277_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*3, v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_i_1266_, v___x_1287_);
v___x_1289_ = lean_array_uset(v_bs_x27_1272_, v_i_1266_, v___x_1286_);
v_i_1266_ = v___x_1288_;
v_bs_1267_ = v___x_1289_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1260_ = stack[0].m_obj;
lean_object* v___x_1261_ = stack[1].m_obj;
lean_object* v___x_1262_ = stack[2].m_obj;
lean_object* v___x_1263_ = stack[3].m_obj;
lean_object* v___x_1264_ = stack[4].m_obj;
size_t v_sz_1265_ = stack[5].m_num;
size_t v_i_1266_ = stack[6].m_num;
lean_object* v_bs_1267_ = stack[7].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_1260_, v___x_1261_, v___x_1262_, v___x_1263_, v___x_1264_, v_sz_1265_, v_i_1266_, v_bs_1267_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_bs_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_1300_, v___x_1301_, v___x_1302_, v___x_1303_, v___x_1304_, v_sz_boxed_1308_, v_i_boxed_1309_, v_bs_1307_);
lean_dec(v___x_1301_);
lean_dec(v___x_1300_);
return v_res_1310_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(lean_object* v_msgData_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v_env_1318_; uint8_t v___x_1319_; lean_object* v_env_1320_; lean_object* v___x_1321_; lean_object* v_toCold_1322_; lean_object* v_mctx_1323_; lean_object* v_lctx_1324_; lean_object* v_options_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1317_ = lean_st_ref_get(v___y_1315_);
v_env_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_env_1318_);
lean_dec(v___x_1317_);
v___x_1319_ = 0;
v_env_1320_ = l_Lean_Environment_setRecordingDeps(v_env_1318_, v___x_1319_);
v___x_1321_ = lean_st_ref_get(v___y_1313_);
v_toCold_1322_ = lean_ctor_get(v___y_1314_, 0);
v_mctx_1323_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref(v_mctx_1323_);
lean_dec(v___x_1321_);
v_lctx_1324_ = lean_ctor_get(v___y_1312_, 2);
v_options_1325_ = lean_ctor_get(v_toCold_1322_, 2);
lean_inc_ref(v_options_1325_);
lean_inc_ref(v_lctx_1324_);
v___x_1326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1326_, 0, v_env_1320_);
lean_ctor_set(v___x_1326_, 1, v_mctx_1323_);
lean_ctor_set(v___x_1326_, 2, v_lctx_1324_);
lean_ctor_set(v___x_1326_, 3, v_options_1325_);
v___x_1327_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v_msgData_1311_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1311_ = stack[0].m_obj;
lean_object* v___y_1312_ = stack[1].m_obj;
lean_object* v___y_1313_ = stack[2].m_obj;
lean_object* v___y_1314_ = stack[3].m_obj;
lean_object* v___y_1315_ = stack[4].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1336_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_box(1);
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2));
v___x_1343_ = l_Lean_MessageData_ofFormat(v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
if (lean_obj_tag(v_x_1345_) == 0)
{
return v_x_1344_;
}
else
{
lean_object* v_head_1346_; lean_object* v_tail_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1369_; 
v_head_1346_ = lean_ctor_get(v_x_1345_, 0);
v_tail_1347_ = lean_ctor_get(v_x_1345_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1345_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1349_ = v_x_1345_;
v_isShared_1350_ = v_isSharedCheck_1369_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_tail_1347_);
lean_inc(v_head_1346_);
lean_dec(v_x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1369_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_before_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1367_; 
v_before_1351_ = lean_ctor_get(v_head_1346_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_head_1346_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v_head_1346_, 1);
lean_dec(v_unused_1368_);
v___x_1353_ = v_head_1346_;
v_isShared_1354_ = v_isSharedCheck_1367_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_before_1351_);
lean_dec(v_head_1346_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1367_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 7);
lean_ctor_set(v___x_1353_, 1, v___x_1355_);
lean_ctor_set(v___x_1353_, 0, v_x_1344_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_x_1344_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3);
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 7);
lean_ctor_set(v___x_1349_, 1, v___x_1358_);
lean_ctor_set(v___x_1349_, 0, v___x_1357_);
v___x_1360_ = v___x_1349_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = l_Lean_MessageData_ofSyntax(v_before_1351_);
v___x_1362_ = l_Lean_indentD(v___x_1361_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1360_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v_x_1344_ = v___x_1363_;
v_x_1345_ = v_tail_1347_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(lean_object* v_opts_1370_, lean_object* v_opt_1371_){
_start:
{
lean_object* v_name_1372_; lean_object* v_defValue_1373_; lean_object* v_map_1374_; lean_object* v___x_1375_; 
v_name_1372_ = lean_ctor_get(v_opt_1371_, 0);
v_defValue_1373_ = lean_ctor_get(v_opt_1371_, 1);
v_map_1374_ = lean_ctor_get(v_opts_1370_, 0);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1374_, v_name_1372_);
if (lean_obj_tag(v___x_1375_) == 0)
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_unbox(v_defValue_1373_);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1375_, 1);
if (lean_obj_tag(v_val_1377_) == 1)
{
uint8_t v_v_1378_; 
v_v_1378_ = lean_ctor_get_uint8(v_val_1377_, 0);
lean_dec_ref_known(v_val_1377_, 0);
return v_v_1378_;
}
else
{
uint8_t v___x_1379_; 
lean_dec(v_val_1377_);
v___x_1379_ = lean_unbox(v_defValue_1373_);
return v___x_1379_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1370_ = stack[0].m_obj;
lean_object* v_opt_1371_ = stack[1].m_obj;
uint8_t v_res_1380_;
v_res_1380_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_1370_, v_opt_1371_);
stack->m_num = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(lean_object* v_opts_1381_, lean_object* v_opt_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_1381_, v_opt_1382_);
lean_dec_ref(v_opt_1382_);
lean_dec_ref(v_opts_1381_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1));
v___x_1389_ = l_Lean_MessageData_ofFormat(v___x_1388_);
return v___x_1389_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(lean_object* v_msgData_1390_, lean_object* v_macroStack_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1392_);
v___x_1395_ = l_Lean_Elab_pp_macroStack;
v___x_1396_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v___x_1394_, v___x_1395_);
lean_dec_ref(v___x_1394_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_macroStack_1391_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_msgData_1390_);
return v___x_1397_;
}
else
{
if (lean_obj_tag(v_macroStack_1391_) == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_msgData_1390_);
return v___x_1398_;
}
else
{
lean_object* v_head_1399_; lean_object* v_after_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1415_; 
v_head_1399_ = lean_ctor_get(v_macroStack_1391_, 0);
lean_inc(v_head_1399_);
v_after_1400_ = lean_ctor_get(v_head_1399_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_head_1399_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_head_1399_, 0);
lean_dec(v_unused_1416_);
v___x_1402_ = v_head_1399_;
v_isShared_1403_ = v_isSharedCheck_1415_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_after_1400_);
lean_dec(v_head_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1415_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 7);
lean_ctor_set(v___x_1402_, 1, v___x_1404_);
lean_ctor_set(v___x_1402_, 0, v_msgData_1390_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_msgData_1390_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_msgData_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1407_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = l_Lean_MessageData_ofSyntax(v_after_1400_);
v___x_1410_ = l_Lean_indentD(v___x_1409_);
v_msgData_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1411_, 0, v___x_1408_);
lean_ctor_set(v_msgData_1411_, 1, v___x_1410_);
v___x_1412_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(v_msgData_1411_, v_macroStack_1391_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1390_ = stack[0].m_obj;
lean_object* v_macroStack_1391_ = stack[1].m_obj;
lean_object* v___y_1392_ = stack[2].m_obj;
lean_object* v_res_1417_;
v_res_1417_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1390_, v_macroStack_1391_, v___y_1392_);
stack->m_obj
 = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_1418_, lean_object* v_macroStack_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1418_, v_macroStack_1419_, v___y_1420_);
lean_dec_ref(v___y_1420_);
return v_res_1422_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_ref_1431_; lean_object* v_macroStack_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_ref_1431_ = lean_ctor_get(v___y_1428_, 2);
v_macroStack_1432_ = lean_ctor_get(v___y_1424_, 1);
v___x_1433_ = l_Lean_Elab_getBetterRef(v_ref_1431_, v_macroStack_1432_);
v___x_1434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msg_1423_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
lean_inc(v_macroStack_1432_);
v___x_1436_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_a_1435_, v_macroStack_1432_, v___y_1428_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1433_);
lean_ctor_set(v___x_1441_, 1, v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 1);
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1423_ = stack[0].m_obj;
lean_object* v___y_1424_ = stack[1].m_obj;
lean_object* v___y_1425_ = stack[2].m_obj;
lean_object* v___y_1426_ = stack[3].m_obj;
lean_object* v___y_1427_ = stack[4].m_obj;
lean_object* v___y_1428_ = stack[5].m_obj;
lean_object* v___y_1429_ = stack[6].m_obj;
lean_object* v_res_1446_;
v_res_1446_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
stack->m_obj
 = v_res_1446_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1455_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(lean_object* v_ref_1456_, lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_toCold_1465_; lean_object* v_currRecDepth_1466_; lean_object* v_ref_1467_; uint16_t v_optionFlags_1468_; uint8_t v_suppressElabErrors_1469_; uint8_t v_isRecordingDeps_1470_; lean_object* v_ref_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_toCold_1465_ = lean_ctor_get(v___y_1462_, 0);
v_currRecDepth_1466_ = lean_ctor_get(v___y_1462_, 1);
v_ref_1467_ = lean_ctor_get(v___y_1462_, 2);
v_optionFlags_1468_ = lean_ctor_get_uint16(v___y_1462_, sizeof(void*)*3);
v_suppressElabErrors_1469_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1470_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*3 + 3);
v_ref_1471_ = l_Lean_replaceRef(v_ref_1456_, v_ref_1467_);
lean_inc(v_currRecDepth_1466_);
lean_inc_ref(v_toCold_1465_);
v___x_1472_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1472_, 0, v_toCold_1465_);
lean_ctor_set(v___x_1472_, 1, v_currRecDepth_1466_);
lean_ctor_set(v___x_1472_, 2, v_ref_1471_);
lean_ctor_set_uint16(v___x_1472_, sizeof(void*)*3, v_optionFlags_1468_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*3 + 2, v_suppressElabErrors_1469_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*3 + 3, v_isRecordingDeps_1470_);
v___x_1473_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___x_1472_, v___y_1463_);
lean_dec_ref_known(v___x_1472_, 3);
return v___x_1473_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1456_ = stack[0].m_obj;
lean_object* v_msg_1457_ = stack[1].m_obj;
lean_object* v___y_1458_ = stack[2].m_obj;
lean_object* v___y_1459_ = stack[3].m_obj;
lean_object* v___y_1460_ = stack[4].m_obj;
lean_object* v___y_1461_ = stack[5].m_obj;
lean_object* v___y_1462_ = stack[6].m_obj;
lean_object* v___y_1463_ = stack[7].m_obj;
lean_object* v_res_1474_;
v_res_1474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1456_, v_msg_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
stack->m_obj
 = v_res_1474_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1475_, v_msg_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_ref_1475_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4));
v___x_1493_ = l_Lean_stringToMessageData(v___x_1492_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6));
v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8));
v___x_1499_ = l_Lean_stringToMessageData(v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10));
v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__14));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__16));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__18));
v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__20));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(lean_object* v_msg_1518_, lean_object* v_declHint_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_env_1524_; uint8_t v___x_1525_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_st_ref_get(v___y_1520_);
v_env_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc_ref(v_env_1524_);
lean_dec(v___x_1523_);
v___x_1525_ = l_Lean_Name_isAnonymous(v_declHint_1519_);
if (v___x_1525_ == 0)
{
uint8_t v_isExporting_1526_; 
v_isExporting_1526_ = lean_ctor_get_uint8(v_env_1524_, sizeof(void*)*13);
if (v_isExporting_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_dec_ref(v_env_1524_);
lean_dec(v_declHint_1519_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_msg_1518_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; uint8_t v___x_1529_; 
lean_inc_ref(v_env_1524_);
v___x_1528_ = l_Lean_Environment_setExporting(v_env_1524_, v___x_1525_);
lean_inc(v_declHint_1519_);
lean_inc_ref(v___x_1528_);
v___x_1529_ = l_Lean_Environment_contains(v___x_1528_, v_declHint_1519_, v_isExporting_1526_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_dec_ref(v___x_1528_);
lean_dec_ref(v_env_1524_);
lean_dec(v_declHint_1519_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_msg_1518_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_c_1536_; lean_object* v___x_1537_; 
v___x_1531_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1532_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1533_ = l_Lean_Options_empty;
v___x_1534_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1528_);
lean_ctor_set(v___x_1534_, 1, v___x_1531_);
lean_ctor_set(v___x_1534_, 2, v___x_1532_);
lean_ctor_set(v___x_1534_, 3, v___x_1533_);
lean_inc(v_declHint_1519_);
v___x_1535_ = l_Lean_MessageData_ofConstName(v_declHint_1519_, v___x_1525_);
v_c_1536_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1536_, 0, v___x_1534_);
lean_ctor_set(v_c_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1524_, v_declHint_1519_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v_env_1524_);
lean_dec(v_declHint_1519_);
v___x_1538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v_c_1536_);
v___x_1540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_MessageData_note(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_msg_1518_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1601_; 
v_val_1545_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1547_ = v___x_1537_;
v_isShared_1548_ = v_isSharedCheck_1601_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_val_1545_);
lean_dec(v___x_1537_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1601_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v_modules_1550_; lean_object* v_moduleNames_1551_; lean_object* v_mod_1552_; uint8_t v___y_1554_; uint8_t v___x_1584_; 
v___x_1549_ = l_Lean_Environment_header(v_env_1524_);
lean_dec_ref(v_env_1524_);
v_modules_1550_ = lean_ctor_get(v___x_1549_, 3);
lean_inc_ref(v_modules_1550_);
v_moduleNames_1551_ = lean_ctor_get(v___x_1549_, 4);
lean_inc_ref(v_moduleNames_1551_);
lean_dec_ref(v___x_1549_);
v_mod_1552_ = lean_array_get(v___x_1522_, v_moduleNames_1551_, v_val_1545_);
lean_dec_ref(v_moduleNames_1551_);
v___x_1584_ = l_Lean_isPrivateName(v_declHint_1519_);
lean_dec(v_declHint_1519_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_array_get_size(v_modules_1550_);
v___x_1586_ = lean_nat_dec_lt(v_val_1545_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v_modules_1550_);
lean_dec(v_val_1545_);
v___y_1554_ = v___x_1584_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1587_; lean_object* v_toImport_1588_; uint8_t v_isExported_1589_; 
v___x_1587_ = lean_array_fget(v_modules_1550_, v_val_1545_);
lean_dec(v_val_1545_);
lean_dec_ref(v_modules_1550_);
v_toImport_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_ref(v_toImport_1588_);
lean_dec(v___x_1587_);
v_isExported_1589_ = lean_ctor_get_uint8(v_toImport_1588_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1588_);
v___y_1554_ = v_isExported_1589_;
goto v___jp_1553_;
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v_modules_1550_);
lean_del_object(v___x_1547_);
lean_dec(v_val_1545_);
v___x_1590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_c_1536_);
v___x_1592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__19);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_MessageData_ofName(v_mod_1552_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__21);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_MessageData_note(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_msg_1518_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
v___jp_1553_:
{
if (v___y_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_c_1536_);
v___x_1557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_ofName(v_mod_1552_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_MessageData_note(v___x_1562_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_msg_1518_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1564_);
v___x_1566_ = v___x_1547_;
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
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1568_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v_c_1536_);
v___x_1570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_MessageData_ofName(v_mod_1552_);
lean_inc_ref(v___x_1572_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__15);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1572_);
v___x_1577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__17);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_MessageData_note(v___x_1578_);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_msg_1518_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1580_);
v___x_1582_ = v___x_1547_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
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
lean_object* v___x_1602_; 
lean_dec_ref(v_env_1524_);
lean_dec(v_declHint_1519_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_msg_1518_);
return v___x_1602_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1518_ = stack[0].m_obj;
lean_object* v_declHint_1519_ = stack[1].m_obj;
lean_object* v___y_1520_ = stack[2].m_obj;
lean_object* v_res_1603_;
v_res_1603_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1518_, v_declHint_1519_, v___y_1520_);
stack->m_obj
 = v_res_1603_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1604_, lean_object* v_declHint_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1604_, v_declHint_1605_, v___y_1606_);
lean_dec(v___y_1606_);
return v_res_1608_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(lean_object* v_msg_1609_, lean_object* v_declHint_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1628_; 
v___x_1618_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1609_, v_declHint_1610_, v___y_1616_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1623_ = l_Lean_unknownIdentifierMessageTag;
v___x_1624_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1624_);
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1609_ = stack[0].m_obj;
lean_object* v_declHint_1610_ = stack[1].m_obj;
lean_object* v___y_1611_ = stack[2].m_obj;
lean_object* v___y_1612_ = stack[3].m_obj;
lean_object* v___y_1613_ = stack[4].m_obj;
lean_object* v___y_1614_ = stack[5].m_obj;
lean_object* v___y_1615_ = stack[6].m_obj;
lean_object* v___y_1616_ = stack[7].m_obj;
lean_object* v_res_1629_;
v_res_1629_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1609_, v_declHint_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(lean_object* v_msg_1630_, lean_object* v_declHint_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1630_, v_declHint_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1639_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(lean_object* v_ref_1640_, lean_object* v_msg_1641_, lean_object* v_declHint_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1641_, v_declHint_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1640_, v_a_1651_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1652_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1640_ = stack[0].m_obj;
lean_object* v_msg_1641_ = stack[1].m_obj;
lean_object* v_declHint_1642_ = stack[2].m_obj;
lean_object* v___y_1643_ = stack[3].m_obj;
lean_object* v___y_1644_ = stack[4].m_obj;
lean_object* v___y_1645_ = stack[5].m_obj;
lean_object* v___y_1646_ = stack[6].m_obj;
lean_object* v___y_1647_ = stack[7].m_obj;
lean_object* v___y_1648_ = stack[8].m_obj;
lean_object* v_res_1653_;
v_res_1653_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1640_, v_msg_1641_, v_declHint_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
stack->m_obj
 = v_res_1653_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(lean_object* v_ref_1654_, lean_object* v_msg_1655_, lean_object* v_declHint_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1654_, v_msg_1655_, v_declHint_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_ref_1654_);
return v_res_1664_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0));
v___x_1667_ = l_Lean_stringToMessageData(v___x_1666_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2));
v___x_1670_ = l_Lean_stringToMessageData(v___x_1669_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4));
v___x_1673_ = l_Lean_stringToMessageData(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6));
v___x_1676_ = l_Lean_stringToMessageData(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg(lean_object* v_constName_1683_, lean_object* v_idOrConst_1684_, lean_object* v_declHint_1685_, lean_object* v_ref_x3f_1686_, lean_object* v_extraMsg_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___y_1696_; lean_object* v_hint_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; uint8_t v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___x_1766_; lean_object* v_a_1767_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1791_; 
lean_inc(v_constName_1683_);
v___x_1766_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_constName_1683_, v_a_1693_);
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
if (lean_obj_tag(v_a_1767_) == 0)
{
lean_object* v_size_1796_; 
v_size_1796_ = lean_ctor_get(v_a_1767_, 0);
lean_inc(v_size_1796_);
v___y_1791_ = v_size_1796_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
v___y_1791_ = v___x_1797_;
goto v___jp_1790_;
}
v___jp_1695_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1704_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1);
v___x_1705_ = l_Lean_stringToMessageData(v_idOrConst_1684_);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = 0;
v___x_1710_ = l_Lean_MessageData_ofConstName(v_constName_1683_, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1708_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v_extraMsg_1687_);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v_hint_1697_);
v___x_1716_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v___y_1696_, v___x_1715_, v_declHint_1685_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1696_);
return v___x_1716_;
}
v___jp_1717_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; size_t v_sz_1733_; size_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1728_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v___y_1723_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___y_1727_);
v___x_1731_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v_sz_1733_ = lean_array_size(v___y_1721_);
v___x_1734_ = ((size_t)0ULL);
lean_inc(v___y_1720_);
lean_inc(v___y_1719_);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___y_1726_, v___y_1725_, v___y_1718_, v___y_1719_, v___y_1720_, v_sz_1733_, v___x_1734_, v___y_1721_);
lean_dec(v___y_1725_);
lean_dec(v___y_1726_);
lean_inc(v___y_1724_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___y_1724_);
v___x_1737_ = lean_box(0);
v___x_1738_ = l_Lean_MessageData_hint(v___x_1732_, v___x_1735_, v___x_1736_, v___x_1737_, v___y_1722_, v_a_1692_, v_a_1693_);
lean_dec_ref(v___x_1735_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___y_1696_ = v___y_1724_;
v_hint_1697_ = v_a_1739_;
v___y_1698_ = v_a_1688_;
v___y_1699_ = v_a_1689_;
v___y_1700_ = v_a_1690_;
v___y_1701_ = v_a_1691_;
v___y_1702_ = v_a_1692_;
v___y_1703_ = v_a_1693_;
goto v___jp_1695_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v___y_1724_);
lean_dec_ref(v_extraMsg_1687_);
lean_dec(v_declHint_1685_);
lean_dec_ref(v_idOrConst_1684_);
lean_dec(v_constName_1683_);
v_a_1740_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1738_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
v___jp_1748_:
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Lean_Name_isAnonymous(v___y_1749_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1760_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9);
v___x_1761_ = l_Lean_MessageData_ofName(v___y_1749_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___y_1718_ = v___y_1750_;
v___y_1719_ = v___y_1751_;
v___y_1720_ = v___y_1753_;
v___y_1721_ = v___y_1752_;
v___y_1722_ = v___y_1754_;
v___y_1723_ = v___y_1758_;
v___y_1724_ = v___y_1755_;
v___y_1725_ = v___y_1756_;
v___y_1726_ = v___y_1757_;
v___y_1727_ = v___x_1764_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1765_; 
lean_dec(v___y_1749_);
v___x_1765_ = l_Lean_MessageData_nil;
v___y_1718_ = v___y_1750_;
v___y_1719_ = v___y_1751_;
v___y_1720_ = v___y_1753_;
v___y_1721_ = v___y_1752_;
v___y_1722_ = v___y_1754_;
v___y_1723_ = v___y_1758_;
v___y_1724_ = v___y_1755_;
v___y_1725_ = v___y_1756_;
v___y_1726_ = v___y_1757_;
v___y_1727_ = v___x_1765_;
goto v___jp_1717_;
}
}
v___jp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = lean_array_get_size(v___y_1769_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_nat_dec_eq(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_toCold_1776_; lean_object* v_env_1777_; lean_object* v_currNamespace_1778_; lean_object* v_openDecls_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1774_ = l_Lean_Syntax_getId(v___y_1770_);
v___x_1775_ = lean_st_ref_get(v_a_1693_);
v_toCold_1776_ = lean_ctor_get(v_a_1692_, 0);
v_env_1777_ = lean_ctor_get(v___x_1775_, 0);
lean_inc_ref(v_env_1777_);
lean_dec(v___x_1775_);
v_currNamespace_1778_ = lean_ctor_get(v_toCold_1776_, 4);
v_openDecls_1779_ = lean_ctor_get(v_toCold_1776_, 5);
lean_inc(v_constName_1683_);
v___x_1780_ = l_Lean_Name_eraseSuffix_x3f(v_constName_1683_, v___x_1774_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_nat_dec_eq(v___x_1771_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11);
v___y_1749_ = v___x_1774_;
v___y_1750_ = v_env_1777_;
v___y_1751_ = v_currNamespace_1778_;
v___y_1752_ = v___y_1769_;
v___y_1753_ = v_openDecls_1779_;
v___y_1754_ = v___x_1773_;
v___y_1755_ = v___y_1770_;
v___y_1756_ = v___x_1780_;
v___y_1757_ = v___x_1771_;
v___y_1758_ = v___x_1783_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1784_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1785_ = lean_array_fget_borrowed(v___y_1769_, v___x_1772_);
lean_inc(v___x_1785_);
v___x_1786_ = l_Lean_MessageData_ofConstName(v___x_1785_, v___x_1773_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1784_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v___x_1784_);
v___y_1749_ = v___x_1774_;
v___y_1750_ = v_env_1777_;
v___y_1751_ = v_currNamespace_1778_;
v___y_1752_ = v___y_1769_;
v___y_1753_ = v_openDecls_1779_;
v___y_1754_ = v___x_1773_;
v___y_1755_ = v___y_1770_;
v___y_1756_ = v___x_1780_;
v___y_1757_ = v___x_1771_;
v___y_1758_ = v___x_1788_;
goto v___jp_1748_;
}
}
else
{
lean_object* v___x_1789_; 
lean_dec_ref(v___y_1769_);
v___x_1789_ = l_Lean_MessageData_nil;
v___y_1696_ = v___y_1770_;
v_hint_1697_ = v___x_1789_;
v___y_1698_ = v_a_1688_;
v___y_1699_ = v_a_1689_;
v___y_1700_ = v_a_1690_;
v___y_1701_ = v_a_1691_;
v___y_1702_ = v_a_1692_;
v___y_1703_ = v_a_1693_;
goto v___jp_1695_;
}
}
v___jp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_mk_empty_array_with_capacity(v___y_1791_);
lean_dec(v___y_1791_);
v___x_1793_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_1792_, v_a_1767_);
if (lean_obj_tag(v_ref_x3f_1686_) == 0)
{
lean_object* v_ref_1794_; 
v_ref_1794_ = lean_ctor_get(v_a_1692_, 2);
lean_inc(v_ref_1794_);
v___y_1769_ = v___x_1793_;
v___y_1770_ = v_ref_1794_;
goto v___jp_1768_;
}
else
{
lean_object* v_val_1795_; 
v_val_1795_ = lean_ctor_get(v_ref_x3f_1686_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v_ref_x3f_1686_, 1);
v___y_1769_ = v___x_1793_;
v___y_1770_ = v_val_1795_;
goto v___jp_1768_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwUnknownNameWithSuggestions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1683_ = stack[0].m_obj;
lean_object* v_idOrConst_1684_ = stack[1].m_obj;
lean_object* v_declHint_1685_ = stack[2].m_obj;
lean_object* v_ref_x3f_1686_ = stack[3].m_obj;
lean_object* v_extraMsg_1687_ = stack[4].m_obj;
lean_object* v_a_1688_ = stack[5].m_obj;
lean_object* v_a_1689_ = stack[6].m_obj;
lean_object* v_a_1690_ = stack[7].m_obj;
lean_object* v_a_1691_ = stack[8].m_obj;
lean_object* v_a_1692_ = stack[9].m_obj;
lean_object* v_a_1693_ = stack[10].m_obj;
lean_object* v_res_1798_;
v_res_1798_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1683_, v_idOrConst_1684_, v_declHint_1685_, v_ref_x3f_1686_, v_extraMsg_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
stack->m_obj
 = v_res_1798_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(lean_object* v_constName_1799_, lean_object* v_idOrConst_1800_, lean_object* v_declHint_1801_, lean_object* v_ref_x3f_1802_, lean_object* v_extraMsg_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1799_, v_idOrConst_1800_, v_declHint_1801_, v_ref_x3f_1802_, v_extraMsg_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
return v_res_1811_;
}
}
lean_object* l_Lean_throwUnknownNameWithSuggestions(lean_object* v_00_u03b1_1812_, lean_object* v_constName_1813_, lean_object* v_idOrConst_1814_, lean_object* v_declHint_1815_, lean_object* v_ref_x3f_1816_, lean_object* v_extraMsg_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1813_, v_idOrConst_1814_, v_declHint_1815_, v_ref_x3f_1816_, v_extraMsg_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownNameWithSuggestions_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1813_ = stack[1].m_obj;
lean_object* v_idOrConst_1814_ = stack[2].m_obj;
lean_object* v_declHint_1815_ = stack[3].m_obj;
lean_object* v_ref_x3f_1816_ = stack[4].m_obj;
lean_object* v_extraMsg_1817_ = stack[5].m_obj;
lean_object* v_a_1818_ = stack[6].m_obj;
lean_object* v_a_1819_ = stack[7].m_obj;
lean_object* v_a_1820_ = stack[8].m_obj;
lean_object* v_a_1821_ = stack[9].m_obj;
lean_object* v_a_1822_ = stack[10].m_obj;
lean_object* v_a_1823_ = stack[11].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l_Lean_throwUnknownNameWithSuggestions(lean_box(0), v_constName_1813_, v_idOrConst_1814_, v_declHint_1815_, v_ref_x3f_1816_, v_extraMsg_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___boxed(lean_object* v_00_u03b1_1827_, lean_object* v_constName_1828_, lean_object* v_idOrConst_1829_, lean_object* v_declHint_1830_, lean_object* v_ref_x3f_1831_, lean_object* v_extraMsg_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_throwUnknownNameWithSuggestions(v_00_u03b1_1827_, v_constName_1828_, v_idOrConst_1829_, v_declHint_1830_, v_ref_x3f_1831_, v_extraMsg_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1840_;
}
}
lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(lean_object* v_incorrectName_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1841_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT void l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_incorrectName_1841_ = stack[0].m_obj;
lean_object* v___y_1842_ = stack[1].m_obj;
lean_object* v___y_1843_ = stack[2].m_obj;
lean_object* v___y_1844_ = stack[3].m_obj;
lean_object* v___y_1845_ = stack[4].m_obj;
lean_object* v___y_1846_ = stack[5].m_obj;
lean_object* v___y_1847_ = stack[6].m_obj;
lean_object* v_res_1850_;
v_res_1850_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(v_incorrectName_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(lean_object* v_incorrectName_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(v_incorrectName_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1859_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_object* v_00_u03b1_1860_, lean_object* v_ref_1861_, lean_object* v_msg_1862_, lean_object* v_declHint_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1861_, v_msg_1862_, v_declHint_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1861_ = stack[1].m_obj;
lean_object* v_msg_1862_ = stack[2].m_obj;
lean_object* v_declHint_1863_ = stack[3].m_obj;
lean_object* v___y_1864_ = stack[4].m_obj;
lean_object* v___y_1865_ = stack[5].m_obj;
lean_object* v___y_1866_ = stack[6].m_obj;
lean_object* v___y_1867_ = stack[7].m_obj;
lean_object* v___y_1868_ = stack[8].m_obj;
lean_object* v___y_1869_ = stack[9].m_obj;
lean_object* v_res_1872_;
v_res_1872_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_box(0), v_ref_1861_, v_msg_1862_, v_declHint_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
stack->m_obj
 = v_res_1872_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(lean_object* v_00_u03b1_1873_, lean_object* v_ref_1874_, lean_object* v_msg_1875_, lean_object* v_declHint_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(v_00_u03b1_1873_, v_ref_1874_, v_msg_1875_, v_declHint_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v_ref_1874_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(lean_object* v_as_1885_, lean_object* v_k_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1885_, v_k_1886_, v_x_1887_, v_x_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(lean_object* v_as_1891_, lean_object* v_k_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(v_as_1891_, v_k_1892_, v_x_1893_, v_x_1894_, v_x_1895_);
lean_dec_ref(v_k_1892_);
lean_dec_ref(v_as_1891_);
return v_res_1896_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(lean_object* v_msg_1897_, lean_object* v_declHint_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1897_, v_declHint_1898_, v___y_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1897_ = stack[0].m_obj;
lean_object* v_declHint_1898_ = stack[1].m_obj;
lean_object* v___y_1899_ = stack[2].m_obj;
lean_object* v___y_1900_ = stack[3].m_obj;
lean_object* v___y_1901_ = stack[4].m_obj;
lean_object* v___y_1902_ = stack[5].m_obj;
lean_object* v___y_1903_ = stack[6].m_obj;
lean_object* v___y_1904_ = stack[7].m_obj;
lean_object* v_res_1907_;
v_res_1907_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_1897_, v_declHint_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
stack->m_obj
 = v_res_1907_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1908_, lean_object* v_declHint_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_1908_, v_declHint_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1917_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_object* v_00_u03b1_1918_, lean_object* v_ref_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1919_, v_msg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1919_ = stack[1].m_obj;
lean_object* v_msg_1920_ = stack[2].m_obj;
lean_object* v___y_1921_ = stack[3].m_obj;
lean_object* v___y_1922_ = stack[4].m_obj;
lean_object* v___y_1923_ = stack[5].m_obj;
lean_object* v___y_1924_ = stack[6].m_obj;
lean_object* v___y_1925_ = stack[7].m_obj;
lean_object* v___y_1926_ = stack[8].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_box(0), v_ref_1919_, v_msg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1930_, lean_object* v_ref_1931_, lean_object* v_msg_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(v_00_u03b1_1930_, v_ref_1931_, v_msg_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v_ref_1931_);
return v_res_1940_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1941_, lean_object* v_msg_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1942_ = stack[1].m_obj;
lean_object* v___y_1943_ = stack[2].m_obj;
lean_object* v___y_1944_ = stack[3].m_obj;
lean_object* v___y_1945_ = stack[4].m_obj;
lean_object* v___y_1946_ = stack[5].m_obj;
lean_object* v___y_1947_ = stack[6].m_obj;
lean_object* v___y_1948_ = stack[7].m_obj;
lean_object* v_res_1951_;
v_res_1951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_box(0), v_msg_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
stack->m_obj
 = v_res_1951_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(v_00_u03b1_1952_, v_msg_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1961_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(lean_object* v_msgData_1962_, lean_object* v_macroStack_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1962_, v_macroStack_1963_, v___y_1968_);
return v___x_1971_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1962_ = stack[0].m_obj;
lean_object* v_macroStack_1963_ = stack[1].m_obj;
lean_object* v___y_1964_ = stack[2].m_obj;
lean_object* v___y_1965_ = stack[3].m_obj;
lean_object* v___y_1966_ = stack[4].m_obj;
lean_object* v___y_1967_ = stack[5].m_obj;
lean_object* v___y_1968_ = stack[6].m_obj;
lean_object* v___y_1969_ = stack[7].m_obj;
lean_object* v_res_1972_;
v_res_1972_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_1962_, v_macroStack_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
stack->m_obj
 = v_res_1972_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(lean_object* v_msgData_1973_, lean_object* v_macroStack_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_1973_, v_macroStack_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1982_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(lean_object* v_exp_1983_, lean_object* v_as_1984_, size_t v_i_1985_, size_t v_stop_1986_){
_start:
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_usize_dec_eq(v_i_1985_, v_stop_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = lean_array_uget_borrowed(v_as_1984_, v_i_1985_);
v___x_1989_ = lean_expr_eqv(v___x_1988_, v_exp_1983_);
if (v___x_1989_ == 0)
{
size_t v___x_1990_; size_t v___x_1991_; 
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_i_1985_, v___x_1990_);
v_i_1985_ = v___x_1991_;
goto _start;
}
else
{
return v___x_1989_;
}
}
else
{
uint8_t v___x_1993_; 
v___x_1993_ = 0;
return v___x_1993_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_exp_1983_ = stack[0].m_obj;
lean_object* v_as_1984_ = stack[1].m_obj;
size_t v_i_1985_ = stack[2].m_num;
size_t v_stop_1986_ = stack[3].m_num;
uint8_t v_res_1994_;
v_res_1994_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1983_, v_as_1984_, v_i_1985_, v_stop_1986_);
stack->m_num = v_res_1994_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(lean_object* v_exp_1995_, lean_object* v_as_1996_, lean_object* v_i_1997_, lean_object* v_stop_1998_){
_start:
{
size_t v_i_boxed_1999_; size_t v_stop_boxed_2000_; uint8_t v_res_2001_; lean_object* v_r_2002_; 
v_i_boxed_1999_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_stop_boxed_2000_ = lean_unbox_usize(v_stop_1998_);
lean_dec(v_stop_1998_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1995_, v_as_1996_, v_i_boxed_1999_, v_stop_boxed_2000_);
lean_dec_ref(v_as_1996_);
lean_dec_ref(v_exp_1995_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(lean_object* v_exp_2003_, lean_object* v_x_2004_){
_start:
{
if (lean_obj_tag(v_x_2004_) == 0)
{
lean_object* v_cs_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_cs_2005_ = lean_ctor_get(v_x_2004_, 0);
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_array_get_size(v_cs_2005_);
v___x_2008_ = lean_nat_dec_lt(v___x_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
return v___x_2008_;
}
else
{
if (v___x_2008_ == 0)
{
return v___x_2008_;
}
else
{
size_t v___x_2009_; size_t v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_of_nat(v___x_2007_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_2003_, v_cs_2005_, v___x_2009_, v___x_2010_);
return v___x_2011_;
}
}
}
else
{
lean_object* v_vs_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_vs_2012_ = lean_ctor_get(v_x_2004_, 0);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_array_get_size(v_vs_2012_);
v___x_2015_ = lean_nat_dec_lt(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
size_t v___x_2016_; size_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = lean_usize_of_nat(v___x_2014_);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_2003_, v_vs_2012_, v___x_2016_, v___x_2017_);
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_exp_2003_ = stack[0].m_obj;
lean_object* v_x_2004_ = stack[1].m_obj;
uint8_t v_res_2019_;
v_res_2019_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_2003_, v_x_2004_);
stack->m_num = v_res_2019_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(lean_object* v_exp_2020_, lean_object* v_as_2021_, size_t v_i_2022_, size_t v_stop_2023_){
_start:
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_usize_dec_eq(v_i_2022_, v_stop_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_array_uget_borrowed(v_as_2021_, v_i_2022_);
v___x_2026_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_2020_, v___x_2025_);
if (v___x_2026_ == 0)
{
size_t v___x_2027_; size_t v___x_2028_; 
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2022_, v___x_2027_);
v_i_2022_ = v___x_2028_;
goto _start;
}
else
{
return v___x_2026_;
}
}
else
{
uint8_t v___x_2030_; 
v___x_2030_ = 0;
return v___x_2030_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_exp_2020_ = stack[0].m_obj;
lean_object* v_as_2021_ = stack[1].m_obj;
size_t v_i_2022_ = stack[2].m_num;
size_t v_stop_2023_ = stack[3].m_num;
uint8_t v_res_2031_;
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_2020_, v_as_2021_, v_i_2022_, v_stop_2023_);
stack->m_num = v_res_2031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(lean_object* v_exp_2032_, lean_object* v_as_2033_, lean_object* v_i_2034_, lean_object* v_stop_2035_){
_start:
{
size_t v_i_boxed_2036_; size_t v_stop_boxed_2037_; uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_i_boxed_2036_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_stop_boxed_2037_ = lean_unbox_usize(v_stop_2035_);
lean_dec(v_stop_2035_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_2032_, v_as_2033_, v_i_boxed_2036_, v_stop_boxed_2037_);
lean_dec_ref(v_as_2033_);
lean_dec_ref(v_exp_2032_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(lean_object* v_exp_2040_, lean_object* v_x_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_2040_, v_x_2041_);
lean_dec_ref(v_x_2041_);
lean_dec_ref(v_exp_2040_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(lean_object* v_exp_2044_, lean_object* v_t_2045_){
_start:
{
lean_object* v_root_2046_; lean_object* v_tail_2047_; uint8_t v___x_2048_; 
v_root_2046_ = lean_ctor_get(v_t_2045_, 0);
v_tail_2047_ = lean_ctor_get(v_t_2045_, 1);
v___x_2048_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_2044_, v_root_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_array_get_size(v_tail_2047_);
v___x_2051_ = lean_nat_dec_lt(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
return v___x_2051_;
}
else
{
if (v___x_2051_ == 0)
{
return v___x_2051_;
}
else
{
size_t v___x_2052_; size_t v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = ((size_t)0ULL);
v___x_2053_ = lean_usize_of_nat(v___x_2050_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_2044_, v_tail_2047_, v___x_2052_, v___x_2053_);
return v___x_2054_;
}
}
}
else
{
return v___x_2048_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_exp_2044_ = stack[0].m_obj;
lean_object* v_t_2045_ = stack[1].m_obj;
uint8_t v_res_2055_;
v_res_2055_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_2044_, v_t_2045_);
stack->m_num = v_res_2055_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(lean_object* v_exp_2056_, lean_object* v_t_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_2056_, v_t_2057_);
lean_dec_ref(v_t_2057_);
lean_dec_ref(v_exp_2056_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(lean_object* v_init_2060_, lean_object* v_x_2061_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v_k_2062_; lean_object* v_l_2063_; lean_object* v_r_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_k_2062_ = lean_ctor_get(v_x_2061_, 1);
v_l_2063_ = lean_ctor_get(v_x_2061_, 3);
v_r_2064_ = lean_ctor_get(v_x_2061_, 4);
v___x_2065_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_2060_, v_r_2064_);
lean_inc(v_k_2062_);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_k_2062_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v_init_2060_ = v___x_2066_;
v_x_2061_ = v_l_2063_;
goto _start;
}
else
{
return v_init_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(lean_object* v_init_2068_, lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_2068_, v_x_2069_);
lean_dec(v_x_2069_);
return v_res_2070_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0));
v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
if (lean_obj_tag(v_a_2074_) == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = l_List_reverse___redArg(v_a_2075_);
return v___x_2076_;
}
else
{
lean_object* v_head_2077_; lean_object* v_tail_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2093_; 
v_head_2077_ = lean_ctor_get(v_a_2074_, 0);
v_tail_2078_ = lean_ctor_get(v_a_2074_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2080_ = v_a_2074_;
v_isShared_2081_ = v_isSharedCheck_2093_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_tail_2078_);
lean_inc(v_head_2077_);
lean_dec(v_a_2074_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2093_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2082_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1);
v___x_2083_ = 0;
v___x_2084_ = l_Lean_MessageData_ofConstName(v_head_2077_, v___x_2083_);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2082_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_indentD(v___x_2087_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v_a_2075_);
lean_ctor_set(v___x_2080_, 0, v___x_2088_);
v___x_2090_ = v___x_2080_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_a_2075_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_a_2074_ = v_tail_2078_;
v_a_2075_ = v___x_2090_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2));
v___x_2099_ = l_Lean_stringToMessageData(v___x_2098_);
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4));
v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
return v___x_2102_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6));
v___x_2105_ = l_Lean_stringToMessageData(v___x_2104_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(lean_object* v_exp_2123_, lean_object* v_expected_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_autoBoundImplicitContext_2133_; 
v_autoBoundImplicitContext_2133_ = lean_ctor_get(v_a_2125_, 2);
if (lean_obj_tag(v_autoBoundImplicitContext_2133_) == 0)
{
lean_dec_ref(v_expected_2124_);
goto v___jp_2130_;
}
else
{
lean_object* v_val_2134_; uint8_t v___x_2135_; 
v_val_2134_ = lean_ctor_get(v_autoBoundImplicitContext_2133_, 0);
v___x_2135_ = l_Lean_Expr_isFVar(v_exp_2123_);
if (v___x_2135_ == 0)
{
lean_dec_ref(v_expected_2124_);
goto v___jp_2130_;
}
else
{
lean_object* v_boundVariables_2136_; uint8_t v___x_2137_; 
v_boundVariables_2136_ = lean_ctor_get(v_val_2134_, 0);
v___x_2137_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_2123_, v_boundVariables_2136_);
if (v___x_2137_ == 0)
{
lean_dec_ref(v_expected_2124_);
goto v___jp_2130_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = l_Lean_Expr_fvarId_x21(v_exp_2123_);
v___x_2139_ = l_Lean_FVarId_getUserName___redArg(v___x_2138_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2198_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc_n(v_a_2140_, 2);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1);
v___x_2142_ = l_Lean_MessageData_ofName(v_a_2140_);
lean_inc_ref(v___x_2142_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_stringToMessageData(v_expected_2124_);
lean_inc_ref(v___x_2146_);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v___x_2146_);
v___x_2151_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_a_2140_, v_a_2128_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2198_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2198_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___y_2159_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v___x_2165_, v_a_2154_);
lean_dec(v_a_2154_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v___x_2167_; 
lean_dec_ref(v___x_2142_);
v___x_2167_ = l_Lean_MessageData_nil;
v___y_2159_ = v___x_2167_;
goto v___jp_2158_;
}
else
{
lean_object* v_tail_2168_; 
v_tail_2168_ = lean_ctor_get(v___x_2166_, 1);
if (lean_obj_tag(v_tail_2168_) == 0)
{
lean_object* v_head_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2186_; 
v_head_2169_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v___x_2166_, 1);
lean_dec(v_unused_2187_);
v___x_2171_ = v___x_2166_;
v_isShared_2172_ = v_isSharedCheck_2186_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_head_2169_);
lean_dec(v___x_2166_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2186_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2173_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2174_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10);
v___x_2175_ = 0;
v___x_2176_ = l_Lean_MessageData_ofConstName(v_head_2169_, v___x_2175_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 7);
lean_ctor_set(v___x_2171_, 1, v___x_2176_);
lean_ctor_set(v___x_2171_, 0, v___x_2174_);
v___x_2178_ = v___x_2171_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2179_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12);
v___x_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2142_);
v___x_2182_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2173_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___y_2159_ = v___x_2184_;
goto v___jp_2158_;
}
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2188_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2189_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2142_);
v___x_2191_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2188_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(v___x_2166_, v___x_2165_);
v___x_2195_ = l_Lean_MessageData_nil;
v___x_2196_ = l_Lean_MessageData_joinSep(v___x_2194_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2193_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___y_2159_ = v___x_2197_;
goto v___jp_2158_;
}
}
v___jp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2152_);
lean_ctor_set(v___x_2160_, 1, v___y_2159_);
v___x_2161_ = l_Lean_MessageData_hint_x27(v___x_2160_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2161_);
v___x_2163_ = v___x_2156_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_expected_2124_);
v_a_2199_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2139_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2139_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
v___jp_2130_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = l_Lean_MessageData_nil;
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_hintAutoImplicitFailure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_exp_2123_ = stack[0].m_obj;
lean_object* v_expected_2124_ = stack[1].m_obj;
lean_object* v_a_2125_ = stack[2].m_obj;
lean_object* v_a_2126_ = stack[3].m_obj;
lean_object* v_a_2127_ = stack[4].m_obj;
lean_object* v_a_2128_ = stack[5].m_obj;
lean_object* v_res_2207_;
v_res_2207_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2123_, v_expected_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
stack->m_obj
 = v_res_2207_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(lean_object* v_exp_2208_, lean_object* v_expected_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2208_, v_expected_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec_ref(v_exp_2208_);
return v_res_2215_;
}
}
lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure(lean_object* v_exp_2216_, lean_object* v_expected_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2216_, v_expected_2217_, v_a_2218_, v_a_2220_, v_a_2222_, v_a_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_hintAutoImplicitFailure_0interp(lean_interpreter_value* stack)
{
lean_object* v_exp_2216_ = stack[0].m_obj;
lean_object* v_expected_2217_ = stack[1].m_obj;
lean_object* v_a_2218_ = stack[2].m_obj;
lean_object* v_a_2219_ = stack[3].m_obj;
lean_object* v_a_2220_ = stack[4].m_obj;
lean_object* v_a_2221_ = stack[5].m_obj;
lean_object* v_a_2222_ = stack[6].m_obj;
lean_object* v_a_2223_ = stack[7].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l_Lean_Elab_Term_hintAutoImplicitFailure(v_exp_2216_, v_expected_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(lean_object* v_exp_2227_, lean_object* v_expected_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Elab_Term_hintAutoImplicitFailure(v_exp_2227_, v_expected_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec_ref(v_exp_2227_);
return v_res_2236_;
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
