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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l_Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Cannot make suggestions for private names"};
static const lean_object* l_Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l_Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid `[suggest_for]` attribute syntax "};
static const lean_object* l_Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l_Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l_Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "identifierSuggestionsImpl"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 206, 69, 219, 26, 51, 91, 166)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggest_for"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 123, 198, 36, 120, 51, 50, 116)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "suggest other (incorrect, not-existing) identifiers that someone might use when they actually want this definition"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_getSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getSuggestions___redArg___closed__0 = (const lean_object*)&l_Lean_getSuggestions___redArg___closed__0_value;
static lean_once_cell_t l_Lean_getSuggestions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getSuggestions___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Change to "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_old_19_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(lean_object* v_as_88_, lean_object* v_lo_89_, lean_object* v_hi_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_nat_dec_lt(v_lo_89_, v_hi_90_);
if (v___x_91_ == 0)
{
lean_dec(v_lo_89_);
return v_as_88_;
}
else
{
lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v_fst_94_; lean_object* v_snd_95_; uint8_t v___x_96_; 
v___f_92_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___closed__0));
lean_inc(v_lo_89_);
v___x_93_ = l_Array_qpartition___redArg(v_as_88_, v___f_92_, v_lo_89_, v_hi_90_);
v_fst_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_fst_94_);
v_snd_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_snd_95_);
lean_dec_ref(v___x_93_);
v___x_96_ = lean_nat_dec_le(v_hi_90_, v_fst_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_snd_95_, v_lo_89_, v_fst_94_);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_add(v_fst_94_, v___x_98_);
lean_dec(v_fst_94_);
v_as_88_ = v___x_97_;
v_lo_89_ = v___x_99_;
goto _start;
}
else
{
lean_dec(v_fst_94_);
lean_dec(v_lo_89_);
return v_snd_95_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___boxed(lean_object* v_as_101_, lean_object* v_lo_102_, lean_object* v_hi_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_as_101_, v_lo_102_, v_hi_103_);
lean_dec(v_hi_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(lean_object* v_init_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v_k_107_; lean_object* v_l_108_; lean_object* v_r_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_k_107_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_k_107_);
v_l_108_ = lean_ctor_get(v_x_106_, 3);
lean_inc(v_l_108_);
v_r_109_ = lean_ctor_get(v_x_106_, 4);
lean_inc(v_r_109_);
lean_dec_ref(v_x_106_);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_105_, v_l_108_);
v___x_111_ = lean_array_push(v___x_110_, v_k_107_);
v_init_105_ = v___x_111_;
v_x_106_ = v_r_109_;
goto _start;
}
else
{
return v_init_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(size_t v_sz_113_, size_t v_i_114_, lean_object* v_bs_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_usize_dec_lt(v_i_114_, v_sz_113_);
if (v___x_116_ == 0)
{
return v_bs_115_;
}
else
{
lean_object* v_v_117_; lean_object* v_fst_118_; lean_object* v_snd_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_137_; 
v_v_117_ = lean_array_uget(v_bs_115_, v_i_114_);
v_fst_118_ = lean_ctor_get(v_v_117_, 0);
v_snd_119_ = lean_ctor_get(v_v_117_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_v_117_);
if (v_isSharedCheck_137_ == 0)
{
v___x_121_ = v_v_117_;
v_isShared_122_ = v_isSharedCheck_137_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snd_119_);
lean_inc(v_fst_118_);
lean_dec(v_v_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_137_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v_bs_x27_124_; lean_object* v___y_126_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v_bs_x27_124_ = lean_array_uset(v_bs_115_, v_i_114_, v___x_123_);
if (lean_obj_tag(v_snd_119_) == 0)
{
lean_object* v_size_136_; 
v_size_136_ = lean_ctor_get(v_snd_119_, 0);
lean_inc(v_size_136_);
v___y_126_ = v_size_136_;
goto v___jp_125_;
}
else
{
v___y_126_ = v___x_123_;
goto v___jp_125_;
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = lean_mk_empty_array_with_capacity(v___y_126_);
lean_dec(v___y_126_);
v___x_128_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_127_, v_snd_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_128_);
v___x_130_ = v___x_121_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_fst_118_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_135_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_114_, v___x_131_);
v___x_133_ = lean_array_uset(v_bs_x27_124_, v_i_114_, v___x_130_);
v_i_114_ = v___x_132_;
v_bs_115_ = v___x_133_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2___boxed(lean_object* v_sz_138_, lean_object* v_i_139_, lean_object* v_bs_140_){
_start:
{
size_t v_sz_boxed_141_; size_t v_i_boxed_142_; lean_object* v_res_143_; 
v_sz_boxed_141_ = lean_unbox_usize(v_sz_138_);
lean_dec(v_sz_138_);
v_i_boxed_142_ = lean_unbox_usize(v_i_139_);
lean_dec(v_i_139_);
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_boxed_141_, v_i_boxed_142_, v_bs_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(lean_object* v_init_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v_k_146_; lean_object* v_v_147_; lean_object* v_l_148_; lean_object* v_r_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_k_146_ = lean_ctor_get(v_x_145_, 1);
v_v_147_ = lean_ctor_get(v_x_145_, 2);
v_l_148_ = lean_ctor_get(v_x_145_, 3);
v_r_149_ = lean_ctor_get(v_x_145_, 4);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_144_, v_l_148_);
lean_inc(v_v_147_);
lean_inc(v_k_146_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_k_146_);
lean_ctor_set(v___x_151_, 1, v_v_147_);
v___x_152_ = lean_array_push(v___x_150_, v___x_151_);
v_init_144_ = v___x_152_;
v_x_145_ = v_r_149_;
goto _start;
}
else
{
return v_init_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2___boxed(lean_object* v_init_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_154_, v_x_155_);
lean_dec(v_x_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(lean_object* v_x_159_, lean_object* v_s_160_, uint8_t v_x_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; size_t v_sz_165_; size_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0));
v___x_164_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_163_, v_s_160_);
v_sz_165_ = lean_array_size(v___x_164_);
v___x_166_ = ((size_t)0ULL);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_165_, v___x_166_, v___x_164_);
v___x_168_ = lean_array_get_size(v___x_167_);
v___x_169_ = lean_nat_dec_eq(v___x_168_, v___x_162_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___y_173_; uint8_t v___x_177_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_sub(v___x_168_, v___x_170_);
v___x_177_ = lean_nat_dec_le(v___x_162_, v___x_171_);
if (v___x_177_ == 0)
{
lean_inc(v___x_171_);
v___y_173_ = v___x_171_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___x_162_;
goto v___jp_172_;
}
v___jp_172_:
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_le(v___y_173_, v___x_171_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v___x_171_);
lean_inc(v___y_173_);
v___x_175_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_167_, v___y_173_, v___y_173_);
lean_dec(v___y_173_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_167_, v___y_173_, v___x_171_);
lean_dec(v___x_171_);
return v___x_176_;
}
}
}
else
{
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed(lean_object* v_x_178_, lean_object* v_s_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_x_2002__boxed_181_; lean_object* v_res_182_; 
v_x_2002__boxed_181_ = lean_unbox(v_x_180_);
v_res_182_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(v_x_178_, v_s_179_, v_x_2002__boxed_181_);
lean_dec(v_s_179_);
lean_dec_ref(v_x_178_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed(lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(v_x_185_);
lean_dec(v_x_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(lean_object* v_table_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; size_t v_sz_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0));
v___x_190_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_189_, v_table_187_);
v_sz_191_ = lean_array_size(v___x_190_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_191_, v___x_192_, v___x_190_);
v___x_194_ = lean_array_get_size(v___x_193_);
v___x_195_ = lean_nat_dec_eq(v___x_194_, v___x_188_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___y_199_; uint8_t v___x_203_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_sub(v___x_194_, v___x_196_);
v___x_203_ = lean_nat_dec_le(v___x_188_, v___x_197_);
if (v___x_203_ == 0)
{
lean_inc(v___x_197_);
v___y_199_ = v___x_197_;
goto v___jp_198_;
}
else
{
v___y_199_ = v___x_188_;
goto v___jp_198_;
}
v___jp_198_:
{
uint8_t v___x_200_; 
v___x_200_ = lean_nat_dec_le(v___y_199_, v___x_197_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v___x_197_);
lean_inc(v___y_199_);
v___x_201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_193_, v___y_199_, v___y_199_);
lean_dec(v___y_199_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_193_, v___y_199_, v___x_197_);
lean_dec(v___x_197_);
return v___x_202_;
}
}
}
else
{
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed(lean_object* v_table_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(v_table_204_);
lean_dec(v_table_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(lean_object* v___x_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed(lean_object* v___x_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(v___x_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(lean_object* v___x_212_, lean_object* v_x_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_212_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed(lean_object* v___x_217_, lean_object* v_x_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(v___x_217_, v_x_218_, v___y_219_);
lean_dec_ref(v___y_219_);
lean_dec_ref(v_x_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11));
v___x_251_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___boxed(lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0(lean_object* v_init_254_, lean_object* v_t_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_254_, v_t_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(lean_object* v_init_257_, lean_object* v_t_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_257_, v_t_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1___boxed(lean_object* v_init_260_, lean_object* v_t_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(v_init_260_, v_t_261_);
lean_dec(v_t_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(lean_object* v_n_263_, lean_object* v_as_264_, lean_object* v_lo_265_, lean_object* v_hi_266_, lean_object* v_w_267_, lean_object* v_hlo_268_, lean_object* v_hhi_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_as_264_, v_lo_265_, v_hi_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___boxed(lean_object* v_n_271_, lean_object* v_as_272_, lean_object* v_lo_273_, lean_object* v_hi_274_, lean_object* v_w_275_, lean_object* v_hlo_276_, lean_object* v_hhi_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(v_n_271_, v_as_272_, v_lo_273_, v_hi_274_, v_w_275_, v_hlo_276_, v_hhi_277_);
lean_dec(v_hi_274_);
lean_dec(v_n_271_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(lean_object* v_snd_279_, lean_object* v_k_280_, lean_object* v_t_281_, lean_object* v_hl_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_279_, v_k_280_, v_t_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___boxed(lean_object* v_snd_284_, lean_object* v_k_285_, lean_object* v_t_286_, lean_object* v_hl_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(v_snd_284_, v_k_285_, v_t_286_, v_hl_287_);
lean_dec_ref(v_snd_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(lean_object* v_fst_289_, lean_object* v_old_290_){
_start:
{
lean_object* v___y_292_; 
if (lean_obj_tag(v_old_290_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_NameSet_empty;
v___y_292_ = v___x_295_;
goto v___jp_291_;
}
else
{
lean_object* v_val_296_; 
v_val_296_ = lean_ctor_get(v_old_290_, 0);
lean_inc(v_val_296_);
lean_dec_ref(v_old_290_);
v___y_292_ = v_val_296_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = l_Lean_NameSet_insert(v___y_292_, v_fst_289_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(lean_object* v_fst_297_, lean_object* v_k_298_, lean_object* v_t_299_){
_start:
{
if (lean_obj_tag(v_t_299_) == 0)
{
lean_object* v_size_300_; lean_object* v_k_301_; lean_object* v_v_302_; lean_object* v_l_303_; lean_object* v_r_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_319_; 
v_size_300_ = lean_ctor_get(v_t_299_, 0);
v_k_301_ = lean_ctor_get(v_t_299_, 1);
v_v_302_ = lean_ctor_get(v_t_299_, 2);
v_l_303_ = lean_ctor_get(v_t_299_, 3);
v_r_304_ = lean_ctor_get(v_t_299_, 4);
v_isSharedCheck_319_ = !lean_is_exclusive(v_t_299_);
if (v_isSharedCheck_319_ == 0)
{
v___x_306_ = v_t_299_;
v_isShared_307_ = v_isSharedCheck_319_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_r_304_);
lean_inc(v_l_303_);
lean_inc(v_v_302_);
lean_inc(v_k_301_);
lean_inc(v_size_300_);
lean_dec(v_t_299_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_319_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; 
v___x_308_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_298_, v_k_301_);
switch(v___x_308_)
{
case 0:
{
lean_object* v_impl_309_; lean_object* v___x_310_; 
lean_del_object(v___x_306_);
lean_dec(v_size_300_);
v_impl_309_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_297_, v_k_298_, v_l_303_);
v___x_310_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_301_, v_v_302_, v_impl_309_, v_r_304_);
return v___x_310_;
}
case 1:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_val_313_; lean_object* v___x_315_; 
lean_dec(v_k_301_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v_v_302_);
v___x_312_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_297_, v___x_311_);
v_val_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_313_);
lean_dec(v___x_312_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 2, v_val_313_);
lean_ctor_set(v___x_306_, 1, v_k_298_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_val_313_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_l_303_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_r_304_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
default: 
{
lean_object* v_impl_317_; lean_object* v___x_318_; 
lean_del_object(v___x_306_);
lean_dec(v_size_300_);
v_impl_317_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_297_, v_k_298_, v_r_304_);
v___x_318_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_301_, v_v_302_, v_l_303_, v_impl_317_);
return v___x_318_;
}
}
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_val_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_320_ = lean_box(0);
v___x_321_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_297_, v___x_320_);
v_val_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_322_);
lean_dec(v___x_321_);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_k_298_);
lean_ctor_set(v___x_324_, 2, v_val_322_);
lean_ctor_set(v___x_324_, 3, v_t_299_);
lean_ctor_set(v___x_324_, 4, v_t_299_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(lean_object* v_fst_325_, lean_object* v_as_326_, size_t v_i_327_, size_t v_stop_328_, lean_object* v_b_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_eq(v_i_327_, v_stop_328_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; size_t v___x_333_; size_t v___x_334_; 
v___x_331_ = lean_array_uget_borrowed(v_as_326_, v_i_327_);
lean_inc(v___x_331_);
lean_inc(v_fst_325_);
v___x_332_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_325_, v___x_331_, v_b_329_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_add(v_i_327_, v___x_333_);
v_i_327_ = v___x_334_;
v_b_329_ = v___x_332_;
goto _start;
}
else
{
lean_dec(v_fst_325_);
return v_b_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1___boxed(lean_object* v_fst_336_, lean_object* v_as_337_, lean_object* v_i_338_, lean_object* v_stop_339_, lean_object* v_b_340_){
_start:
{
size_t v_i_boxed_341_; size_t v_stop_boxed_342_; lean_object* v_res_343_; 
v_i_boxed_341_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_stop_boxed_342_ = lean_unbox_usize(v_stop_339_);
lean_dec(v_stop_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_336_, v_as_337_, v_i_boxed_341_, v_stop_boxed_342_, v_b_340_);
lean_dec_ref(v_as_337_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0(lean_object* v_table_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_fst_346_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_fst_346_);
v_snd_347_ = lean_ctor_get(v_x_345_, 1);
lean_inc(v_snd_347_);
lean_dec_ref(v_x_345_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_array_get_size(v_snd_347_);
v___x_350_ = lean_nat_dec_lt(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec(v_snd_347_);
lean_dec(v_fst_346_);
return v_table_344_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = lean_nat_dec_le(v___x_349_, v___x_349_);
if (v___x_351_ == 0)
{
if (v___x_350_ == 0)
{
lean_dec(v_snd_347_);
lean_dec(v_fst_346_);
return v_table_344_;
}
else
{
size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_349_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_346_, v_snd_347_, v___x_352_, v___x_353_, v_table_344_);
lean_dec(v_snd_347_);
return v___x_354_;
}
}
else
{
size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((size_t)0ULL);
v___x_356_ = lean_usize_of_nat(v___x_349_);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_346_, v_snd_347_, v___x_355_, v___x_356_, v_table_344_);
lean_dec(v_snd_347_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting(){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4));
v___x_378_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object* v_fst_381_, lean_object* v_k_382_, lean_object* v_t_383_, lean_object* v_hl_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_381_, v_k_382_, v_t_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t v_sz_386_, size_t v_i_387_, lean_object* v_bs_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_389_ == 0)
{
return v_bs_388_;
}
else
{
lean_object* v_v_390_; lean_object* v___x_391_; lean_object* v_bs_x27_392_; lean_object* v___x_393_; size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v_v_390_ = lean_array_uget(v_bs_388_, v_i_387_);
v___x_391_ = lean_unsigned_to_nat(0u);
v_bs_x27_392_ = lean_array_uset(v_bs_388_, v_i_387_, v___x_391_);
v___x_393_ = l_Lean_Syntax_getId(v_v_390_);
lean_dec(v_v_390_);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_add(v_i_387_, v___x_394_);
v___x_396_ = lean_array_uset(v_bs_x27_392_, v_i_387_, v___x_393_);
v_i_387_ = v___x_395_;
v_bs_388_ = v___x_396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_398_, lean_object* v_i_399_, lean_object* v_bs_400_){
_start:
{
size_t v_sz_boxed_401_; size_t v_i_boxed_402_; lean_object* v_res_403_; 
v_sz_boxed_401_ = lean_unbox_usize(v_sz_398_);
lean_dec(v_sz_398_);
v_i_boxed_402_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_boxed_401_, v_i_boxed_402_, v_bs_400_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
lean_ctor_set(v___x_409_, 3, v___x_407_);
lean_ctor_set(v___x_409_, 4, v___x_407_);
lean_ctor_set(v___x_409_, 5, v___x_407_);
lean_ctor_set(v___x_409_, 6, v___x_407_);
lean_ctor_set(v___x_409_, 7, v___x_407_);
lean_ctor_set(v___x_409_, 8, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(32u);
v___x_411_ = lean_mk_empty_array_with_capacity(v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_413_ = ((size_t)5ULL);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_unsigned_to_nat(32u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
v___x_417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_418_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___x_414_);
lean_ctor_set(v___x_418_, 3, v___x_414_);
lean_ctor_set_usize(v___x_418_, 4, v___x_413_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_box(1);
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v_env_428_; lean_object* v_options_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_427_ = lean_st_ref_get(v___y_425_);
v_env_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_env_428_);
lean_dec(v___x_427_);
v_options_429_ = lean_ctor_get(v___y_424_, 2);
v___x_430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_429_);
v___x_432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_432_, 0, v_env_428_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set(v___x_432_, 3, v_options_429_);
v___x_433_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_msgData_423_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_ref_444_; lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_ref_444_ = lean_ctor_get(v___y_441_, 5);
v___x_445_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msg_440_, v___y_441_, v___y_442_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_inc(v_ref_444_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v_ref_444_);
lean_ctor_set(v___x_450_, 1, v_a_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 1);
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object* v_name_472_, uint8_t v_kind_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___y_483_; 
v___x_477_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_478_ = l_Lean_MessageData_ofName(v_name_472_);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
switch(v_kind_473_)
{
case 0:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6));
v___y_483_ = v___x_490_;
goto v___jp_482_;
}
case 1:
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7));
v___y_483_ = v___x_491_;
goto v___jp_482_;
}
default: 
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8));
v___y_483_ = v___x_492_;
goto v___jp_482_;
}
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___y_483_);
v___x_485_ = l_Lean_MessageData_ofFormat(v___x_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_481_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_488_, v___y_474_, v___y_475_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_name_493_, lean_object* v_kind_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
uint8_t v_kind_boxed_498_; lean_object* v_res_499_; 
v_kind_boxed_498_ = lean_unbox(v_kind_494_);
v_res_499_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_493_, v_kind_boxed_498_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_499_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_500_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_510_ = l_Lean_stringToMessageData(v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v_decl_520_, lean_object* v_stx_521_, uint8_t v_kind_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v_altSyntaxIds_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_587_; lean_object* v___y_588_; uint8_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 0;
v___x_665_ = l_Lean_instBEqAttributeKind_beq(v_kind_522_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec(v_stx_521_);
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___x_666_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v___x_519_, v_kind_522_, v___y_523_, v___y_524_);
return v___x_666_;
}
else
{
lean_dec(v___x_519_);
goto v___jp_603_;
}
v___jp_526_:
{
lean_object* v___x_529_; lean_object* v_toEnvExtension_530_; lean_object* v_env_531_; lean_object* v_nextMacroScope_532_; lean_object* v_ngen_533_; lean_object* v_auxDeclNGen_534_; lean_object* v_traceState_535_; lean_object* v_messages_536_; lean_object* v_infoState_537_; lean_object* v_snapshotTasks_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_577_; 
v___x_529_ = lean_st_ref_take(v___y_528_);
v_toEnvExtension_530_ = lean_ctor_get(v_a_515_, 0);
v_env_531_ = lean_ctor_get(v___x_529_, 0);
v_nextMacroScope_532_ = lean_ctor_get(v___x_529_, 1);
v_ngen_533_ = lean_ctor_get(v___x_529_, 2);
v_auxDeclNGen_534_ = lean_ctor_get(v___x_529_, 3);
v_traceState_535_ = lean_ctor_get(v___x_529_, 4);
v_messages_536_ = lean_ctor_get(v___x_529_, 6);
v_infoState_537_ = lean_ctor_get(v___x_529_, 7);
v_snapshotTasks_538_ = lean_ctor_get(v___x_529_, 8);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_529_, 5);
lean_dec(v_unused_578_);
v___x_540_ = v___x_529_;
v_isShared_541_ = v_isSharedCheck_577_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snapshotTasks_538_);
lean_inc(v_infoState_537_);
lean_inc(v_messages_536_);
lean_inc(v_traceState_535_);
lean_inc(v_auxDeclNGen_534_);
lean_inc(v_ngen_533_);
lean_inc(v_nextMacroScope_532_);
lean_inc(v_env_531_);
lean_dec(v___x_529_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_577_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_asyncMode_542_; size_t v_sz_543_; size_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v_asyncMode_542_ = lean_ctor_get(v_toEnvExtension_530_, 2);
lean_inc(v_asyncMode_542_);
v_sz_543_ = lean_array_size(v___y_527_);
v___x_544_ = ((size_t)0ULL);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_543_, v___x_544_, v___y_527_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_decl_520_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_box(0);
lean_inc_ref(v___x_546_);
v___x_548_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_515_, v_env_531_, v___x_546_, v_asyncMode_542_, v___x_547_);
lean_dec(v_asyncMode_542_);
v___x_549_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 5, v___x_549_);
lean_ctor_set(v___x_540_, 0, v___x_548_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_nextMacroScope_532_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_ngen_533_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_auxDeclNGen_534_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_traceState_535_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_messages_536_);
lean_ctor_set(v_reuseFailAlloc_576_, 7, v_infoState_537_);
lean_ctor_set(v_reuseFailAlloc_576_, 8, v_snapshotTasks_538_);
v___x_551_ = v_reuseFailAlloc_576_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_toEnvExtension_554_; lean_object* v_env_555_; lean_object* v_nextMacroScope_556_; lean_object* v_ngen_557_; lean_object* v_auxDeclNGen_558_; lean_object* v_traceState_559_; lean_object* v_messages_560_; lean_object* v_infoState_561_; lean_object* v_snapshotTasks_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_574_; 
v___x_552_ = lean_st_ref_set(v___y_528_, v___x_551_);
v___x_553_ = lean_st_ref_take(v___y_528_);
v_toEnvExtension_554_ = lean_ctor_get(v_a_516_, 0);
v_env_555_ = lean_ctor_get(v___x_553_, 0);
v_nextMacroScope_556_ = lean_ctor_get(v___x_553_, 1);
v_ngen_557_ = lean_ctor_get(v___x_553_, 2);
v_auxDeclNGen_558_ = lean_ctor_get(v___x_553_, 3);
v_traceState_559_ = lean_ctor_get(v___x_553_, 4);
v_messages_560_ = lean_ctor_get(v___x_553_, 6);
v_infoState_561_ = lean_ctor_get(v___x_553_, 7);
v_snapshotTasks_562_ = lean_ctor_get(v___x_553_, 8);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v___x_553_, 5);
lean_dec(v_unused_575_);
v___x_564_ = v___x_553_;
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snapshotTasks_562_);
lean_inc(v_infoState_561_);
lean_inc(v_messages_560_);
lean_inc(v_traceState_559_);
lean_inc(v_auxDeclNGen_558_);
lean_inc(v_ngen_557_);
lean_inc(v_nextMacroScope_556_);
lean_inc(v_env_555_);
lean_dec(v___x_553_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_asyncMode_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v_asyncMode_566_ = lean_ctor_get(v_toEnvExtension_554_, 2);
lean_inc(v_asyncMode_566_);
v___x_567_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_516_, v_env_555_, v___x_546_, v_asyncMode_566_, v___x_547_);
lean_dec(v_asyncMode_566_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 5, v___x_549_);
lean_ctor_set(v___x_564_, 0, v___x_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_nextMacroScope_556_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_ngen_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_auxDeclNGen_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_traceState_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_messages_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_infoState_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 8, v_snapshotTasks_562_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_st_ref_set(v___y_528_, v___x_569_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
}
}
v___jp_579_:
{
uint8_t v___x_583_; 
v___x_583_ = l_Lean_isPrivateName(v_decl_520_);
if (v___x_583_ == 0)
{
v___y_527_ = v_altSyntaxIds_580_;
v___y_528_ = v___y_582_;
goto v___jp_526_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v_altSyntaxIds_580_);
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___x_584_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_585_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_584_, v___y_581_, v___y_582_);
return v___x_585_;
}
}
v___jp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v___x_589_ = lean_obj_once(&l_Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = l_Lean_Syntax_instRepr_repr(v_stx_521_, v___x_590_);
v___x_592_ = l_Lean_MessageData_ofFormat(v___x_591_);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_589_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_593_, v___y_587_, v___y_588_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
v___jp_603_:
{
if (lean_obj_tag(v_stx_521_) == 1)
{
lean_object* v_kind_604_; 
v_kind_604_ = lean_ctor_get(v_stx_521_, 1);
if (lean_obj_tag(v_kind_604_) == 1)
{
lean_object* v_pre_605_; 
v_pre_605_ = lean_ctor_get(v_kind_604_, 0);
if (lean_obj_tag(v_pre_605_) == 1)
{
lean_object* v_pre_606_; 
v_pre_606_ = lean_ctor_get(v_pre_605_, 0);
switch(lean_obj_tag(v_pre_606_))
{
case 0:
{
lean_object* v_args_607_; lean_object* v_str_608_; lean_object* v_str_609_; uint8_t v___x_610_; 
v_args_607_ = lean_ctor_get(v_stx_521_, 2);
v_str_608_ = lean_ctor_get(v_kind_604_, 1);
v_str_609_ = lean_ctor_get(v_pre_605_, 1);
v___x_610_ = lean_string_dec_eq(v_str_609_, v___x_517_);
if (v___x_610_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_string_dec_eq(v_str_608_, v___x_518_);
if (v___x_611_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_get_size(v_args_607_);
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_nat_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_fget_borrowed(v_args_607_, v___x_615_);
if (lean_obj_tag(v___x_616_) == 2)
{
lean_object* v_val_617_; uint8_t v___x_618_; 
v_val_617_ = lean_ctor_get(v___x_616_, 1);
v___x_618_ = lean_string_dec_eq(v_val_617_, v___x_518_);
if (v___x_618_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_array_fget_borrowed(v_args_607_, v___x_619_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_kind_621_; 
v_kind_621_ = lean_ctor_get(v___x_620_, 1);
if (lean_obj_tag(v_kind_621_) == 1)
{
lean_object* v_pre_622_; 
v_pre_622_ = lean_ctor_get(v_kind_621_, 0);
if (lean_obj_tag(v_pre_622_) == 0)
{
lean_object* v_args_623_; lean_object* v_str_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_args_623_ = lean_ctor_get(v___x_620_, 2);
v_str_624_ = lean_ctor_get(v_kind_621_, 1);
v___x_625_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_626_ = lean_string_dec_eq(v_str_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_inc_ref(v_args_623_);
lean_dec_ref(v_stx_521_);
v_altSyntaxIds_580_ = v_args_623_;
v___y_581_ = v___y_523_;
v___y_582_ = v___y_524_;
goto v___jp_579_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
}
}
}
case 1:
{
lean_object* v_pre_627_; 
v_pre_627_ = lean_ctor_get(v_pre_606_, 0);
if (lean_obj_tag(v_pre_627_) == 1)
{
lean_object* v_pre_628_; 
v_pre_628_ = lean_ctor_get(v_pre_627_, 0);
if (lean_obj_tag(v_pre_628_) == 0)
{
lean_object* v_args_629_; lean_object* v_str_630_; lean_object* v_str_631_; lean_object* v_str_632_; lean_object* v_str_633_; uint8_t v___x_634_; 
v_args_629_ = lean_ctor_get(v_stx_521_, 2);
v_str_630_ = lean_ctor_get(v_kind_604_, 1);
v_str_631_ = lean_ctor_get(v_pre_605_, 1);
v_str_632_ = lean_ctor_get(v_pre_606_, 1);
v_str_633_ = lean_ctor_get(v_pre_627_, 1);
v___x_634_ = lean_string_dec_eq(v_str_633_, v___x_517_);
if (v___x_634_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_636_ = lean_string_dec_eq(v_str_632_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_638_ = lean_string_dec_eq(v_str_631_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_640_ = lean_string_dec_eq(v_str_630_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_array_get_size(v_args_629_);
v___x_642_ = lean_unsigned_to_nat(2u);
v___x_643_ = lean_nat_dec_eq(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_array_fget_borrowed(v_args_629_, v___x_644_);
if (lean_obj_tag(v___x_645_) == 3)
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v___x_645_, 2);
if (lean_obj_tag(v_val_646_) == 1)
{
lean_object* v_pre_647_; 
v_pre_647_ = lean_ctor_get(v_val_646_, 0);
if (lean_obj_tag(v_pre_647_) == 0)
{
lean_object* v_preresolved_648_; lean_object* v_str_649_; uint8_t v___x_650_; 
v_preresolved_648_ = lean_ctor_get(v___x_645_, 3);
v_str_649_ = lean_ctor_get(v_val_646_, 1);
v___x_650_ = lean_string_dec_eq(v_str_649_, v___x_518_);
if (v___x_650_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
if (lean_obj_tag(v_preresolved_648_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_array_fget_borrowed(v_args_629_, v___x_651_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_kind_653_; 
v_kind_653_ = lean_ctor_get(v___x_652_, 1);
if (lean_obj_tag(v_kind_653_) == 1)
{
lean_object* v_pre_654_; 
v_pre_654_ = lean_ctor_get(v_kind_653_, 0);
if (lean_obj_tag(v_pre_654_) == 0)
{
lean_object* v_args_655_; lean_object* v_str_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_args_655_ = lean_ctor_get(v___x_652_, 2);
v_str_656_ = lean_ctor_get(v_kind_653_, 1);
v___x_657_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_658_ = lean_string_dec_eq(v_str_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_array_get_size(v_args_655_);
v___x_660_ = lean_nat_dec_eq(v___x_659_, v___x_651_);
if (v___x_660_ == 0)
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_inc_ref(v_args_655_);
lean_dec_ref(v_stx_521_);
v___x_661_ = lean_array_fget(v_args_655_, v___x_644_);
lean_dec_ref(v_args_655_);
v___x_662_ = lean_mk_empty_array_with_capacity(v___x_651_);
v___x_663_ = lean_array_push(v___x_662_, v___x_661_);
v_altSyntaxIds_580_ = v___x_663_;
v___y_581_ = v___y_523_;
v___y_582_ = v___y_524_;
goto v___jp_579_;
}
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
default: 
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_decl_520_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_a_515_);
v___y_587_ = v___y_523_;
v___y_588_ = v___y_524_;
goto v___jp_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_decl_672_, lean_object* v_stx_673_, lean_object* v_kind_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint8_t v_kind_boxed_678_; lean_object* v_res_679_; 
v_kind_boxed_678_ = lean_unbox(v_kind_674_);
v_res_679_ = l_Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v_a_667_, v_a_668_, v___x_669_, v___x_670_, v___x_671_, v_decl_672_, v_stx_673_, v_kind_boxed_678_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
return v_res_679_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v___x_686_, lean_object* v_decl_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_691_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_692_ = l_Lean_MessageData_ofName(v___x_686_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_695_, v___y_688_, v___y_689_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v___x_697_, lean_object* v_decl_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v___x_697_, v_decl_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v_decl_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
v___x_721_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4));
v___x_724_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_725_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
lean_inc(v_a_722_);
lean_inc(v_a_720_);
v___f_726_ = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_726_, 0, v_a_720_);
lean_closure_set(v___f_726_, 1, v_a_722_);
lean_closure_set(v___f_726_, 2, v___x_723_);
lean_closure_set(v___f_726_, 3, v___x_724_);
lean_closure_set(v___f_726_, 4, v___x_725_);
v___f_727_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_728_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___f_726_);
lean_ctor_set(v___x_729_, 2, v___f_727_);
v___x_730_ = l_Lean_registerBuiltinAttribute(v___x_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_730_, 0);
lean_dec(v_unused_739_);
v___x_732_ = v___x_730_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_dec(v___x_730_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_a_720_);
lean_ctor_set(v___x_734_, 1, v_a_722_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_722_);
lean_dec(v_a_720_);
v_a_740_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_730_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_730_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_a_720_);
v_a_748_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_721_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_721_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
v_a_756_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_719_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_719_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_766_, lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_767_, v___y_768_, v___y_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_772_, lean_object* v_msg_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(v_00_u03b1_772_, v_msg_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b1_778_, lean_object* v_name_779_, uint8_t v_kind_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_779_, v_kind_780_, v___y_781_, v___y_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b1_785_, lean_object* v_name_786_, lean_object* v_kind_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_kind_boxed_791_; lean_object* v_res_792_; 
v_kind_boxed_791_ = lean_unbox(v_kind_787_);
v_res_792_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(v_00_u03b1_785_, v_name_786_, v_kind_boxed_791_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1(lean_object* v_incorrectName_815_, lean_object* v___f_816_, lean_object* v___f_817_, lean_object* v_x1_818_, lean_object* v_x2_819_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_array_get_size(v_x2_819_);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_dec_ref(v___f_817_);
lean_dec_ref(v___f_816_);
lean_dec(v_incorrectName_815_);
return v_x1_818_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_sub(v___x_821_, v___x_823_);
v___x_825_ = lean_nat_dec_le(v___x_820_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v___x_824_);
lean_dec_ref(v___f_817_);
lean_dec_ref(v___f_816_);
lean_dec(v_incorrectName_815_);
return v_x1_818_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_incorrectName_815_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_829_ = l_Array_binSearchAux___redArg(v___f_816_, v___x_828_, v_x2_819_, v___x_827_, v___x_820_, v___x_824_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec_ref(v___f_817_);
return v_x1_818_;
}
else
{
lean_object* v_val_830_; lean_object* v_snd_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_val_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_830_);
lean_dec_ref(v___x_829_);
v_snd_831_ = lean_ctor_get(v_val_830_, 1);
lean_inc(v_snd_831_);
lean_dec(v_val_830_);
v___x_832_ = lean_array_get_size(v_snd_831_);
v___x_833_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_834_ = lean_nat_dec_lt(v___x_820_, v___x_832_);
if (v___x_834_ == 0)
{
lean_dec(v_snd_831_);
lean_dec_ref(v___f_817_);
return v_x1_818_;
}
else
{
uint8_t v___x_835_; 
v___x_835_ = lean_nat_dec_le(v___x_832_, v___x_832_);
if (v___x_835_ == 0)
{
if (v___x_834_ == 0)
{
lean_dec(v_snd_831_);
lean_dec_ref(v___f_817_);
return v_x1_818_;
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_832_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_833_, v___f_817_, v_snd_831_, v___x_836_, v___x_837_, v_x1_818_);
return v___x_838_;
}
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_of_nat(v___x_832_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_833_, v___f_817_, v_snd_831_, v___x_839_, v___x_840_, v_x1_818_);
return v___x_841_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1___boxed(lean_object* v_incorrectName_842_, lean_object* v___f_843_, lean_object* v___f_844_, lean_object* v_x1_845_, lean_object* v_x2_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_getSuggestions___redArg___lam__1(v_incorrectName_842_, v___f_843_, v___f_844_, v_x1_845_, v_x2_846_);
lean_dec_ref(v_x2_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0(lean_object* v___x_848_, lean_object* v_toPure_849_, lean_object* v___f_850_, lean_object* v_incorrectName_851_, lean_object* v_env_852_){
_start:
{
lean_object* v___x_853_; lean_object* v_snd_854_; lean_object* v_toEnvExtension_855_; lean_object* v_asyncMode_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_importedEntries_859_; lean_object* v_state_860_; lean_object* v___y_862_; lean_object* v___x_878_; 
v___x_853_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_854_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_snd_854_);
v_toEnvExtension_855_ = lean_ctor_get(v_snd_854_, 0);
lean_inc_ref(v_toEnvExtension_855_);
lean_dec(v_snd_854_);
v_asyncMode_856_ = lean_ctor_get(v_toEnvExtension_855_, 2);
lean_inc(v_asyncMode_856_);
v___x_857_ = lean_box(0);
v___x_858_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_848_, v_toEnvExtension_855_, v_env_852_, v_asyncMode_856_, v___x_857_);
lean_dec(v_asyncMode_856_);
lean_dec_ref(v_toEnvExtension_855_);
v_importedEntries_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_ref(v_importedEntries_859_);
v_state_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_state_860_);
lean_dec(v___x_858_);
v___x_878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_860_, v_incorrectName_851_);
lean_dec(v_state_860_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_NameSet_empty;
v___y_862_ = v___x_879_;
goto v___jp_861_;
}
else
{
lean_object* v_val_880_; 
v_val_880_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_val_880_);
lean_dec_ref(v___x_878_);
v___y_862_ = v_val_880_;
goto v___jp_861_;
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_array_get_size(v_importedEntries_859_);
v___x_865_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_866_ = lean_nat_dec_lt(v___x_863_, v___x_864_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_dec_ref(v_importedEntries_859_);
lean_dec_ref(v___f_850_);
v___x_867_ = lean_apply_2(v_toPure_849_, lean_box(0), v___y_862_);
return v___x_867_;
}
else
{
uint8_t v___x_868_; 
v___x_868_ = lean_nat_dec_le(v___x_864_, v___x_864_);
if (v___x_868_ == 0)
{
if (v___x_866_ == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v_importedEntries_859_);
lean_dec_ref(v___f_850_);
v___x_869_ = lean_apply_2(v_toPure_849_, lean_box(0), v___y_862_);
return v___x_869_;
}
else
{
size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_864_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_865_, v___f_850_, v_importedEntries_859_, v___x_870_, v___x_871_, v___y_862_);
v___x_873_ = lean_apply_2(v_toPure_849_, lean_box(0), v___x_872_);
return v___x_873_;
}
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_864_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_865_, v___f_850_, v_importedEntries_859_, v___x_874_, v___x_875_, v___y_862_);
v___x_877_ = lean_apply_2(v_toPure_849_, lean_box(0), v___x_876_);
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0___boxed(lean_object* v___x_881_, lean_object* v_toPure_882_, lean_object* v___f_883_, lean_object* v_incorrectName_884_, lean_object* v_env_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_getSuggestions___redArg___lam__0(v___x_881_, v_toPure_882_, v___f_883_, v_incorrectName_884_, v_env_885_);
lean_dec(v_incorrectName_884_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_getSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_box(1);
v___x_889_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg(lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_incorrectName_892_){
_start:
{
lean_object* v_toApplicative_893_; lean_object* v_toBind_894_; lean_object* v_getEnv_895_; lean_object* v_toPure_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v_toApplicative_893_ = lean_ctor_get(v_inst_890_, 0);
lean_inc_ref(v_toApplicative_893_);
v_toBind_894_ = lean_ctor_get(v_inst_890_, 1);
lean_inc(v_toBind_894_);
lean_dec_ref(v_inst_890_);
v_getEnv_895_ = lean_ctor_get(v_inst_891_, 0);
lean_inc(v_getEnv_895_);
lean_dec_ref(v_inst_891_);
v_toPure_896_ = lean_ctor_get(v_toApplicative_893_, 1);
lean_inc(v_toPure_896_);
lean_dec_ref(v_toApplicative_893_);
v___f_897_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___closed__0));
v___f_898_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
lean_inc(v_incorrectName_892_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_899_, 0, v_incorrectName_892_);
lean_closure_set(v___f_899_, 1, v___f_897_);
lean_closure_set(v___f_899_, 2, v___f_898_);
v___x_900_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__1, &l_Lean_getSuggestions___redArg___closed__1_once, _init_l_Lean_getSuggestions___redArg___closed__1);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_901_, 0, v___x_900_);
lean_closure_set(v___f_901_, 1, v_toPure_896_);
lean_closure_set(v___f_901_, 2, v___f_899_);
lean_closure_set(v___f_901_, 3, v_incorrectName_892_);
v___x_902_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v_getEnv_895_, v___f_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions(lean_object* v_m_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_incorrectName_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_getSuggestions___redArg(v_inst_904_, v_inst_905_, v_incorrectName_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1(lean_object* v_trueName_908_, lean_object* v___f_909_, lean_object* v___f_910_, lean_object* v_x1_911_, lean_object* v_x2_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_array_get_size(v_x2_912_);
v___x_915_ = lean_nat_dec_lt(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_dec_ref(v___f_910_);
lean_dec_ref(v___f_909_);
lean_dec(v_trueName_908_);
return v_x1_911_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_sub(v___x_914_, v___x_916_);
v___x_918_ = lean_nat_dec_le(v___x_913_, v___x_917_);
if (v___x_918_ == 0)
{
lean_dec(v___x_917_);
lean_dec_ref(v___f_910_);
lean_dec_ref(v___f_909_);
lean_dec(v_trueName_908_);
return v_x1_911_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_919_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_trueName_908_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_922_ = l_Array_binSearchAux___redArg(v___f_909_, v___x_921_, v_x2_912_, v___x_920_, v___x_913_, v___x_917_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref(v___f_910_);
return v_x1_911_;
}
else
{
lean_object* v_val_923_; lean_object* v_snd_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_val_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_val_923_);
lean_dec_ref(v___x_922_);
v_snd_924_ = lean_ctor_get(v_val_923_, 1);
lean_inc(v_snd_924_);
lean_dec(v_val_923_);
v___x_925_ = lean_array_get_size(v_snd_924_);
v___x_926_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_927_ = lean_nat_dec_lt(v___x_913_, v___x_925_);
if (v___x_927_ == 0)
{
lean_dec(v_snd_924_);
lean_dec_ref(v___f_910_);
return v_x1_911_;
}
else
{
uint8_t v___x_928_; 
v___x_928_ = lean_nat_dec_le(v___x_925_, v___x_925_);
if (v___x_928_ == 0)
{
if (v___x_927_ == 0)
{
lean_dec(v_snd_924_);
lean_dec_ref(v___f_910_);
return v_x1_911_;
}
else
{
size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___x_929_ = ((size_t)0ULL);
v___x_930_ = lean_usize_of_nat(v___x_925_);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_926_, v___f_910_, v_snd_924_, v___x_929_, v___x_930_, v_x1_911_);
return v___x_931_;
}
}
else
{
size_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((size_t)0ULL);
v___x_933_ = lean_usize_of_nat(v___x_925_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_926_, v___f_910_, v_snd_924_, v___x_932_, v___x_933_, v_x1_911_);
return v___x_934_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1___boxed(lean_object* v_trueName_935_, lean_object* v___f_936_, lean_object* v___f_937_, lean_object* v_x1_938_, lean_object* v_x2_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_getStoredSuggestions___redArg___lam__1(v_trueName_935_, v___f_936_, v___f_937_, v_x1_938_, v_x2_939_);
lean_dec_ref(v_x2_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0(lean_object* v___x_941_, lean_object* v_toPure_942_, lean_object* v___f_943_, lean_object* v_trueName_944_, lean_object* v_env_945_){
_start:
{
lean_object* v___x_946_; lean_object* v_fst_947_; lean_object* v_toEnvExtension_948_; lean_object* v_asyncMode_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_importedEntries_952_; lean_object* v_state_953_; lean_object* v___y_955_; lean_object* v___x_971_; 
v___x_946_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_fst_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_fst_947_);
v_toEnvExtension_948_ = lean_ctor_get(v_fst_947_, 0);
lean_inc_ref(v_toEnvExtension_948_);
lean_dec(v_fst_947_);
v_asyncMode_949_ = lean_ctor_get(v_toEnvExtension_948_, 2);
lean_inc(v_asyncMode_949_);
v___x_950_ = lean_box(0);
v___x_951_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_941_, v_toEnvExtension_948_, v_env_945_, v_asyncMode_949_, v___x_950_);
lean_dec(v_asyncMode_949_);
lean_dec_ref(v_toEnvExtension_948_);
v_importedEntries_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_importedEntries_952_);
v_state_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_state_953_);
lean_dec(v___x_951_);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_953_, v_trueName_944_);
lean_dec(v_state_953_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_NameSet_empty;
v___y_955_ = v___x_972_;
goto v___jp_954_;
}
else
{
lean_object* v_val_973_; 
v_val_973_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_val_973_);
lean_dec_ref(v___x_971_);
v___y_955_ = v_val_973_;
goto v___jp_954_;
}
v___jp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_importedEntries_952_);
v___x_958_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_959_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v_importedEntries_952_);
lean_dec_ref(v___f_943_);
v___x_960_ = lean_apply_2(v_toPure_942_, lean_box(0), v___y_955_);
return v___x_960_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = lean_nat_dec_le(v___x_957_, v___x_957_);
if (v___x_961_ == 0)
{
if (v___x_959_ == 0)
{
lean_object* v___x_962_; 
lean_dec_ref(v_importedEntries_952_);
lean_dec_ref(v___f_943_);
v___x_962_ = lean_apply_2(v_toPure_942_, lean_box(0), v___y_955_);
return v___x_962_;
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_usize_of_nat(v___x_957_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_958_, v___f_943_, v_importedEntries_952_, v___x_963_, v___x_964_, v___y_955_);
v___x_966_ = lean_apply_2(v_toPure_942_, lean_box(0), v___x_965_);
return v___x_966_;
}
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = ((size_t)0ULL);
v___x_968_ = lean_usize_of_nat(v___x_957_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_958_, v___f_943_, v_importedEntries_952_, v___x_967_, v___x_968_, v___y_955_);
v___x_970_ = lean_apply_2(v_toPure_942_, lean_box(0), v___x_969_);
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0___boxed(lean_object* v___x_974_, lean_object* v_toPure_975_, lean_object* v___f_976_, lean_object* v_trueName_977_, lean_object* v_env_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_getStoredSuggestions___redArg___lam__0(v___x_974_, v_toPure_975_, v___f_976_, v_trueName_977_, v_env_978_);
lean_dec(v_trueName_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg(lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_trueName_982_){
_start:
{
lean_object* v_toApplicative_983_; lean_object* v_toBind_984_; lean_object* v_getEnv_985_; lean_object* v_toPure_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___f_991_; lean_object* v___x_992_; 
v_toApplicative_983_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_983_);
v_toBind_984_ = lean_ctor_get(v_inst_980_, 1);
lean_inc(v_toBind_984_);
lean_dec_ref(v_inst_980_);
v_getEnv_985_ = lean_ctor_get(v_inst_981_, 0);
lean_inc(v_getEnv_985_);
lean_dec_ref(v_inst_981_);
v_toPure_986_ = lean_ctor_get(v_toApplicative_983_, 1);
lean_inc(v_toPure_986_);
lean_dec_ref(v_toApplicative_983_);
v___f_987_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___closed__0));
v___f_988_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
lean_inc(v_trueName_982_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_989_, 0, v_trueName_982_);
lean_closure_set(v___f_989_, 1, v___f_987_);
lean_closure_set(v___f_989_, 2, v___f_988_);
v___x_990_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__1, &l_Lean_getSuggestions___redArg___closed__1_once, _init_l_Lean_getSuggestions___redArg___closed__1);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_991_, 0, v___x_990_);
lean_closure_set(v___f_991_, 1, v_toPure_986_);
lean_closure_set(v___f_991_, 2, v___f_989_);
lean_closure_set(v___f_991_, 3, v_trueName_982_);
v___x_992_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v_getEnv_985_, v___f_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions(lean_object* v_m_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_trueName_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_getStoredSuggestions___redArg(v_inst_994_, v_inst_995_, v_trueName_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object* v_x_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0));
v___x_1001_ = lean_string_append(v___x_1000_, v_x_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object* v_x_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(v_x_1002_);
lean_dec_ref(v_x_1002_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, size_t v_sz_1011_, size_t v_i_1012_, lean_object* v_bs_1013_){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_usize_dec_lt(v_i_1012_, v_sz_1011_);
if (v___x_1014_ == 0)
{
lean_dec(v___x_1010_);
lean_dec(v___x_1009_);
lean_dec_ref(v___x_1008_);
return v_bs_1013_;
}
else
{
lean_object* v_v_1015_; lean_object* v___x_1016_; lean_object* v_bs_x27_1017_; lean_object* v___y_1019_; 
v_v_1015_ = lean_array_uget(v_bs_1013_, v_i_1012_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v_bs_x27_1017_ = lean_array_uset(v_bs_1013_, v_i_1012_, v___x_1016_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_inc(v_v_1015_);
v___y_1019_ = v_v_1015_;
goto v___jp_1018_;
}
else
{
lean_object* v_val_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_val_1037_ = lean_ctor_get(v___x_1007_, 0);
v___x_1038_ = lean_box(0);
lean_inc(v_v_1015_);
v___x_1039_ = l_Lean_Name_replacePrefix(v_v_1015_, v_val_1037_, v___x_1038_);
v___x_1040_ = l_Lean_Options_empty;
lean_inc(v___x_1039_);
lean_inc(v___x_1010_);
lean_inc(v___x_1009_);
lean_inc_ref(v___x_1008_);
v___x_1041_ = l_Lean_ResolveName_resolveGlobalName(v___x_1008_, v___x_1040_, v___x_1009_, v___x_1010_, v___x_1039_);
v___x_1042_ = l_List_lengthTR___redArg(v___x_1041_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_dec_eq(v___x_1042_, v___x_1043_);
lean_dec(v___x_1042_);
if (v___x_1044_ == 0)
{
lean_dec(v___x_1039_);
lean_inc(v_v_1015_);
v___y_1019_ = v_v_1015_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___x_1039_;
goto v___jp_1018_;
}
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_1019_, v___x_1014_);
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1024_ = 0;
v___x_1025_ = l_Lean_MessageData_ofConstName(v_v_1015_, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1023_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1023_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1));
v___x_1030_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1021_);
lean_ctor_set(v___x_1030_, 1, v___x_1022_);
lean_ctor_set(v___x_1030_, 2, v___x_1022_);
lean_ctor_set(v___x_1030_, 3, v___x_1022_);
lean_ctor_set(v___x_1030_, 4, v___x_1028_);
lean_ctor_set(v___x_1030_, 5, v___x_1029_);
v___x_1031_ = 0;
v___x_1032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1022_);
lean_ctor_set(v___x_1032_, 2, v___x_1022_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*3, v___x_1031_);
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1012_, v___x_1033_);
v___x_1035_ = lean_array_uset(v_bs_x27_1017_, v_i_1012_, v___x_1032_);
v_i_1012_ = v___x_1034_;
v_bs_1013_ = v___x_1035_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object* v___x_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_sz_1049_, lean_object* v_i_1050_, lean_object* v_bs_1051_){
_start:
{
size_t v_sz_boxed_1052_; size_t v_i_boxed_1053_; lean_object* v_res_1054_; 
v_sz_boxed_1052_ = lean_unbox_usize(v_sz_1049_);
lean_dec(v_sz_1049_);
v_i_boxed_1053_ = lean_unbox_usize(v_i_1050_);
lean_dec(v_i_1050_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_1045_, v___x_1046_, v___x_1047_, v___x_1048_, v_sz_boxed_1052_, v_i_boxed_1053_, v_bs_1051_);
lean_dec(v___x_1045_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(lean_object* v_msgData_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v_env_1062_; lean_object* v___x_1063_; lean_object* v_mctx_1064_; lean_object* v_lctx_1065_; lean_object* v_options_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1061_ = lean_st_ref_get(v___y_1059_);
v_env_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_env_1062_);
lean_dec(v___x_1061_);
v___x_1063_ = lean_st_ref_get(v___y_1057_);
v_mctx_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_mctx_1064_);
lean_dec(v___x_1063_);
v_lctx_1065_ = lean_ctor_get(v___y_1056_, 2);
v_options_1066_ = lean_ctor_get(v___y_1058_, 2);
lean_inc_ref(v_options_1066_);
lean_inc_ref(v_lctx_1065_);
v___x_1067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1067_, 0, v_env_1062_);
lean_ctor_set(v___x_1067_, 1, v_mctx_1064_);
lean_ctor_set(v___x_1067_, 2, v_lctx_1065_);
lean_ctor_set(v___x_1067_, 3, v_options_1066_);
v___x_1068_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v_msgData_1055_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_box(1);
v___x_1078_ = l_Lean_MessageData_ofFormat(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2));
v___x_1083_ = l_Lean_MessageData_ofFormat(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
if (lean_obj_tag(v_x_1085_) == 0)
{
return v_x_1084_;
}
else
{
lean_object* v_head_1086_; lean_object* v_tail_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1109_; 
v_head_1086_ = lean_ctor_get(v_x_1085_, 0);
v_tail_1087_ = lean_ctor_get(v_x_1085_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1085_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1089_ = v_x_1085_;
v_isShared_1090_ = v_isSharedCheck_1109_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_tail_1087_);
lean_inc(v_head_1086_);
lean_dec(v_x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1109_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_before_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1107_; 
v_before_1091_ = lean_ctor_get(v_head_1086_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_head_1086_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_head_1086_, 1);
lean_dec(v_unused_1108_);
v___x_1093_ = v_head_1086_;
v_isShared_1094_ = v_isSharedCheck_1107_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_before_1091_);
lean_dec(v_head_1086_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1107_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 7);
lean_ctor_set(v___x_1093_, 1, v___x_1095_);
lean_ctor_set(v___x_1093_, 0, v_x_1084_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_x_1084_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 7);
lean_ctor_set(v___x_1089_, 1, v___x_1098_);
lean_ctor_set(v___x_1089_, 0, v___x_1097_);
v___x_1100_ = v___x_1089_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = l_Lean_MessageData_ofSyntax(v_before_1091_);
v___x_1102_ = l_Lean_indentD(v___x_1101_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1100_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v_x_1084_ = v___x_1103_;
v_x_1085_ = v_tail_1087_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(lean_object* v_opts_1110_, lean_object* v_opt_1111_){
_start:
{
lean_object* v_name_1112_; lean_object* v_defValue_1113_; lean_object* v_map_1114_; lean_object* v___x_1115_; 
v_name_1112_ = lean_ctor_get(v_opt_1111_, 0);
v_defValue_1113_ = lean_ctor_get(v_opt_1111_, 1);
v_map_1114_ = lean_ctor_get(v_opts_1110_, 0);
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1114_, v_name_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_unbox(v_defValue_1113_);
return v___x_1116_;
}
else
{
lean_object* v_val_1117_; 
v_val_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1117_);
lean_dec_ref(v___x_1115_);
if (lean_obj_tag(v_val_1117_) == 1)
{
uint8_t v_v_1118_; 
v_v_1118_ = lean_ctor_get_uint8(v_val_1117_, 0);
lean_dec_ref(v_val_1117_);
return v_v_1118_;
}
else
{
uint8_t v___x_1119_; 
lean_dec(v_val_1117_);
v___x_1119_ = lean_unbox(v_defValue_1113_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(lean_object* v_opts_1120_, lean_object* v_opt_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_1120_, v_opt_1121_);
lean_dec_ref(v_opt_1121_);
lean_dec_ref(v_opts_1120_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1));
v___x_1128_ = l_Lean_MessageData_ofFormat(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(lean_object* v_msgData_1129_, lean_object* v_macroStack_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_options_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_options_1133_ = lean_ctor_get(v___y_1131_, 2);
v___x_1134_ = l_Lean_Elab_pp_macroStack;
v___x_1135_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_options_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec(v_macroStack_1130_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_msgData_1129_);
return v___x_1136_;
}
else
{
if (lean_obj_tag(v_macroStack_1130_) == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_msgData_1129_);
return v___x_1137_;
}
else
{
lean_object* v_head_1138_; lean_object* v_after_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1154_; 
v_head_1138_ = lean_ctor_get(v_macroStack_1130_, 0);
lean_inc(v_head_1138_);
v_after_1139_ = lean_ctor_get(v_head_1138_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_head_1138_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_head_1138_, 0);
lean_dec(v_unused_1155_);
v___x_1141_ = v_head_1138_;
v_isShared_1142_ = v_isSharedCheck_1154_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_after_1139_);
lean_dec(v_head_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1154_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 7);
lean_ctor_set(v___x_1141_, 1, v___x_1143_);
lean_ctor_set(v___x_1141_, 0, v_msgData_1129_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_msgData_1129_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_msgData_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1146_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_ofSyntax(v_after_1139_);
v___x_1149_ = l_Lean_indentD(v___x_1148_);
v_msgData_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1150_, 0, v___x_1147_);
lean_ctor_set(v_msgData_1150_, 1, v___x_1149_);
v___x_1151_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(v_msgData_1150_, v_macroStack_1130_);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_1156_, lean_object* v_macroStack_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1156_, v_macroStack_1157_, v___y_1158_);
lean_dec_ref(v___y_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v_a_1171_; lean_object* v_macroStack_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_ref_1169_ = lean_ctor_get(v___y_1166_, 5);
v___x_1170_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msg_1161_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v___x_1170_);
v_macroStack_1172_ = lean_ctor_get(v___y_1162_, 1);
lean_inc(v_macroStack_1172_);
lean_dec_ref(v___y_1162_);
lean_inc(v_macroStack_1172_);
v___x_1173_ = l_Lean_Elab_getBetterRef(v_ref_1169_, v_macroStack_1172_);
v___x_1174_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_a_1171_, v_macroStack_1172_, v___y_1166_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1173_);
lean_ctor_set(v___x_1179_, 1, v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(lean_object* v_ref_1193_, lean_object* v_msg_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_fileName_1202_; lean_object* v_fileMap_1203_; lean_object* v_options_1204_; lean_object* v_currRecDepth_1205_; lean_object* v_maxRecDepth_1206_; lean_object* v_ref_1207_; lean_object* v_currNamespace_1208_; lean_object* v_openDecls_1209_; lean_object* v_initHeartbeats_1210_; lean_object* v_maxHeartbeats_1211_; lean_object* v_quotContext_1212_; lean_object* v_currMacroScope_1213_; uint8_t v_diag_1214_; lean_object* v_cancelTk_x3f_1215_; uint8_t v_suppressElabErrors_1216_; lean_object* v_inheritedTraceOptions_1217_; lean_object* v_ref_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_fileName_1202_ = lean_ctor_get(v___y_1199_, 0);
v_fileMap_1203_ = lean_ctor_get(v___y_1199_, 1);
v_options_1204_ = lean_ctor_get(v___y_1199_, 2);
v_currRecDepth_1205_ = lean_ctor_get(v___y_1199_, 3);
v_maxRecDepth_1206_ = lean_ctor_get(v___y_1199_, 4);
v_ref_1207_ = lean_ctor_get(v___y_1199_, 5);
v_currNamespace_1208_ = lean_ctor_get(v___y_1199_, 6);
v_openDecls_1209_ = lean_ctor_get(v___y_1199_, 7);
v_initHeartbeats_1210_ = lean_ctor_get(v___y_1199_, 8);
v_maxHeartbeats_1211_ = lean_ctor_get(v___y_1199_, 9);
v_quotContext_1212_ = lean_ctor_get(v___y_1199_, 10);
v_currMacroScope_1213_ = lean_ctor_get(v___y_1199_, 11);
v_diag_1214_ = lean_ctor_get_uint8(v___y_1199_, sizeof(void*)*14);
v_cancelTk_x3f_1215_ = lean_ctor_get(v___y_1199_, 12);
v_suppressElabErrors_1216_ = lean_ctor_get_uint8(v___y_1199_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1217_ = lean_ctor_get(v___y_1199_, 13);
v_ref_1218_ = l_Lean_replaceRef(v_ref_1193_, v_ref_1207_);
lean_inc_ref(v_inheritedTraceOptions_1217_);
lean_inc(v_cancelTk_x3f_1215_);
lean_inc(v_currMacroScope_1213_);
lean_inc(v_quotContext_1212_);
lean_inc(v_maxHeartbeats_1211_);
lean_inc(v_initHeartbeats_1210_);
lean_inc(v_openDecls_1209_);
lean_inc(v_currNamespace_1208_);
lean_inc(v_maxRecDepth_1206_);
lean_inc(v_currRecDepth_1205_);
lean_inc_ref(v_options_1204_);
lean_inc_ref(v_fileMap_1203_);
lean_inc_ref(v_fileName_1202_);
v___x_1219_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1219_, 0, v_fileName_1202_);
lean_ctor_set(v___x_1219_, 1, v_fileMap_1203_);
lean_ctor_set(v___x_1219_, 2, v_options_1204_);
lean_ctor_set(v___x_1219_, 3, v_currRecDepth_1205_);
lean_ctor_set(v___x_1219_, 4, v_maxRecDepth_1206_);
lean_ctor_set(v___x_1219_, 5, v_ref_1218_);
lean_ctor_set(v___x_1219_, 6, v_currNamespace_1208_);
lean_ctor_set(v___x_1219_, 7, v_openDecls_1209_);
lean_ctor_set(v___x_1219_, 8, v_initHeartbeats_1210_);
lean_ctor_set(v___x_1219_, 9, v_maxHeartbeats_1211_);
lean_ctor_set(v___x_1219_, 10, v_quotContext_1212_);
lean_ctor_set(v___x_1219_, 11, v_currMacroScope_1213_);
lean_ctor_set(v___x_1219_, 12, v_cancelTk_x3f_1215_);
lean_ctor_set(v___x_1219_, 13, v_inheritedTraceOptions_1217_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*14, v_diag_1214_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*14 + 1, v_suppressElabErrors_1216_);
lean_inc_ref(v___y_1195_);
v___x_1220_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___x_1219_, v___y_1200_);
lean_dec_ref(v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1221_, lean_object* v_msg_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1221_, v_msg_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v_ref_1221_);
return v_res_1230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4));
v___x_1239_ = l_Lean_stringToMessageData(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8));
v___x_1245_ = l_Lean_stringToMessageData(v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12));
v___x_1251_ = l_Lean_stringToMessageData(v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(lean_object* v_msg_1252_, lean_object* v_declHint_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v_env_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_st_ref_get(v___y_1254_);
v_env_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref(v_env_1257_);
lean_dec(v___x_1256_);
v___x_1258_ = l_Lean_Name_isAnonymous(v_declHint_1253_);
if (v___x_1258_ == 0)
{
uint8_t v_isExporting_1259_; 
v_isExporting_1259_ = lean_ctor_get_uint8(v_env_1257_, sizeof(void*)*8);
if (v_isExporting_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref(v_env_1257_);
lean_dec(v_declHint_1253_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_msg_1252_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
lean_inc_ref(v_env_1257_);
v___x_1261_ = l_Lean_Environment_setExporting(v_env_1257_, v___x_1258_);
lean_inc(v_declHint_1253_);
lean_inc_ref(v___x_1261_);
v___x_1262_ = l_Lean_Environment_contains(v___x_1261_, v_declHint_1253_, v_isExporting_1259_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref(v___x_1261_);
lean_dec_ref(v_env_1257_);
lean_dec(v_declHint_1253_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_msg_1252_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_c_1269_; lean_object* v___x_1270_; 
v___x_1264_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1265_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1266_ = l_Lean_Options_empty;
v___x_1267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1261_);
lean_ctor_set(v___x_1267_, 1, v___x_1264_);
lean_ctor_set(v___x_1267_, 2, v___x_1265_);
lean_ctor_set(v___x_1267_, 3, v___x_1266_);
lean_inc(v_declHint_1253_);
v___x_1268_ = l_Lean_MessageData_ofConstName(v_declHint_1253_, v___x_1258_);
v_c_1269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1269_, 0, v___x_1267_);
lean_ctor_set(v_c_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1257_, v_declHint_1253_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec_ref(v_env_1257_);
lean_dec(v_declHint_1253_);
v___x_1271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_c_1269_);
v___x_1273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_MessageData_note(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_msg_1252_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
else
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1313_; 
v_val_1278_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1280_ = v___x_1270_;
v_isShared_1281_ = v_isSharedCheck_1313_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v___x_1270_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1313_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_mod_1285_; uint8_t v___x_1286_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = l_Lean_Environment_header(v_env_1257_);
lean_dec_ref(v_env_1257_);
v___x_1284_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1283_);
v_mod_1285_ = lean_array_get(v___x_1282_, v___x_1284_, v_val_1278_);
lean_dec(v_val_1278_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = l_Lean_isPrivateName(v_declHint_1253_);
lean_dec(v_declHint_1253_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1287_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_c_1269_);
v___x_1289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_MessageData_ofName(v_mod_1285_);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_MessageData_note(v___x_1294_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_msg_1252_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1296_);
v___x_1298_ = v___x_1280_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_c_1269_);
v___x_1302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = l_Lean_MessageData_ofName(v_mod_1285_);
v___x_1305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13);
v___x_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_Lean_MessageData_note(v___x_1307_);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_msg_1252_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1309_);
v___x_1311_ = v___x_1280_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1314_; 
lean_dec_ref(v_env_1257_);
lean_dec(v_declHint_1253_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_msg_1252_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1315_, lean_object* v_declHint_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1315_, v_declHint_1316_, v___y_1317_);
lean_dec(v___y_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(lean_object* v_msg_1320_, lean_object* v_declHint_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1339_; 
v___x_1329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1320_, v_declHint_1321_, v___y_1327_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1334_ = l_Lean_unknownIdentifierMessageTag;
v___x_1335_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v_a_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1335_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(lean_object* v_msg_1340_, lean_object* v_declHint_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1340_, v_declHint_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(lean_object* v_ref_1350_, lean_object* v_msg_1351_, lean_object* v_declHint_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v_a_1361_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1351_, v_declHint_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1350_, v_a_1361_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(lean_object* v_ref_1363_, lean_object* v_msg_1364_, lean_object* v_declHint_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1363_, v_msg_1364_, v_declHint_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v_ref_1363_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object* v_as_1374_, lean_object* v_k_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_m_1380_; lean_object* v_a_1381_; uint8_t v___x_1382_; 
v___x_1378_ = lean_nat_add(v_x_1376_, v_x_1377_);
v___x_1379_ = lean_unsigned_to_nat(1u);
v_m_1380_ = lean_nat_shiftr(v___x_1378_, v___x_1379_);
lean_dec(v___x_1378_);
v_a_1381_ = lean_array_fget_borrowed(v_as_1374_, v_m_1380_);
v___x_1382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_1381_, v_k_1375_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
lean_dec(v_x_1377_);
v___x_1383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_k_1375_, v_a_1381_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec(v_m_1380_);
lean_dec(v_x_1376_);
lean_inc(v_a_1381_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_a_1381_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_nat_dec_eq(v_m_1380_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = lean_nat_sub(v_m_1380_, v___x_1379_);
lean_dec(v_m_1380_);
v___x_1388_ = lean_nat_dec_lt(v___x_1387_, v_x_1376_);
if (v___x_1388_ == 0)
{
v_x_1377_ = v___x_1387_;
goto _start;
}
else
{
lean_object* v___x_1390_; 
lean_dec(v___x_1387_);
lean_dec(v_x_1376_);
v___x_1390_ = lean_box(0);
return v___x_1390_;
}
}
else
{
lean_object* v___x_1391_; 
lean_dec(v_m_1380_);
lean_dec(v_x_1376_);
v___x_1391_ = lean_box(0);
return v___x_1391_;
}
}
}
else
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
lean_dec(v_x_1376_);
v___x_1392_ = lean_nat_add(v_m_1380_, v___x_1379_);
lean_dec(v_m_1380_);
v___x_1393_ = lean_nat_dec_le(v___x_1392_, v_x_1377_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v___x_1392_);
lean_dec(v_x_1377_);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
v_x_1376_ = v___x_1392_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object* v_as_1396_, lean_object* v_k_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1396_, v_k_1397_, v_x_1398_, v_x_1399_);
lean_dec_ref(v_k_1397_);
lean_dec_ref(v_as_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object* v_incorrectName_1401_, lean_object* v_as_1402_, size_t v_i_1403_, size_t v_stop_1404_, lean_object* v_b_1405_){
_start:
{
lean_object* v___y_1407_; uint8_t v___x_1411_; 
v___x_1411_ = lean_usize_dec_eq(v_i_1403_, v_stop_1404_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1412_ = lean_array_uget_borrowed(v_as_1402_, v_i_1403_);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_array_get_size(v___x_1412_);
v___x_1415_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
v___y_1407_ = v_b_1405_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_sub(v___x_1414_, v___x_1416_);
v___x_1418_ = lean_nat_dec_le(v___x_1413_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec(v___x_1417_);
v___y_1407_ = v_b_1405_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
lean_inc(v_incorrectName_1401_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_incorrectName_1401_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v___x_1412_, v___x_1420_, v___x_1413_, v___x_1417_);
lean_dec_ref(v___x_1420_);
if (lean_obj_tag(v___x_1421_) == 0)
{
v___y_1407_ = v_b_1405_;
goto v___jp_1406_;
}
else
{
lean_object* v_val_1422_; lean_object* v_snd_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1422_);
lean_dec_ref(v___x_1421_);
v_snd_1423_ = lean_ctor_get(v_val_1422_, 1);
lean_inc(v_snd_1423_);
lean_dec(v_val_1422_);
v___x_1424_ = lean_array_get_size(v_snd_1423_);
v___x_1425_ = lean_nat_dec_lt(v___x_1413_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_snd_1423_);
v___y_1407_ = v_b_1405_;
goto v___jp_1406_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
if (v___x_1426_ == 0)
{
if (v___x_1425_ == 0)
{
lean_dec(v_snd_1423_);
v___y_1407_ = v_b_1405_;
goto v___jp_1406_;
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1424_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1423_, v___x_1427_, v___x_1428_, v_b_1405_);
lean_dec(v_snd_1423_);
v___y_1407_ = v___x_1429_;
goto v___jp_1406_;
}
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1424_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1423_, v___x_1430_, v___x_1431_, v_b_1405_);
lean_dec(v_snd_1423_);
v___y_1407_ = v___x_1432_;
goto v___jp_1406_;
}
}
}
}
}
}
else
{
lean_dec(v_incorrectName_1401_);
return v_b_1405_;
}
v___jp_1406_:
{
size_t v___x_1408_; size_t v___x_1409_; 
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1403_, v___x_1408_);
v_i_1403_ = v___x_1409_;
v_b_1405_ = v___y_1407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object* v_incorrectName_1433_, lean_object* v_as_1434_, lean_object* v_i_1435_, lean_object* v_stop_1436_, lean_object* v_b_1437_){
_start:
{
size_t v_i_boxed_1438_; size_t v_stop_boxed_1439_; lean_object* v_res_1440_; 
v_i_boxed_1438_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_stop_boxed_1439_ = lean_unbox_usize(v_stop_1436_);
lean_dec(v_stop_1436_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1433_, v_as_1434_, v_i_boxed_1438_, v_stop_boxed_1439_, v_b_1437_);
lean_dec_ref(v_as_1434_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object* v_incorrectName_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_env_1445_; lean_object* v___x_1446_; lean_object* v_snd_1447_; lean_object* v_toEnvExtension_1448_; lean_object* v_asyncMode_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_importedEntries_1453_; lean_object* v_state_1454_; lean_object* v___y_1456_; lean_object* v___x_1471_; 
v___x_1444_ = lean_st_ref_get(v___y_1442_);
v_env_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc_ref(v_env_1445_);
lean_dec(v___x_1444_);
v___x_1446_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_1447_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_snd_1447_);
v_toEnvExtension_1448_ = lean_ctor_get(v_snd_1447_, 0);
lean_inc_ref(v_toEnvExtension_1448_);
lean_dec(v_snd_1447_);
v_asyncMode_1449_ = lean_ctor_get(v_toEnvExtension_1448_, 2);
lean_inc(v_asyncMode_1449_);
v___x_1450_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__1, &l_Lean_getSuggestions___redArg___closed__1_once, _init_l_Lean_getSuggestions___redArg___closed__1);
v___x_1451_ = lean_box(0);
v___x_1452_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1450_, v_toEnvExtension_1448_, v_env_1445_, v_asyncMode_1449_, v___x_1451_);
lean_dec(v_asyncMode_1449_);
lean_dec_ref(v_toEnvExtension_1448_);
v_importedEntries_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_importedEntries_1453_);
v_state_1454_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_state_1454_);
lean_dec(v___x_1452_);
v___x_1471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1454_, v_incorrectName_1441_);
lean_dec(v_state_1454_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_NameSet_empty;
v___y_1456_ = v___x_1472_;
goto v___jp_1455_;
}
else
{
lean_object* v_val_1473_; 
v_val_1473_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_val_1473_);
lean_dec_ref(v___x_1471_);
v___y_1456_ = v_val_1473_;
goto v___jp_1455_;
}
v___jp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_array_get_size(v_importedEntries_1453_);
v___x_1459_ = lean_nat_dec_lt(v___x_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_importedEntries_1453_);
lean_dec(v_incorrectName_1441_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1456_);
return v___x_1460_;
}
else
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_nat_dec_le(v___x_1458_, v___x_1458_);
if (v___x_1461_ == 0)
{
if (v___x_1459_ == 0)
{
lean_object* v___x_1462_; 
lean_dec_ref(v_importedEntries_1453_);
lean_dec(v_incorrectName_1441_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1456_);
return v___x_1462_;
}
else
{
size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = lean_usize_of_nat(v___x_1458_);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1441_, v_importedEntries_1453_, v___x_1463_, v___x_1464_, v___y_1456_);
lean_dec_ref(v_importedEntries_1453_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
else
{
size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1458_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1441_, v_importedEntries_1453_, v___x_1467_, v___x_1468_, v___y_1456_);
lean_dec_ref(v_importedEntries_1453_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object* v_incorrectName_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1474_, v___y_1475_);
lean_dec(v___y_1475_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg(lean_object* v_constName_1496_, lean_object* v_idOrConst_1497_, lean_object* v_declHint_1498_, lean_object* v_ref_x3f_1499_, lean_object* v_extraMsg_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___y_1509_; lean_object* v_hint_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; uint8_t v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1601_; 
lean_inc(v_constName_1496_);
v___x_1577_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_constName_1496_, v_a_1506_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
if (lean_obj_tag(v_a_1578_) == 0)
{
lean_object* v_size_1606_; 
v_size_1606_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_size_1606_);
v___y_1601_ = v_size_1606_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___y_1601_ = v___x_1607_;
goto v___jp_1600_;
}
v___jp_1508_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1517_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1);
v___x_1518_ = l_Lean_stringToMessageData(v_idOrConst_1497_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = 0;
v___x_1523_ = l_Lean_MessageData_ofConstName(v_constName_1496_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1521_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v_extraMsg_1500_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v_hint_1510_);
v___x_1529_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v___y_1509_, v___x_1528_, v_declHint_1498_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1509_);
return v___x_1529_;
}
v___jp_1530_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; size_t v_sz_1545_; size_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1540_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___y_1537_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___y_1539_);
v___x_1543_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v_sz_1545_ = lean_array_size(v___y_1531_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___y_1534_, v___y_1535_, v___y_1532_, v___y_1533_, v_sz_1545_, v___x_1546_, v___y_1531_);
lean_dec(v___y_1534_);
lean_inc(v___y_1536_);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___y_1536_);
v___x_1549_ = lean_box(0);
lean_inc_ref(v_a_1505_);
v___x_1550_ = l_Lean_MessageData_hint(v___x_1544_, v___x_1547_, v___x_1548_, v___x_1549_, v___y_1538_, v_a_1505_, v_a_1506_);
lean_dec_ref(v___x_1547_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___y_1509_ = v___y_1536_;
v_hint_1510_ = v_a_1551_;
v___y_1511_ = v_a_1501_;
v___y_1512_ = v_a_1502_;
v___y_1513_ = v_a_1503_;
v___y_1514_ = v_a_1504_;
v___y_1515_ = v_a_1505_;
v___y_1516_ = v_a_1506_;
goto v___jp_1508_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v___y_1536_);
lean_dec_ref(v_a_1505_);
lean_dec_ref(v_extraMsg_1500_);
lean_dec(v_declHint_1498_);
lean_dec_ref(v_idOrConst_1497_);
lean_dec(v_constName_1496_);
v_a_1552_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1550_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1550_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
v___jp_1560_:
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Lean_Name_isAnonymous(v___y_1566_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9);
v___x_1572_ = l_Lean_MessageData_ofName(v___y_1566_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___y_1531_ = v___y_1561_;
v___y_1532_ = v___y_1562_;
v___y_1533_ = v___y_1563_;
v___y_1534_ = v___y_1564_;
v___y_1535_ = v___y_1565_;
v___y_1536_ = v___y_1567_;
v___y_1537_ = v___y_1569_;
v___y_1538_ = v___y_1568_;
v___y_1539_ = v___x_1575_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1576_; 
lean_dec(v___y_1566_);
v___x_1576_ = l_Lean_MessageData_nil;
v___y_1531_ = v___y_1561_;
v___y_1532_ = v___y_1562_;
v___y_1533_ = v___y_1563_;
v___y_1534_ = v___y_1564_;
v___y_1535_ = v___y_1565_;
v___y_1536_ = v___y_1567_;
v___y_1537_ = v___y_1569_;
v___y_1538_ = v___y_1568_;
v___y_1539_ = v___x_1576_;
goto v___jp_1530_;
}
}
v___jp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = lean_array_get_size(v___y_1580_);
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = lean_nat_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v_env_1586_; lean_object* v_currNamespace_1587_; lean_object* v_openDecls_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1585_ = lean_st_ref_get(v_a_1506_);
v_env_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_env_1586_);
lean_dec(v___x_1585_);
v_currNamespace_1587_ = lean_ctor_get(v_a_1505_, 6);
v_openDecls_1588_ = lean_ctor_get(v_a_1505_, 7);
v___x_1589_ = l_Lean_Syntax_getId(v___y_1581_);
lean_inc(v_constName_1496_);
v___x_1590_ = l_Lean_Name_eraseSuffix_x3f(v_constName_1496_, v___x_1589_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_dec_eq(v___x_1582_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11);
lean_inc(v_openDecls_1588_);
lean_inc(v_currNamespace_1587_);
v___y_1561_ = v___y_1580_;
v___y_1562_ = v_currNamespace_1587_;
v___y_1563_ = v_openDecls_1588_;
v___y_1564_ = v___x_1590_;
v___y_1565_ = v_env_1586_;
v___y_1566_ = v___x_1589_;
v___y_1567_ = v___y_1581_;
v___y_1568_ = v___x_1584_;
v___y_1569_ = v___x_1593_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1594_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1595_ = lean_array_fget_borrowed(v___y_1580_, v___x_1583_);
lean_inc(v___x_1595_);
v___x_1596_ = l_Lean_MessageData_ofConstName(v___x_1595_, v___x_1584_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1594_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1594_);
lean_inc(v_openDecls_1588_);
lean_inc(v_currNamespace_1587_);
v___y_1561_ = v___y_1580_;
v___y_1562_ = v_currNamespace_1587_;
v___y_1563_ = v_openDecls_1588_;
v___y_1564_ = v___x_1590_;
v___y_1565_ = v_env_1586_;
v___y_1566_ = v___x_1589_;
v___y_1567_ = v___y_1581_;
v___y_1568_ = v___x_1584_;
v___y_1569_ = v___x_1598_;
goto v___jp_1560_;
}
}
else
{
lean_object* v___x_1599_; 
lean_dec_ref(v___y_1580_);
v___x_1599_ = l_Lean_MessageData_nil;
v___y_1509_ = v___y_1581_;
v_hint_1510_ = v___x_1599_;
v___y_1511_ = v_a_1501_;
v___y_1512_ = v_a_1502_;
v___y_1513_ = v_a_1503_;
v___y_1514_ = v_a_1504_;
v___y_1515_ = v_a_1505_;
v___y_1516_ = v_a_1506_;
goto v___jp_1508_;
}
}
v___jp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_mk_empty_array_with_capacity(v___y_1601_);
lean_dec(v___y_1601_);
v___x_1603_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_1602_, v_a_1578_);
if (lean_obj_tag(v_ref_x3f_1499_) == 0)
{
lean_object* v_ref_1604_; 
v_ref_1604_ = lean_ctor_get(v_a_1505_, 5);
lean_inc(v_ref_1604_);
v___y_1580_ = v___x_1603_;
v___y_1581_ = v_ref_1604_;
goto v___jp_1579_;
}
else
{
lean_object* v_val_1605_; 
v_val_1605_ = lean_ctor_get(v_ref_x3f_1499_, 0);
lean_inc(v_val_1605_);
lean_dec_ref(v_ref_x3f_1499_);
v___y_1580_ = v___x_1603_;
v___y_1581_ = v_val_1605_;
goto v___jp_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(lean_object* v_constName_1608_, lean_object* v_idOrConst_1609_, lean_object* v_declHint_1610_, lean_object* v_ref_x3f_1611_, lean_object* v_extraMsg_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1608_, v_idOrConst_1609_, v_declHint_1610_, v_ref_x3f_1611_, v_extraMsg_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions(lean_object* v_00_u03b1_1621_, lean_object* v_constName_1622_, lean_object* v_idOrConst_1623_, lean_object* v_declHint_1624_, lean_object* v_ref_x3f_1625_, lean_object* v_extraMsg_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; 
lean_inc_ref(v_a_1631_);
v___x_1634_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1622_, v_idOrConst_1623_, v_declHint_1624_, v_ref_x3f_1625_, v_extraMsg_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___boxed(lean_object* v_00_u03b1_1635_, lean_object* v_constName_1636_, lean_object* v_idOrConst_1637_, lean_object* v_declHint_1638_, lean_object* v_ref_x3f_1639_, lean_object* v_extraMsg_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_throwUnknownNameWithSuggestions(v_00_u03b1_1635_, v_constName_1636_, v_idOrConst_1637_, v_declHint_1638_, v_ref_x3f_1639_, v_extraMsg_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(lean_object* v_incorrectName_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1649_, v___y_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(lean_object* v_incorrectName_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(v_incorrectName_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_object* v_00_u03b1_1667_, lean_object* v_ref_1668_, lean_object* v_msg_1669_, lean_object* v_declHint_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1668_, v_msg_1669_, v_declHint_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_ref_1680_, lean_object* v_msg_1681_, lean_object* v_declHint_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(v_00_u03b1_1679_, v_ref_1680_, v_msg_1681_, v_declHint_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_ref_1680_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(lean_object* v_as_1691_, lean_object* v_k_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1691_, v_k_1692_, v_x_1693_, v_x_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(lean_object* v_as_1697_, lean_object* v_k_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(v_as_1697_, v_k_1698_, v_x_1699_, v_x_1700_, v_x_1701_);
lean_dec_ref(v_k_1698_);
lean_dec_ref(v_as_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(lean_object* v_msg_1703_, lean_object* v_declHint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1703_, v_declHint_1704_, v___y_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1713_, lean_object* v_declHint_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_1713_, v_declHint_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_object* v_00_u03b1_1723_, lean_object* v_ref_1724_, lean_object* v_msg_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1724_, v_msg_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_ref_1735_, lean_object* v_msg_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(v_00_u03b1_1734_, v_ref_1735_, v_msg_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_ref_1735_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1745_, lean_object* v_msg_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
lean_inc_ref(v___y_1747_);
v___x_1754_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_msg_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(v_00_u03b1_1755_, v_msg_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(lean_object* v_msgData_1765_, lean_object* v_macroStack_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1765_, v_macroStack_1766_, v___y_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(lean_object* v_msgData_1775_, lean_object* v_macroStack_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_1775_, v_macroStack_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1784_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(lean_object* v_exp_1785_, lean_object* v_as_1786_, size_t v_i_1787_, size_t v_stop_1788_){
_start:
{
uint8_t v___x_1789_; 
v___x_1789_ = lean_usize_dec_eq(v_i_1787_, v_stop_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_array_uget_borrowed(v_as_1786_, v_i_1787_);
v___x_1791_ = lean_expr_eqv(v___x_1790_, v_exp_1785_);
if (v___x_1791_ == 0)
{
size_t v___x_1792_; size_t v___x_1793_; 
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_add(v_i_1787_, v___x_1792_);
v_i_1787_ = v___x_1793_;
goto _start;
}
else
{
return v___x_1791_;
}
}
else
{
uint8_t v___x_1795_; 
v___x_1795_ = 0;
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(lean_object* v_exp_1796_, lean_object* v_as_1797_, lean_object* v_i_1798_, lean_object* v_stop_1799_){
_start:
{
size_t v_i_boxed_1800_; size_t v_stop_boxed_1801_; uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_i_boxed_1800_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_stop_boxed_1801_ = lean_unbox_usize(v_stop_1799_);
lean_dec(v_stop_1799_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1796_, v_as_1797_, v_i_boxed_1800_, v_stop_boxed_1801_);
lean_dec_ref(v_as_1797_);
lean_dec_ref(v_exp_1796_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(lean_object* v_exp_1804_, lean_object* v_x_1805_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v_cs_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_cs_1806_ = lean_ctor_get(v_x_1805_, 0);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_array_get_size(v_cs_1806_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
return v___x_1809_;
}
else
{
if (v___x_1809_ == 0)
{
return v___x_1809_;
}
else
{
size_t v___x_1810_; size_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = lean_usize_of_nat(v___x_1808_);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1804_, v_cs_1806_, v___x_1810_, v___x_1811_);
return v___x_1812_;
}
}
}
else
{
lean_object* v_vs_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_vs_1813_ = lean_ctor_get(v_x_1805_, 0);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_array_get_size(v_vs_1813_);
v___x_1816_ = lean_nat_dec_lt(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
return v___x_1816_;
}
else
{
if (v___x_1816_ == 0)
{
return v___x_1816_;
}
else
{
size_t v___x_1817_; size_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1815_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1804_, v_vs_1813_, v___x_1817_, v___x_1818_);
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(lean_object* v_exp_1820_, lean_object* v_as_1821_, size_t v_i_1822_, size_t v_stop_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_eq(v_i_1822_, v_stop_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_uget_borrowed(v_as_1821_, v_i_1822_);
v___x_1826_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1820_, v___x_1825_);
if (v___x_1826_ == 0)
{
size_t v___x_1827_; size_t v___x_1828_; 
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_add(v_i_1822_, v___x_1827_);
v_i_1822_ = v___x_1828_;
goto _start;
}
else
{
return v___x_1826_;
}
}
else
{
uint8_t v___x_1830_; 
v___x_1830_ = 0;
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(lean_object* v_exp_1831_, lean_object* v_as_1832_, lean_object* v_i_1833_, lean_object* v_stop_1834_){
_start:
{
size_t v_i_boxed_1835_; size_t v_stop_boxed_1836_; uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_i_boxed_1835_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_stop_boxed_1836_ = lean_unbox_usize(v_stop_1834_);
lean_dec(v_stop_1834_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1831_, v_as_1832_, v_i_boxed_1835_, v_stop_boxed_1836_);
lean_dec_ref(v_as_1832_);
lean_dec_ref(v_exp_1831_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(lean_object* v_exp_1839_, lean_object* v_x_1840_){
_start:
{
uint8_t v_res_1841_; lean_object* v_r_1842_; 
v_res_1841_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1839_, v_x_1840_);
lean_dec_ref(v_x_1840_);
lean_dec_ref(v_exp_1839_);
v_r_1842_ = lean_box(v_res_1841_);
return v_r_1842_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(lean_object* v_exp_1843_, lean_object* v_t_1844_){
_start:
{
lean_object* v_root_1845_; lean_object* v_tail_1846_; uint8_t v___x_1847_; 
v_root_1845_ = lean_ctor_get(v_t_1844_, 0);
v_tail_1846_ = lean_ctor_get(v_t_1844_, 1);
v___x_1847_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1843_, v_root_1845_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_array_get_size(v_tail_1846_);
v___x_1850_ = lean_nat_dec_lt(v___x_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
return v___x_1847_;
}
else
{
if (v___x_1850_ == 0)
{
return v___x_1847_;
}
else
{
size_t v___x_1851_; size_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1849_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1843_, v_tail_1846_, v___x_1851_, v___x_1852_);
return v___x_1853_;
}
}
}
else
{
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(lean_object* v_exp_1854_, lean_object* v_t_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_1854_, v_t_1855_);
lean_dec_ref(v_t_1855_);
lean_dec_ref(v_exp_1854_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(lean_object* v_init_1858_, lean_object* v_x_1859_){
_start:
{
if (lean_obj_tag(v_x_1859_) == 0)
{
lean_object* v_k_1860_; lean_object* v_l_1861_; lean_object* v_r_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_k_1860_ = lean_ctor_get(v_x_1859_, 1);
v_l_1861_ = lean_ctor_get(v_x_1859_, 3);
v_r_1862_ = lean_ctor_get(v_x_1859_, 4);
v___x_1863_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1858_, v_r_1862_);
lean_inc(v_k_1860_);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_k_1860_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v_init_1858_ = v___x_1864_;
v_x_1859_ = v_l_1861_;
goto _start;
}
else
{
return v_init_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(lean_object* v_init_1866_, lean_object* v_x_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1866_, v_x_1867_);
lean_dec(v_x_1867_);
return v_res_1868_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0));
v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
if (lean_obj_tag(v_a_1872_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = l_List_reverse___redArg(v_a_1873_);
return v___x_1874_;
}
else
{
lean_object* v_head_1875_; lean_object* v_tail_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1891_; 
v_head_1875_ = lean_ctor_get(v_a_1872_, 0);
v_tail_1876_ = lean_ctor_get(v_a_1872_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_a_1872_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1878_ = v_a_1872_;
v_isShared_1879_ = v_isSharedCheck_1891_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_tail_1876_);
lean_inc(v_head_1875_);
lean_dec(v_a_1872_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1891_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1880_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1);
v___x_1881_ = 0;
v___x_1882_ = l_Lean_MessageData_ofConstName(v_head_1875_, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_indentD(v___x_1885_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_a_1873_);
lean_ctor_set(v___x_1878_, 0, v___x_1886_);
v___x_1888_ = v___x_1878_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_a_1873_);
v___x_1888_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v_a_1872_ = v_tail_1876_;
v_a_1873_ = v___x_1888_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0));
v___x_1894_ = l_Lean_stringToMessageData(v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2));
v___x_1897_ = l_Lean_stringToMessageData(v___x_1896_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4));
v___x_1900_ = l_Lean_stringToMessageData(v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6));
v___x_1903_ = l_Lean_stringToMessageData(v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9));
v___x_1908_ = l_Lean_stringToMessageData(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11));
v___x_1911_ = l_Lean_stringToMessageData(v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13));
v___x_1914_ = l_Lean_stringToMessageData(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17));
v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(lean_object* v_exp_1921_, lean_object* v_expected_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_autoBoundImplicitContext_1931_; 
v_autoBoundImplicitContext_1931_ = lean_ctor_get(v_a_1923_, 2);
if (lean_obj_tag(v_autoBoundImplicitContext_1931_) == 0)
{
lean_dec_ref(v_expected_1922_);
goto v___jp_1928_;
}
else
{
lean_object* v_val_1932_; uint8_t v___x_1933_; 
v_val_1932_ = lean_ctor_get(v_autoBoundImplicitContext_1931_, 0);
v___x_1933_ = l_Lean_Expr_isFVar(v_exp_1921_);
if (v___x_1933_ == 0)
{
lean_dec_ref(v_expected_1922_);
goto v___jp_1928_;
}
else
{
lean_object* v_boundVariables_1934_; uint8_t v___x_1935_; 
v_boundVariables_1934_ = lean_ctor_get(v_val_1932_, 0);
v___x_1935_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_1921_, v_boundVariables_1934_);
if (v___x_1935_ == 0)
{
lean_dec_ref(v_expected_1922_);
goto v___jp_1928_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = l_Lean_Expr_fvarId_x21(v_exp_1921_);
v___x_1937_ = l_Lean_FVarId_getUserName___redArg(v___x_1936_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1996_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
lean_inc(v_a_1938_);
v___x_1939_ = l_Lean_MessageData_ofName(v_a_1938_);
v___x_1940_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_a_1938_, v_a_1926_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1996_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1996_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___y_1957_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1945_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1);
lean_inc_ref(v___x_1939_);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1939_);
v___x_1947_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_stringToMessageData(v_expected_1922_);
lean_inc_ref(v___x_1949_);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v___x_1949_);
v___x_1954_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v___x_1963_, v_a_1941_);
lean_dec(v_a_1941_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref(v___x_1939_);
v___x_1965_ = l_Lean_MessageData_nil;
v___y_1957_ = v___x_1965_;
goto v___jp_1956_;
}
else
{
lean_object* v_tail_1966_; 
v_tail_1966_ = lean_ctor_get(v___x_1964_, 1);
lean_inc(v_tail_1966_);
if (lean_obj_tag(v_tail_1966_) == 0)
{
lean_object* v_head_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1984_; 
v_head_1967_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1964_, 1);
lean_dec(v_unused_1985_);
v___x_1969_ = v___x_1964_;
v_isShared_1970_ = v_isSharedCheck_1984_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_head_1967_);
lean_dec(v___x_1964_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1984_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1971_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_1972_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10);
v___x_1973_ = 0;
v___x_1974_ = l_Lean_MessageData_ofConstName(v_head_1967_, v___x_1973_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 7);
lean_ctor_set(v___x_1969_, 1, v___x_1974_);
lean_ctor_set(v___x_1969_, 0, v___x_1972_);
v___x_1976_ = v___x_1969_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1977_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1939_);
v___x_1980_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1971_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___y_1957_ = v___x_1982_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec(v_tail_1966_);
v___x_1986_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_1987_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v___x_1939_);
v___x_1989_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1986_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(v___x_1964_, v___x_1963_);
v___x_1993_ = l_Lean_MessageData_nil;
v___x_1994_ = l_Lean_MessageData_joinSep(v___x_1992_, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1991_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___y_1957_ = v___x_1995_;
goto v___jp_1956_;
}
}
v___jp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1955_);
lean_ctor_set(v___x_1958_, 1, v___y_1957_);
v___x_1959_ = l_Lean_MessageData_hint_x27(v___x_1958_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1959_);
v___x_1961_ = v___x_1943_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_expected_1922_);
v_a_1997_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1937_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1937_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
v___jp_1928_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = l_Lean_MessageData_nil;
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(lean_object* v_exp_2005_, lean_object* v_expected_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2005_, v_expected_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_exp_2005_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure(lean_object* v_exp_2013_, lean_object* v_expected_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2013_, v_expected_2014_, v_a_2015_, v_a_2017_, v_a_2019_, v_a_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(lean_object* v_exp_2023_, lean_object* v_expected_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_Elab_Term_hintAutoImplicitFailure(v_exp_2023_, v_expected_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec_ref(v_exp_2023_);
return v_res_2032_;
}
}
lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ErrorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_IdentifierSuggestion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
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
