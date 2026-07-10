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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value;
static const lean_ctor_object l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value),((lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value)}};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4 = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Cannot make suggestions for private names"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid `[suggest_for]` attribute syntax "};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11));
v___x_300_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___boxed(lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0(lean_object* v_init_303_, lean_object* v_t_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_303_, v_t_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(lean_object* v_init_306_, lean_object* v_t_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_306_, v_t_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1___boxed(lean_object* v_init_309_, lean_object* v_t_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(v_init_309_, v_t_310_);
lean_dec(v_t_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(lean_object* v_n_312_, lean_object* v_as_313_, lean_object* v_lo_314_, lean_object* v_hi_315_, lean_object* v_w_316_, lean_object* v_hlo_317_, lean_object* v_hhi_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_312_, v_as_313_, v_lo_314_, v_hi_315_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___boxed(lean_object* v_n_320_, lean_object* v_as_321_, lean_object* v_lo_322_, lean_object* v_hi_323_, lean_object* v_w_324_, lean_object* v_hlo_325_, lean_object* v_hhi_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(v_n_320_, v_as_321_, v_lo_322_, v_hi_323_, v_w_324_, v_hlo_325_, v_hhi_326_);
lean_dec(v_hi_323_);
lean_dec(v_n_320_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(lean_object* v_snd_328_, lean_object* v_k_329_, lean_object* v_t_330_, lean_object* v_hl_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_328_, v_k_329_, v_t_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___boxed(lean_object* v_snd_333_, lean_object* v_k_334_, lean_object* v_t_335_, lean_object* v_hl_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(v_snd_333_, v_k_334_, v_t_335_, v_hl_336_);
lean_dec_ref(v_snd_333_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(lean_object* v_n_338_, lean_object* v_lo_339_, lean_object* v_hi_340_, lean_object* v_hhi_341_, lean_object* v_pivot_342_, lean_object* v_as_343_, lean_object* v_i_344_, lean_object* v_k_345_, lean_object* v_ilo_346_, lean_object* v_ik_347_, lean_object* v_w_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_340_, v_pivot_342_, v_as_343_, v_i_344_, v_k_345_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___boxed(lean_object* v_n_350_, lean_object* v_lo_351_, lean_object* v_hi_352_, lean_object* v_hhi_353_, lean_object* v_pivot_354_, lean_object* v_as_355_, lean_object* v_i_356_, lean_object* v_k_357_, lean_object* v_ilo_358_, lean_object* v_ik_359_, lean_object* v_w_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(v_n_350_, v_lo_351_, v_hi_352_, v_hhi_353_, v_pivot_354_, v_as_355_, v_i_356_, v_k_357_, v_ilo_358_, v_ik_359_, v_w_360_);
lean_dec_ref(v_pivot_354_);
lean_dec(v_hi_352_);
lean_dec(v_lo_351_);
lean_dec(v_n_350_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(lean_object* v_fst_362_, lean_object* v_old_363_){
_start:
{
lean_object* v___y_365_; 
if (lean_obj_tag(v_old_363_) == 0)
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_NameSet_empty;
v___y_365_ = v___x_368_;
goto v___jp_364_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v_old_363_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v_old_363_, 1);
v___y_365_ = v_val_369_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_Lean_NameSet_insert(v___y_365_, v_fst_362_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(lean_object* v_fst_370_, lean_object* v_k_371_, lean_object* v_t_372_){
_start:
{
if (lean_obj_tag(v_t_372_) == 0)
{
lean_object* v_size_373_; lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_l_376_; lean_object* v_r_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_392_; 
v_size_373_ = lean_ctor_get(v_t_372_, 0);
v_k_374_ = lean_ctor_get(v_t_372_, 1);
v_v_375_ = lean_ctor_get(v_t_372_, 2);
v_l_376_ = lean_ctor_get(v_t_372_, 3);
v_r_377_ = lean_ctor_get(v_t_372_, 4);
v_isSharedCheck_392_ = !lean_is_exclusive(v_t_372_);
if (v_isSharedCheck_392_ == 0)
{
v___x_379_ = v_t_372_;
v_isShared_380_ = v_isSharedCheck_392_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_r_377_);
lean_inc(v_l_376_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
lean_inc(v_size_373_);
lean_dec(v_t_372_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_392_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
uint8_t v___x_381_; 
v___x_381_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_371_, v_k_374_);
switch(v___x_381_)
{
case 0:
{
lean_object* v_impl_382_; lean_object* v___x_383_; 
lean_del_object(v___x_379_);
lean_dec(v_size_373_);
v_impl_382_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_370_, v_k_371_, v_l_376_);
v___x_383_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_374_, v_v_375_, v_impl_382_, v_r_377_);
return v___x_383_;
}
case 1:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_val_386_; lean_object* v___x_388_; 
lean_dec(v_k_374_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v_v_375_);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_370_, v___x_384_);
v_val_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_386_);
lean_dec(v___x_385_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 2, v_val_386_);
lean_ctor_set(v___x_379_, 1, v_k_371_);
v___x_388_ = v___x_379_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_size_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_k_371_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_val_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_r_377_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
default: 
{
lean_object* v_impl_390_; lean_object* v___x_391_; 
lean_del_object(v___x_379_);
lean_dec(v_size_373_);
v_impl_390_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_370_, v_k_371_, v_r_377_);
v___x_391_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_374_, v_v_375_, v_l_376_, v_impl_390_);
return v___x_391_;
}
}
}
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_val_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = lean_box(0);
v___x_394_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_370_, v___x_393_);
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec(v___x_394_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_k_371_);
lean_ctor_set(v___x_397_, 2, v_val_395_);
lean_ctor_set(v___x_397_, 3, v_t_372_);
lean_ctor_set(v___x_397_, 4, v_t_372_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(lean_object* v_fst_398_, lean_object* v_as_399_, size_t v_i_400_, size_t v_stop_401_, lean_object* v_b_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_eq(v_i_400_, v_stop_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; size_t v___x_406_; size_t v___x_407_; 
v___x_404_ = lean_array_uget_borrowed(v_as_399_, v_i_400_);
lean_inc(v___x_404_);
lean_inc(v_fst_398_);
v___x_405_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_398_, v___x_404_, v_b_402_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_400_, v___x_406_);
v_i_400_ = v___x_407_;
v_b_402_ = v___x_405_;
goto _start;
}
else
{
lean_dec(v_fst_398_);
return v_b_402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1___boxed(lean_object* v_fst_409_, lean_object* v_as_410_, lean_object* v_i_411_, lean_object* v_stop_412_, lean_object* v_b_413_){
_start:
{
size_t v_i_boxed_414_; size_t v_stop_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_stop_boxed_415_ = lean_unbox_usize(v_stop_412_);
lean_dec(v_stop_412_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_409_, v_as_410_, v_i_boxed_414_, v_stop_boxed_415_, v_b_413_);
lean_dec_ref(v_as_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0(lean_object* v_table_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_fst_419_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_fst_419_);
v_snd_420_ = lean_ctor_get(v_x_418_, 1);
lean_inc(v_snd_420_);
lean_dec_ref(v_x_418_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_array_get_size(v_snd_420_);
v___x_423_ = lean_nat_dec_lt(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_dec(v_snd_420_);
lean_dec(v_fst_419_);
return v_table_417_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_le(v___x_422_, v___x_422_);
if (v___x_424_ == 0)
{
if (v___x_423_ == 0)
{
lean_dec(v_snd_420_);
lean_dec(v_fst_419_);
return v_table_417_;
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((size_t)0ULL);
v___x_426_ = lean_usize_of_nat(v___x_422_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_419_, v_snd_420_, v___x_425_, v___x_426_, v_table_417_);
lean_dec(v_snd_420_);
return v___x_427_;
}
}
else
{
size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_428_ = ((size_t)0ULL);
v___x_429_ = lean_usize_of_nat(v___x_422_);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_419_, v_snd_420_, v___x_428_, v___x_429_, v_table_417_);
lean_dec(v_snd_420_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4));
v___x_451_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(lean_object* v_fst_454_, lean_object* v_k_455_, lean_object* v_t_456_, lean_object* v_hl_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_454_, v_k_455_, v_t_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_459_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set(v___x_464_, 3, v___x_463_);
lean_ctor_set(v___x_464_, 4, v___x_462_);
lean_ctor_set(v___x_464_, 5, v___x_462_);
lean_ctor_set(v___x_464_, 6, v___x_462_);
lean_ctor_set(v___x_464_, 7, v___x_462_);
lean_ctor_set(v___x_464_, 8, v___x_462_);
lean_ctor_set(v___x_464_, 9, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(32u);
v___x_466_ = lean_mk_empty_array_with_capacity(v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_468_ = ((size_t)5ULL);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_unsigned_to_nat(32u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_473_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
lean_ctor_set(v___x_473_, 2, v___x_469_);
lean_ctor_set(v___x_473_, 3, v___x_469_);
lean_ctor_set_usize(v___x_473_, 4, v___x_468_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_box(1);
v___x_475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_476_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_474_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; lean_object* v_env_483_; lean_object* v_options_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_482_ = lean_st_ref_get(v___y_480_);
v_env_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref(v_env_483_);
lean_dec(v___x_482_);
v_options_484_ = lean_ctor_get(v___y_479_, 2);
v___x_485_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_486_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_484_);
v___x_487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_487_, 0, v_env_483_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
lean_ctor_set(v___x_487_, 3, v_options_484_);
v___x_488_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_msgData_478_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_ref_499_; lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_ref_499_ = lean_ctor_get(v___y_496_, 5);
v___x_500_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msg_495_, v___y_496_, v___y_497_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_inc(v_ref_499_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_ref_499_);
lean_ctor_set(v___x_505_, 1, v_a_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 1);
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2));
v___x_520_ = l_Lean_stringToMessageData(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4));
v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object* v_name_527_, uint8_t v_kind_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___y_538_; 
v___x_532_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_533_ = l_Lean_MessageData_ofName(v_name_527_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
switch(v_kind_528_)
{
case 0:
{
lean_object* v___x_545_; 
v___x_545_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6));
v___y_538_ = v___x_545_;
goto v___jp_537_;
}
case 1:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7));
v___y_538_ = v___x_546_;
goto v___jp_537_;
}
default: 
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8));
v___y_538_ = v___x_547_;
goto v___jp_537_;
}
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc_ref(v___y_538_);
v___x_539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_539_, 0, v___y_538_);
v___x_540_ = l_Lean_MessageData_ofFormat(v___x_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_536_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_543_, v___y_529_, v___y_530_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_name_548_, lean_object* v_kind_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
uint8_t v_kind_boxed_553_; lean_object* v_res_554_; 
v_kind_boxed_553_ = lean_unbox(v_kind_549_);
v_res_554_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_548_, v_kind_boxed_553_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t v_sz_555_, size_t v_i_556_, lean_object* v_bs_557_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_556_, v_sz_555_);
if (v___x_558_ == 0)
{
return v_bs_557_;
}
else
{
lean_object* v_v_559_; lean_object* v___x_560_; lean_object* v_bs_x27_561_; lean_object* v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v_v_559_ = lean_array_uget(v_bs_557_, v_i_556_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_bs_x27_561_ = lean_array_uset(v_bs_557_, v_i_556_, v___x_560_);
v___x_562_ = l_Lean_Syntax_getId(v_v_559_);
lean_dec(v_v_559_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_556_, v___x_563_);
v___x_565_ = lean_array_uset(v_bs_x27_561_, v_i_556_, v___x_562_);
v_i_556_ = v___x_564_;
v_bs_557_ = v___x_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_bs_569_){
_start:
{
size_t v_sz_boxed_570_; size_t v_i_boxed_571_; lean_object* v_res_572_; 
v_sz_boxed_570_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_571_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_boxed_570_, v_i_boxed_571_, v_bs_569_);
return v_res_572_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v_a_588_, lean_object* v___x_589_, lean_object* v_a_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v_decl_595_, lean_object* v_stx_596_, uint8_t v_kind_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v_altSyntaxIds_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 0;
v___x_736_ = l_Lean_instBEqAttributeKind_beq(v_kind_597_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v_stx_596_);
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___x_737_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v___x_594_, v_kind_597_, v___y_598_, v___y_599_);
return v___x_737_;
}
else
{
lean_dec(v___x_594_);
goto v___jp_676_;
}
v___jp_601_:
{
lean_object* v___x_604_; lean_object* v_toEnvExtension_605_; lean_object* v_env_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_traceState_610_; lean_object* v_messages_611_; lean_object* v_infoState_612_; lean_object* v_snapshotTasks_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_651_; 
v___x_604_ = lean_st_ref_take(v___y_603_);
v_toEnvExtension_605_ = lean_ctor_get(v_a_588_, 0);
v_env_606_ = lean_ctor_get(v___x_604_, 0);
v_nextMacroScope_607_ = lean_ctor_get(v___x_604_, 1);
v_ngen_608_ = lean_ctor_get(v___x_604_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_604_, 3);
v_traceState_610_ = lean_ctor_get(v___x_604_, 4);
v_messages_611_ = lean_ctor_get(v___x_604_, 6);
v_infoState_612_ = lean_ctor_get(v___x_604_, 7);
v_snapshotTasks_613_ = lean_ctor_get(v___x_604_, 8);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_604_, 5);
lean_dec(v_unused_652_);
v___x_615_ = v___x_604_;
v_isShared_616_ = v_isSharedCheck_651_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snapshotTasks_613_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_611_);
lean_inc(v_traceState_610_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_inc(v_env_606_);
lean_dec(v___x_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_651_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_asyncMode_617_; size_t v_sz_618_; size_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_asyncMode_617_ = lean_ctor_get(v_toEnvExtension_605_, 2);
lean_inc(v_asyncMode_617_);
v_sz_618_ = lean_array_size(v___y_602_);
v___x_619_ = ((size_t)0ULL);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_618_, v___x_619_, v___y_602_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_decl_595_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc(v___x_589_);
lean_inc_ref(v___x_621_);
v___x_622_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_588_, v_env_606_, v___x_621_, v_asyncMode_617_, v___x_589_);
lean_dec(v_asyncMode_617_);
v___x_623_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 5, v___x_623_);
lean_ctor_set(v___x_615_, 0, v___x_622_);
v___x_625_ = v___x_615_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_traceState_610_);
lean_ctor_set(v_reuseFailAlloc_650_, 5, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_650_, 6, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_650_, 7, v_infoState_612_);
lean_ctor_set(v_reuseFailAlloc_650_, 8, v_snapshotTasks_613_);
v___x_625_ = v_reuseFailAlloc_650_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_toEnvExtension_628_; lean_object* v_env_629_; lean_object* v_nextMacroScope_630_; lean_object* v_ngen_631_; lean_object* v_auxDeclNGen_632_; lean_object* v_traceState_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_648_; 
v___x_626_ = lean_st_ref_set(v___y_603_, v___x_625_);
v___x_627_ = lean_st_ref_take(v___y_603_);
v_toEnvExtension_628_ = lean_ctor_get(v_a_590_, 0);
v_env_629_ = lean_ctor_get(v___x_627_, 0);
v_nextMacroScope_630_ = lean_ctor_get(v___x_627_, 1);
v_ngen_631_ = lean_ctor_get(v___x_627_, 2);
v_auxDeclNGen_632_ = lean_ctor_get(v___x_627_, 3);
v_traceState_633_ = lean_ctor_get(v___x_627_, 4);
v_messages_634_ = lean_ctor_get(v___x_627_, 6);
v_infoState_635_ = lean_ctor_get(v___x_627_, 7);
v_snapshotTasks_636_ = lean_ctor_get(v___x_627_, 8);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v___x_627_, 5);
lean_dec(v_unused_649_);
v___x_638_ = v___x_627_;
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snapshotTasks_636_);
lean_inc(v_infoState_635_);
lean_inc(v_messages_634_);
lean_inc(v_traceState_633_);
lean_inc(v_auxDeclNGen_632_);
lean_inc(v_ngen_631_);
lean_inc(v_nextMacroScope_630_);
lean_inc(v_env_629_);
lean_dec(v___x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_asyncMode_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v_asyncMode_640_ = lean_ctor_get(v_toEnvExtension_628_, 2);
lean_inc(v_asyncMode_640_);
v___x_641_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_590_, v_env_629_, v___x_621_, v_asyncMode_640_, v___x_589_);
lean_dec(v_asyncMode_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 5, v___x_623_);
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_nextMacroScope_630_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_ngen_631_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_auxDeclNGen_632_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_traceState_633_);
lean_ctor_set(v_reuseFailAlloc_647_, 5, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_647_, 6, v_messages_634_);
lean_ctor_set(v_reuseFailAlloc_647_, 7, v_infoState_635_);
lean_ctor_set(v_reuseFailAlloc_647_, 8, v_snapshotTasks_636_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_st_ref_set(v___y_603_, v___x_643_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
}
}
v___jp_653_:
{
uint8_t v___x_657_; 
v___x_657_ = l_Lean_isPrivateName(v_decl_595_);
if (v___x_657_ == 0)
{
v___y_602_ = v_altSyntaxIds_654_;
v___y_603_ = v___y_656_;
goto v___jp_601_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec_ref(v_altSyntaxIds_654_);
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___x_658_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_659_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_658_, v___y_655_, v___y_656_);
return v___x_659_;
}
}
v___jp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v___x_663_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_664_ = l_Lean_Syntax_instRepr_repr(v_stx_596_, v___x_591_);
v___x_665_ = l_Lean_MessageData_ofFormat(v___x_664_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_663_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_666_, v___y_661_, v___y_662_);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
v___jp_676_:
{
if (lean_obj_tag(v_stx_596_) == 1)
{
lean_object* v_kind_677_; 
v_kind_677_ = lean_ctor_get(v_stx_596_, 1);
if (lean_obj_tag(v_kind_677_) == 1)
{
lean_object* v_pre_678_; 
v_pre_678_ = lean_ctor_get(v_kind_677_, 0);
if (lean_obj_tag(v_pre_678_) == 1)
{
lean_object* v_pre_679_; 
v_pre_679_ = lean_ctor_get(v_pre_678_, 0);
switch(lean_obj_tag(v_pre_679_))
{
case 0:
{
lean_object* v_args_680_; lean_object* v_str_681_; lean_object* v_str_682_; uint8_t v___x_683_; 
v_args_680_ = lean_ctor_get(v_stx_596_, 2);
v_str_681_ = lean_ctor_get(v_kind_677_, 1);
v_str_682_ = lean_ctor_get(v_pre_678_, 1);
v___x_683_ = lean_string_dec_eq(v_str_682_, v___x_592_);
if (v___x_683_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
uint8_t v___x_684_; 
v___x_684_ = lean_string_dec_eq(v_str_681_, v___x_593_);
if (v___x_684_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_array_get_size(v_args_680_);
v___x_686_ = lean_unsigned_to_nat(2u);
v___x_687_ = lean_nat_dec_eq(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_array_fget_borrowed(v_args_680_, v___x_591_);
if (lean_obj_tag(v___x_688_) == 2)
{
lean_object* v_val_689_; uint8_t v___x_690_; 
v_val_689_ = lean_ctor_get(v___x_688_, 1);
v___x_690_ = lean_string_dec_eq(v_val_689_, v___x_593_);
if (v___x_690_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_array_fget_borrowed(v_args_680_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 1)
{
lean_object* v_kind_693_; 
v_kind_693_ = lean_ctor_get(v___x_692_, 1);
if (lean_obj_tag(v_kind_693_) == 1)
{
lean_object* v_pre_694_; 
v_pre_694_ = lean_ctor_get(v_kind_693_, 0);
if (lean_obj_tag(v_pre_694_) == 0)
{
lean_object* v_args_695_; lean_object* v_str_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_args_695_ = lean_ctor_get(v___x_692_, 2);
v_str_696_ = lean_ctor_get(v_kind_693_, 1);
v___x_697_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_698_ = lean_string_dec_eq(v_str_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_inc_ref(v_args_695_);
lean_dec_ref_known(v_stx_596_, 3);
v_altSyntaxIds_654_ = v_args_695_;
v___y_655_ = v___y_598_;
v___y_656_ = v___y_599_;
goto v___jp_653_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
}
}
}
case 1:
{
lean_object* v_pre_699_; 
v_pre_699_ = lean_ctor_get(v_pre_679_, 0);
if (lean_obj_tag(v_pre_699_) == 1)
{
lean_object* v_pre_700_; 
v_pre_700_ = lean_ctor_get(v_pre_699_, 0);
if (lean_obj_tag(v_pre_700_) == 0)
{
lean_object* v_args_701_; lean_object* v_str_702_; lean_object* v_str_703_; lean_object* v_str_704_; lean_object* v_str_705_; uint8_t v___x_706_; 
v_args_701_ = lean_ctor_get(v_stx_596_, 2);
v_str_702_ = lean_ctor_get(v_kind_677_, 1);
v_str_703_ = lean_ctor_get(v_pre_678_, 1);
v_str_704_ = lean_ctor_get(v_pre_679_, 1);
v_str_705_ = lean_ctor_get(v_pre_699_, 1);
v___x_706_ = lean_string_dec_eq(v_str_705_, v___x_592_);
if (v___x_706_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_708_ = lean_string_dec_eq(v_str_704_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_710_ = lean_string_dec_eq(v_str_703_, v___x_709_);
if (v___x_710_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_712_ = lean_string_dec_eq(v_str_702_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_array_get_size(v_args_701_);
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = lean_nat_dec_eq(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = lean_array_fget_borrowed(v_args_701_, v___x_591_);
if (lean_obj_tag(v___x_716_) == 3)
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___x_716_, 2);
if (lean_obj_tag(v_val_717_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_val_717_, 0);
if (lean_obj_tag(v_pre_718_) == 0)
{
lean_object* v_preresolved_719_; lean_object* v_str_720_; uint8_t v___x_721_; 
v_preresolved_719_ = lean_ctor_get(v___x_716_, 3);
v_str_720_ = lean_ctor_get(v_val_717_, 1);
v___x_721_ = lean_string_dec_eq(v_str_720_, v___x_593_);
if (v___x_721_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
if (lean_obj_tag(v_preresolved_719_) == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_array_fget_borrowed(v_args_701_, v___x_722_);
if (lean_obj_tag(v___x_723_) == 1)
{
lean_object* v_kind_724_; 
v_kind_724_ = lean_ctor_get(v___x_723_, 1);
if (lean_obj_tag(v_kind_724_) == 1)
{
lean_object* v_pre_725_; 
v_pre_725_ = lean_ctor_get(v_kind_724_, 0);
if (lean_obj_tag(v_pre_725_) == 0)
{
lean_object* v_args_726_; lean_object* v_str_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_args_726_ = lean_ctor_get(v___x_723_, 2);
v_str_727_ = lean_ctor_get(v_kind_724_, 1);
v___x_728_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_729_ = lean_string_dec_eq(v_str_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_args_726_);
v___x_731_ = lean_nat_dec_eq(v___x_730_, v___x_722_);
if (v___x_731_ == 0)
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_inc_ref(v_args_726_);
lean_dec_ref_known(v_stx_596_, 3);
v___x_732_ = lean_array_fget(v_args_726_, v___x_591_);
lean_dec_ref(v_args_726_);
v___x_733_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_734_ = lean_array_push(v___x_733_, v___x_732_);
v_altSyntaxIds_654_ = v___x_734_;
v___y_655_ = v___y_598_;
v___y_656_ = v___y_599_;
goto v___jp_653_;
}
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
default: 
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_decl_595_);
lean_dec_ref(v_a_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_a_588_);
v___y_661_ = v___y_598_;
v___y_662_ = v___y_599_;
goto v___jp_660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_738_, lean_object* v___x_739_, lean_object* v_a_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v_decl_745_, lean_object* v_stx_746_, lean_object* v_kind_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v_kind_boxed_751_; lean_object* v_res_752_; 
v_kind_boxed_751_ = lean_unbox(v_kind_747_);
v_res_752_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v_a_738_, v___x_739_, v_a_740_, v___x_741_, v___x_742_, v___x_743_, v___x_744_, v_decl_745_, v_stx_746_, v_kind_boxed_751_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec_ref(v___x_743_);
lean_dec_ref(v___x_742_);
lean_dec(v___x_741_);
return v_res_752_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(lean_object* v___x_759_, lean_object* v_decl_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_764_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_765_ = l_Lean_MessageData_ofName(v___x_759_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_768_, v___y_761_, v___y_762_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v___x_770_, lean_object* v_decl_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v___x_770_, v_decl_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v_decl_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_n(v_a_812_, 2);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = lean_box(0);
v___x_814_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4));
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_817_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
lean_inc(v_a_810_);
v___f_818_ = lean_alloc_closure((void*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed), 13, 7);
lean_closure_set(v___f_818_, 0, v_a_810_);
lean_closure_set(v___f_818_, 1, v___x_813_);
lean_closure_set(v___f_818_, 2, v_a_812_);
lean_closure_set(v___f_818_, 3, v___x_815_);
lean_closure_set(v___f_818_, 4, v___x_814_);
lean_closure_set(v___f_818_, 5, v___x_816_);
lean_closure_set(v___f_818_, 6, v___x_817_);
v___f_819_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_820_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___f_818_);
lean_ctor_set(v___x_821_, 2, v___f_819_);
v___x_822_ = l_Lean_registerBuiltinAttribute(v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_831_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_a_810_);
lean_ctor_set(v___x_826_, 1, v_a_812_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_812_);
lean_dec(v_a_810_);
v_a_832_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_822_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_810_);
v_a_840_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_811_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_811_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_809_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_809_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
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
LEAN_EXPORT lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_858_, lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_859_, v___y_860_, v___y_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_864_, lean_object* v_msg_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(v_00_u03b1_864_, v_msg_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b1_870_, lean_object* v_name_871_, uint8_t v_kind_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_871_, v_kind_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b1_877_, lean_object* v_name_878_, lean_object* v_kind_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v_kind_boxed_883_; lean_object* v_res_884_; 
v_kind_boxed_883_ = lean_unbox(v_kind_879_);
v_res_884_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(v_00_u03b1_877_, v_name_878_, v_kind_boxed_883_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1(lean_object* v_incorrectName_907_, lean_object* v___f_908_, lean_object* v___f_909_, lean_object* v_x1_910_, lean_object* v_x2_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_get_size(v_x2_911_);
v___x_914_ = lean_nat_dec_lt(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec_ref(v___f_909_);
lean_dec_ref(v___f_908_);
lean_dec(v_incorrectName_907_);
return v_x1_910_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_sub(v___x_913_, v___x_915_);
v___x_917_ = lean_nat_dec_le(v___x_912_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec(v___x_916_);
lean_dec_ref(v___f_909_);
lean_dec_ref(v___f_908_);
lean_dec(v_incorrectName_907_);
return v_x1_910_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_incorrectName_907_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_921_ = l_Array_binSearchAux___redArg(v___f_908_, v___x_920_, v_x2_911_, v___x_919_, v___x_912_, v___x_916_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref(v___f_909_);
return v_x1_910_;
}
else
{
lean_object* v_val_922_; lean_object* v_snd_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_val_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v___x_921_, 1);
v_snd_923_ = lean_ctor_get(v_val_922_, 1);
lean_inc(v_snd_923_);
lean_dec(v_val_922_);
v___x_924_ = lean_array_get_size(v_snd_923_);
v___x_925_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_926_ = lean_nat_dec_lt(v___x_912_, v___x_924_);
if (v___x_926_ == 0)
{
lean_dec(v_snd_923_);
lean_dec_ref(v___f_909_);
return v_x1_910_;
}
else
{
uint8_t v___x_927_; 
v___x_927_ = lean_nat_dec_le(v___x_924_, v___x_924_);
if (v___x_927_ == 0)
{
if (v___x_926_ == 0)
{
lean_dec(v_snd_923_);
lean_dec_ref(v___f_909_);
return v_x1_910_;
}
else
{
size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((size_t)0ULL);
v___x_929_ = lean_usize_of_nat(v___x_924_);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_925_, v___f_909_, v_snd_923_, v___x_928_, v___x_929_, v_x1_910_);
return v___x_930_;
}
}
else
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((size_t)0ULL);
v___x_932_ = lean_usize_of_nat(v___x_924_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_925_, v___f_909_, v_snd_923_, v___x_931_, v___x_932_, v_x1_910_);
return v___x_933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__1___boxed(lean_object* v_incorrectName_934_, lean_object* v___f_935_, lean_object* v___f_936_, lean_object* v_x1_937_, lean_object* v_x2_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_getSuggestions___redArg___lam__1(v_incorrectName_934_, v___f_935_, v___f_936_, v_x1_937_, v_x2_938_);
lean_dec_ref(v_x2_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0(lean_object* v___x_940_, lean_object* v_toPure_941_, lean_object* v___f_942_, lean_object* v_incorrectName_943_, lean_object* v_env_944_){
_start:
{
lean_object* v___x_945_; lean_object* v_snd_946_; lean_object* v_toEnvExtension_947_; lean_object* v_asyncMode_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_importedEntries_951_; lean_object* v_state_952_; lean_object* v___y_954_; lean_object* v___x_970_; 
v___x_945_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_946_ = lean_ctor_get(v___x_945_, 1);
v_toEnvExtension_947_ = lean_ctor_get(v_snd_946_, 0);
v_asyncMode_948_ = lean_ctor_get(v_toEnvExtension_947_, 2);
v___x_949_ = lean_box(0);
v___x_950_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_940_, v_toEnvExtension_947_, v_env_944_, v_asyncMode_948_, v___x_949_);
v_importedEntries_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_importedEntries_951_);
v_state_952_ = lean_ctor_get(v___x_950_, 1);
lean_inc(v_state_952_);
lean_dec(v___x_950_);
v___x_970_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_952_, v_incorrectName_943_);
lean_dec(v_state_952_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_NameSet_empty;
v___y_954_ = v___x_971_;
goto v___jp_953_;
}
else
{
lean_object* v_val_972_; 
v_val_972_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v___x_970_, 1);
v___y_954_ = v_val_972_;
goto v___jp_953_;
}
v___jp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get_size(v_importedEntries_951_);
v___x_957_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_958_ = lean_nat_dec_lt(v___x_955_, v___x_956_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_importedEntries_951_);
lean_dec_ref(v___f_942_);
v___x_959_ = lean_apply_2(v_toPure_941_, lean_box(0), v___y_954_);
return v___x_959_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = lean_nat_dec_le(v___x_956_, v___x_956_);
if (v___x_960_ == 0)
{
if (v___x_958_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_importedEntries_951_);
lean_dec_ref(v___f_942_);
v___x_961_ = lean_apply_2(v_toPure_941_, lean_box(0), v___y_954_);
return v___x_961_;
}
else
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_956_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_957_, v___f_942_, v_importedEntries_951_, v___x_962_, v___x_963_, v___y_954_);
v___x_965_ = lean_apply_2(v_toPure_941_, lean_box(0), v___x_964_);
return v___x_965_;
}
}
else
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_956_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_957_, v___f_942_, v_importedEntries_951_, v___x_966_, v___x_967_, v___y_954_);
v___x_969_ = lean_apply_2(v_toPure_941_, lean_box(0), v___x_968_);
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg___lam__0___boxed(lean_object* v___x_973_, lean_object* v_toPure_974_, lean_object* v___f_975_, lean_object* v_incorrectName_976_, lean_object* v_env_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_getSuggestions___redArg___lam__0(v___x_973_, v_toPure_974_, v___f_975_, v_incorrectName_976_, v_env_977_);
lean_dec(v_incorrectName_976_);
lean_dec_ref(v___x_973_);
return v_res_978_;
}
}
static lean_object* _init_l_Lean_getSuggestions___redArg___closed__2(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_box(1);
v___x_982_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___redArg(lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_incorrectName_985_){
_start:
{
lean_object* v_toApplicative_986_; lean_object* v_toBind_987_; lean_object* v_getEnv_988_; lean_object* v_toPure_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___f_994_; lean_object* v___x_995_; 
v_toApplicative_986_ = lean_ctor_get(v_inst_983_, 0);
lean_inc_ref(v_toApplicative_986_);
v_toBind_987_ = lean_ctor_get(v_inst_983_, 1);
lean_inc(v_toBind_987_);
lean_dec_ref(v_inst_983_);
v_getEnv_988_ = lean_ctor_get(v_inst_984_, 0);
lean_inc(v_getEnv_988_);
lean_dec_ref(v_inst_984_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_inc(v_toPure_989_);
lean_dec_ref(v_toApplicative_986_);
v___f_990_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
v___f_991_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__1));
lean_inc(v_incorrectName_985_);
v___f_992_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_992_, 0, v_incorrectName_985_);
lean_closure_set(v___f_992_, 1, v___f_990_);
lean_closure_set(v___f_992_, 2, v___f_991_);
v___x_993_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___f_994_ = lean_alloc_closure((void*)(l_Lean_getSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_994_, 0, v___x_993_);
lean_closure_set(v___f_994_, 1, v_toPure_989_);
lean_closure_set(v___f_994_, 2, v___f_992_);
lean_closure_set(v___f_994_, 3, v_incorrectName_985_);
v___x_995_ = lean_apply_4(v_toBind_987_, lean_box(0), lean_box(0), v_getEnv_988_, v___f_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions(lean_object* v_m_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_incorrectName_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_getSuggestions___redArg(v_inst_997_, v_inst_998_, v_incorrectName_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1(lean_object* v_trueName_1001_, lean_object* v___f_1002_, lean_object* v___f_1003_, lean_object* v_x1_1004_, lean_object* v_x2_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_array_get_size(v_x2_1005_);
v___x_1008_ = lean_nat_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec_ref(v___f_1003_);
lean_dec_ref(v___f_1002_);
lean_dec(v_trueName_1001_);
return v_x1_1004_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_sub(v___x_1007_, v___x_1009_);
v___x_1011_ = lean_nat_dec_le(v___x_1006_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_dec(v___x_1010_);
lean_dec_ref(v___f_1003_);
lean_dec_ref(v___f_1002_);
lean_dec(v_trueName_1001_);
return v_x1_1004_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_trueName_1001_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__1));
v___x_1015_ = l_Array_binSearchAux___redArg(v___f_1002_, v___x_1014_, v_x2_1005_, v___x_1013_, v___x_1006_, v___x_1010_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_dec_ref(v___f_1003_);
return v_x1_1004_;
}
else
{
lean_object* v_val_1016_; lean_object* v_snd_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_val_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v_snd_1017_ = lean_ctor_get(v_val_1016_, 1);
lean_inc(v_snd_1017_);
lean_dec(v_val_1016_);
v___x_1018_ = lean_array_get_size(v_snd_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1020_ = lean_nat_dec_lt(v___x_1006_, v___x_1018_);
if (v___x_1020_ == 0)
{
lean_dec(v_snd_1017_);
lean_dec_ref(v___f_1003_);
return v_x1_1004_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1018_, v___x_1018_);
if (v___x_1021_ == 0)
{
if (v___x_1020_ == 0)
{
lean_dec(v_snd_1017_);
lean_dec_ref(v___f_1003_);
return v_x1_1004_;
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1018_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1019_, v___f_1003_, v_snd_1017_, v___x_1022_, v___x_1023_, v_x1_1004_);
return v___x_1024_;
}
}
else
{
size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1018_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1019_, v___f_1003_, v_snd_1017_, v___x_1025_, v___x_1026_, v_x1_1004_);
return v___x_1027_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__1___boxed(lean_object* v_trueName_1028_, lean_object* v___f_1029_, lean_object* v___f_1030_, lean_object* v_x1_1031_, lean_object* v_x2_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_getStoredSuggestions___redArg___lam__1(v_trueName_1028_, v___f_1029_, v___f_1030_, v_x1_1031_, v_x2_1032_);
lean_dec_ref(v_x2_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0(lean_object* v___x_1034_, lean_object* v_toPure_1035_, lean_object* v___f_1036_, lean_object* v_trueName_1037_, lean_object* v_env_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v_fst_1040_; lean_object* v_toEnvExtension_1041_; lean_object* v_asyncMode_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_importedEntries_1045_; lean_object* v_state_1046_; lean_object* v___y_1048_; lean_object* v___x_1064_; 
v___x_1039_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_fst_1040_ = lean_ctor_get(v___x_1039_, 0);
v_toEnvExtension_1041_ = lean_ctor_get(v_fst_1040_, 0);
v_asyncMode_1042_ = lean_ctor_get(v_toEnvExtension_1041_, 2);
v___x_1043_ = lean_box(0);
v___x_1044_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1034_, v_toEnvExtension_1041_, v_env_1038_, v_asyncMode_1042_, v___x_1043_);
v_importedEntries_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc_ref(v_importedEntries_1045_);
v_state_1046_ = lean_ctor_get(v___x_1044_, 1);
lean_inc(v_state_1046_);
lean_dec(v___x_1044_);
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1046_, v_trueName_1037_);
lean_dec(v_state_1046_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_NameSet_empty;
v___y_1048_ = v___x_1065_;
goto v___jp_1047_;
}
else
{
lean_object* v_val_1066_; 
v_val_1066_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v___x_1064_, 1);
v___y_1048_ = v_val_1066_;
goto v___jp_1047_;
}
v___jp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = lean_array_get_size(v_importedEntries_1045_);
v___x_1051_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__11));
v___x_1052_ = lean_nat_dec_lt(v___x_1049_, v___x_1050_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v_importedEntries_1045_);
lean_dec_ref(v___f_1036_);
v___x_1053_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___y_1048_);
return v___x_1053_;
}
else
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_nat_dec_le(v___x_1050_, v___x_1050_);
if (v___x_1054_ == 0)
{
if (v___x_1052_ == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v_importedEntries_1045_);
lean_dec_ref(v___f_1036_);
v___x_1055_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___y_1048_);
return v___x_1055_;
}
else
{
size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = ((size_t)0ULL);
v___x_1057_ = lean_usize_of_nat(v___x_1050_);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1051_, v___f_1036_, v_importedEntries_1045_, v___x_1056_, v___x_1057_, v___y_1048_);
v___x_1059_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1058_);
return v___x_1059_;
}
}
else
{
size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1050_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1051_, v___f_1036_, v_importedEntries_1045_, v___x_1060_, v___x_1061_, v___y_1048_);
v___x_1063_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1062_);
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg___lam__0___boxed(lean_object* v___x_1067_, lean_object* v_toPure_1068_, lean_object* v___f_1069_, lean_object* v_trueName_1070_, lean_object* v_env_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_getStoredSuggestions___redArg___lam__0(v___x_1067_, v_toPure_1068_, v___f_1069_, v_trueName_1070_, v_env_1071_);
lean_dec(v_trueName_1070_);
lean_dec_ref(v___x_1067_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions___redArg(lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_trueName_1075_){
_start:
{
lean_object* v_toApplicative_1076_; lean_object* v_toBind_1077_; lean_object* v_getEnv_1078_; lean_object* v_toPure_1079_; lean_object* v___f_1080_; lean_object* v___f_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v_toApplicative_1076_ = lean_ctor_get(v_inst_1073_, 0);
lean_inc_ref(v_toApplicative_1076_);
v_toBind_1077_ = lean_ctor_get(v_inst_1073_, 1);
lean_inc(v_toBind_1077_);
lean_dec_ref(v_inst_1073_);
v_getEnv_1078_ = lean_ctor_get(v_inst_1074_, 0);
lean_inc(v_getEnv_1078_);
lean_dec_ref(v_inst_1074_);
v_toPure_1079_ = lean_ctor_get(v_toApplicative_1076_, 1);
lean_inc(v_toPure_1079_);
lean_dec_ref(v_toApplicative_1076_);
v___f_1080_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__0));
v___f_1081_ = ((lean_object*)(l_Lean_getSuggestions___redArg___closed__1));
lean_inc(v_trueName_1075_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1082_, 0, v_trueName_1075_);
lean_closure_set(v___f_1082_, 1, v___f_1080_);
lean_closure_set(v___f_1082_, 2, v___f_1081_);
v___x_1083_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_getStoredSuggestions___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1084_, 0, v___x_1083_);
lean_closure_set(v___f_1084_, 1, v_toPure_1079_);
lean_closure_set(v___f_1084_, 2, v___f_1082_);
lean_closure_set(v___f_1084_, 3, v_trueName_1075_);
v___x_1085_ = lean_apply_4(v_toBind_1077_, lean_box(0), lean_box(0), v_getEnv_1078_, v___f_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStoredSuggestions(lean_object* v_m_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_trueName_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_getStoredSuggestions___redArg(v_inst_1087_, v_inst_1088_, v_trueName_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0));
v___x_1094_ = lean_string_append(v___x_1093_, v_x_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object* v_x_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(v_x_1095_);
lean_dec_ref(v_x_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object* v___x_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, size_t v_sz_1104_, size_t v_i_1105_, lean_object* v_bs_1106_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_usize_dec_lt(v_i_1105_, v_sz_1104_);
if (v___x_1107_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
return v_bs_1106_;
}
else
{
lean_object* v_v_1108_; lean_object* v___x_1109_; lean_object* v_bs_x27_1110_; lean_object* v___y_1112_; 
v_v_1108_ = lean_array_uget(v_bs_1106_, v_i_1105_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v_bs_x27_1110_ = lean_array_uset(v_bs_1106_, v_i_1105_, v___x_1109_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_inc(v_v_1108_);
v___y_1112_ = v_v_1108_;
goto v___jp_1111_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; uint8_t v___x_1138_; 
v_val_1130_ = lean_ctor_get(v___x_1100_, 0);
v___x_1131_ = lean_box(0);
lean_inc(v_v_1108_);
v___x_1132_ = l_Lean_Name_replacePrefix(v_v_1108_, v_val_1130_, v___x_1131_);
v___x_1133_ = l_Lean_Options_empty;
lean_inc(v___x_1132_);
lean_inc(v___x_1103_);
lean_inc(v___x_1102_);
lean_inc_ref(v___x_1101_);
v___x_1134_ = l_Lean_ResolveName_resolveGlobalName(v___x_1101_, v___x_1133_, v___x_1102_, v___x_1103_, v___x_1132_);
v___x_1135_ = l_List_lengthTR___redArg(v___x_1134_);
lean_dec(v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_dec_eq(v___x_1135_, v___x_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_bool_not(v___x_1137_);
if (v___x_1138_ == 0)
{
v___y_1112_ = v___x_1132_;
goto v___jp_1111_;
}
else
{
lean_dec(v___x_1132_);
lean_inc(v_v_1108_);
v___y_1112_ = v_v_1108_;
goto v___jp_1111_;
}
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1113_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_1112_, v___x_1107_);
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1117_ = 0;
v___x_1118_ = l_Lean_MessageData_ofConstName(v_v_1108_, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1116_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1116_);
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1));
v___x_1123_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1114_);
lean_ctor_set(v___x_1123_, 1, v___x_1115_);
lean_ctor_set(v___x_1123_, 2, v___x_1115_);
lean_ctor_set(v___x_1123_, 3, v___x_1115_);
lean_ctor_set(v___x_1123_, 4, v___x_1121_);
lean_ctor_set(v___x_1123_, 5, v___x_1122_);
v___x_1124_ = 0;
v___x_1125_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1115_);
lean_ctor_set(v___x_1125_, 2, v___x_1115_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*3, v___x_1124_);
v___x_1126_ = ((size_t)1ULL);
v___x_1127_ = lean_usize_add(v_i_1105_, v___x_1126_);
v___x_1128_ = lean_array_uset(v_bs_x27_1110_, v_i_1105_, v___x_1125_);
v_i_1105_ = v___x_1127_;
v_bs_1106_ = v___x_1128_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v_sz_1143_, lean_object* v_i_1144_, lean_object* v_bs_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1143_);
lean_dec(v_sz_1143_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_1139_, v___x_1140_, v___x_1141_, v___x_1142_, v_sz_boxed_1146_, v_i_boxed_1147_, v_bs_1145_);
lean_dec(v___x_1139_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(lean_object* v_msgData_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v_env_1156_; lean_object* v___x_1157_; lean_object* v_mctx_1158_; lean_object* v_lctx_1159_; lean_object* v_options_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1155_ = lean_st_ref_get(v___y_1153_);
v_env_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_env_1156_);
lean_dec(v___x_1155_);
v___x_1157_ = lean_st_ref_get(v___y_1151_);
v_mctx_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_ref(v_mctx_1158_);
lean_dec(v___x_1157_);
v_lctx_1159_ = lean_ctor_get(v___y_1150_, 2);
v_options_1160_ = lean_ctor_get(v___y_1152_, 2);
lean_inc_ref(v_options_1160_);
lean_inc_ref(v_lctx_1159_);
v___x_1161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1161_, 0, v_env_1156_);
lean_ctor_set(v___x_1161_, 1, v_mctx_1158_);
lean_ctor_set(v___x_1161_, 2, v_lctx_1159_);
lean_ctor_set(v___x_1161_, 3, v_options_1160_);
v___x_1162_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_msgData_1149_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1170_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_box(1);
v___x_1172_ = l_Lean_MessageData_ofFormat(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2));
v___x_1177_ = l_Lean_MessageData_ofFormat(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
return v_x_1178_;
}
else
{
lean_object* v_head_1180_; lean_object* v_tail_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1203_; 
v_head_1180_ = lean_ctor_get(v_x_1179_, 0);
v_tail_1181_ = lean_ctor_get(v_x_1179_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1183_ = v_x_1179_;
v_isShared_1184_ = v_isSharedCheck_1203_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_tail_1181_);
lean_inc(v_head_1180_);
lean_dec(v_x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1203_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_before_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1201_; 
v_before_1185_ = lean_ctor_get(v_head_1180_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_head_1180_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_head_1180_, 1);
lean_dec(v_unused_1202_);
v___x_1187_ = v_head_1180_;
v_isShared_1188_ = v_isSharedCheck_1201_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_before_1185_);
lean_dec(v_head_1180_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1201_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 7);
lean_ctor_set(v___x_1187_, 1, v___x_1189_);
lean_ctor_set(v___x_1187_, 0, v_x_1178_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_x_1178_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 7);
lean_ctor_set(v___x_1183_, 1, v___x_1192_);
lean_ctor_set(v___x_1183_, 0, v___x_1191_);
v___x_1194_ = v___x_1183_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = l_Lean_MessageData_ofSyntax(v_before_1185_);
v___x_1196_ = l_Lean_indentD(v___x_1195_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1194_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v_x_1178_ = v___x_1197_;
v_x_1179_ = v_tail_1181_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(lean_object* v_opts_1204_, lean_object* v_opt_1205_){
_start:
{
lean_object* v_name_1206_; lean_object* v_defValue_1207_; lean_object* v_map_1208_; lean_object* v___x_1209_; 
v_name_1206_ = lean_ctor_get(v_opt_1205_, 0);
v_defValue_1207_ = lean_ctor_get(v_opt_1205_, 1);
v_map_1208_ = lean_ctor_get(v_opts_1204_, 0);
v___x_1209_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1208_, v_name_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_unbox(v_defValue_1207_);
return v___x_1210_;
}
else
{
lean_object* v_val_1211_; 
v_val_1211_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v___x_1209_, 1);
if (lean_obj_tag(v_val_1211_) == 1)
{
uint8_t v_v_1212_; 
v_v_1212_ = lean_ctor_get_uint8(v_val_1211_, 0);
lean_dec_ref_known(v_val_1211_, 0);
return v_v_1212_;
}
else
{
uint8_t v___x_1213_; 
lean_dec(v_val_1211_);
v___x_1213_ = lean_unbox(v_defValue_1207_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(lean_object* v_opts_1214_, lean_object* v_opt_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_1214_, v_opt_1215_);
lean_dec_ref(v_opt_1215_);
lean_dec_ref(v_opts_1214_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1));
v___x_1222_ = l_Lean_MessageData_ofFormat(v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(lean_object* v_msgData_1223_, lean_object* v_macroStack_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_options_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; uint8_t v___x_1230_; 
v_options_1227_ = lean_ctor_get(v___y_1225_, 2);
v___x_1228_ = l_Lean_Elab_pp_macroStack;
v___x_1229_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_options_1227_, v___x_1228_);
v___x_1230_ = lean_bool_not(v___x_1229_);
if (v___x_1230_ == 0)
{
if (lean_obj_tag(v_macroStack_1224_) == 0)
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_msgData_1223_);
return v___x_1231_;
}
else
{
lean_object* v_head_1232_; lean_object* v_after_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1248_; 
v_head_1232_ = lean_ctor_get(v_macroStack_1224_, 0);
lean_inc(v_head_1232_);
v_after_1233_ = lean_ctor_get(v_head_1232_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_head_1232_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_head_1232_, 0);
lean_dec(v_unused_1249_);
v___x_1235_ = v_head_1232_;
v_isShared_1236_ = v_isSharedCheck_1248_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_after_1233_);
lean_dec(v_head_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1248_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set_tag(v___x_1235_, 7);
lean_ctor_set(v___x_1235_, 1, v___x_1237_);
lean_ctor_set(v___x_1235_, 0, v_msgData_1223_);
v___x_1239_ = v___x_1235_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_msgData_1223_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_msgData_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1240_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_MessageData_ofSyntax(v_after_1233_);
v___x_1243_ = l_Lean_indentD(v___x_1242_);
v_msgData_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1244_, 0, v___x_1241_);
lean_ctor_set(v_msgData_1244_, 1, v___x_1243_);
v___x_1245_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(v_msgData_1244_, v_macroStack_1224_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
}
else
{
lean_object* v___x_1250_; 
lean_dec(v_macroStack_1224_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_msgData_1223_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_1251_, lean_object* v_macroStack_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1251_, v_macroStack_1252_, v___y_1253_);
lean_dec_ref(v___y_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(lean_object* v_msg_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_ref_1264_; lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v_macroStack_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_ref_1264_ = lean_ctor_get(v___y_1261_, 5);
v___x_1265_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msg_1256_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref(v___x_1265_);
v_macroStack_1267_ = lean_ctor_get(v___y_1257_, 1);
v___x_1268_ = l_Lean_Elab_getBetterRef(v_ref_1264_, v_macroStack_1267_);
lean_inc(v_macroStack_1267_);
v___x_1269_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_a_1266_, v_macroStack_1267_, v___y_1261_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1268_);
lean_ctor_set(v___x_1274_, 1, v_a_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(lean_object* v_ref_1288_, lean_object* v_msg_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_fileName_1297_; lean_object* v_fileMap_1298_; lean_object* v_options_1299_; lean_object* v_currRecDepth_1300_; lean_object* v_maxRecDepth_1301_; lean_object* v_ref_1302_; lean_object* v_currNamespace_1303_; lean_object* v_openDecls_1304_; lean_object* v_initHeartbeats_1305_; lean_object* v_maxHeartbeats_1306_; lean_object* v_quotContext_1307_; lean_object* v_currMacroScope_1308_; uint8_t v_diag_1309_; lean_object* v_cancelTk_x3f_1310_; uint8_t v_suppressElabErrors_1311_; lean_object* v_inheritedTraceOptions_1312_; lean_object* v_ref_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_fileName_1297_ = lean_ctor_get(v___y_1294_, 0);
v_fileMap_1298_ = lean_ctor_get(v___y_1294_, 1);
v_options_1299_ = lean_ctor_get(v___y_1294_, 2);
v_currRecDepth_1300_ = lean_ctor_get(v___y_1294_, 3);
v_maxRecDepth_1301_ = lean_ctor_get(v___y_1294_, 4);
v_ref_1302_ = lean_ctor_get(v___y_1294_, 5);
v_currNamespace_1303_ = lean_ctor_get(v___y_1294_, 6);
v_openDecls_1304_ = lean_ctor_get(v___y_1294_, 7);
v_initHeartbeats_1305_ = lean_ctor_get(v___y_1294_, 8);
v_maxHeartbeats_1306_ = lean_ctor_get(v___y_1294_, 9);
v_quotContext_1307_ = lean_ctor_get(v___y_1294_, 10);
v_currMacroScope_1308_ = lean_ctor_get(v___y_1294_, 11);
v_diag_1309_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*14);
v_cancelTk_x3f_1310_ = lean_ctor_get(v___y_1294_, 12);
v_suppressElabErrors_1311_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1312_ = lean_ctor_get(v___y_1294_, 13);
v_ref_1313_ = l_Lean_replaceRef(v_ref_1288_, v_ref_1302_);
lean_inc_ref(v_inheritedTraceOptions_1312_);
lean_inc(v_cancelTk_x3f_1310_);
lean_inc(v_currMacroScope_1308_);
lean_inc(v_quotContext_1307_);
lean_inc(v_maxHeartbeats_1306_);
lean_inc(v_initHeartbeats_1305_);
lean_inc(v_openDecls_1304_);
lean_inc(v_currNamespace_1303_);
lean_inc(v_maxRecDepth_1301_);
lean_inc(v_currRecDepth_1300_);
lean_inc_ref(v_options_1299_);
lean_inc_ref(v_fileMap_1298_);
lean_inc_ref(v_fileName_1297_);
v___x_1314_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1314_, 0, v_fileName_1297_);
lean_ctor_set(v___x_1314_, 1, v_fileMap_1298_);
lean_ctor_set(v___x_1314_, 2, v_options_1299_);
lean_ctor_set(v___x_1314_, 3, v_currRecDepth_1300_);
lean_ctor_set(v___x_1314_, 4, v_maxRecDepth_1301_);
lean_ctor_set(v___x_1314_, 5, v_ref_1313_);
lean_ctor_set(v___x_1314_, 6, v_currNamespace_1303_);
lean_ctor_set(v___x_1314_, 7, v_openDecls_1304_);
lean_ctor_set(v___x_1314_, 8, v_initHeartbeats_1305_);
lean_ctor_set(v___x_1314_, 9, v_maxHeartbeats_1306_);
lean_ctor_set(v___x_1314_, 10, v_quotContext_1307_);
lean_ctor_set(v___x_1314_, 11, v_currMacroScope_1308_);
lean_ctor_set(v___x_1314_, 12, v_cancelTk_x3f_1310_);
lean_ctor_set(v___x_1314_, 13, v_inheritedTraceOptions_1312_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*14, v_diag_1309_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*14 + 1, v_suppressElabErrors_1311_);
v___x_1315_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___x_1314_, v___y_1295_);
lean_dec_ref_known(v___x_1314_, 14);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1316_, v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v_ref_1316_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10));
v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(lean_object* v_msg_1347_, lean_object* v_declHint_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v_env_1352_; uint8_t v___y_1354_; uint8_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1351_ = lean_st_ref_get(v___y_1349_);
v_env_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_ref(v_env_1352_);
lean_dec(v___x_1351_);
v___x_1410_ = l_Lean_Name_isAnonymous(v_declHint_1348_);
v___x_1411_ = lean_bool_not(v___x_1410_);
if (v___x_1411_ == 0)
{
v___y_1354_ = v___x_1411_;
goto v___jp_1353_;
}
else
{
uint8_t v_isExporting_1412_; 
v_isExporting_1412_ = lean_ctor_get_uint8(v_env_1352_, sizeof(void*)*8);
v___y_1354_ = v_isExporting_1412_;
goto v___jp_1353_;
}
v___jp_1353_:
{
if (v___y_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_dec_ref(v_env_1352_);
lean_dec(v_declHint_1348_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_msg_1347_);
return v___x_1355_;
}
else
{
uint8_t v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = 0;
lean_inc_ref(v_env_1352_);
v___x_1357_ = l_Lean_Environment_setExporting(v_env_1352_, v___x_1356_);
lean_inc(v_declHint_1348_);
lean_inc_ref(v___x_1357_);
v___x_1358_ = l_Lean_Environment_contains(v___x_1357_, v_declHint_1348_, v___y_1354_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v___x_1357_);
lean_dec_ref(v_env_1352_);
lean_dec(v_declHint_1348_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_msg_1347_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_c_1365_; lean_object* v___x_1366_; 
v___x_1360_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1362_ = l_Lean_Options_empty;
v___x_1363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1357_);
lean_ctor_set(v___x_1363_, 1, v___x_1360_);
lean_ctor_set(v___x_1363_, 2, v___x_1361_);
lean_ctor_set(v___x_1363_, 3, v___x_1362_);
lean_inc(v_declHint_1348_);
v___x_1364_ = l_Lean_MessageData_ofConstName(v_declHint_1348_, v___x_1356_);
v_c_1365_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1365_, 0, v___x_1363_);
lean_ctor_set(v_c_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1352_, v_declHint_1348_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v_env_1352_);
lean_dec(v_declHint_1348_);
v___x_1367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_c_1365_);
v___x_1369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_MessageData_note(v___x_1370_);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_msg_1347_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
else
{
lean_object* v_val_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1409_; 
v_val_1374_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1376_ = v___x_1366_;
v_isShared_1377_ = v_isSharedCheck_1409_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_val_1374_);
lean_dec(v___x_1366_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1409_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_mod_1381_; uint8_t v___x_1382_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Lean_Environment_header(v_env_1352_);
lean_dec_ref(v_env_1352_);
v___x_1380_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1379_);
v_mod_1381_ = lean_array_get(v___x_1378_, v___x_1380_, v_val_1374_);
lean_dec(v_val_1374_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = l_Lean_isPrivateName(v_declHint_1348_);
lean_dec(v_declHint_1348_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v_c_1365_);
v___x_1385_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = l_Lean_MessageData_ofName(v_mod_1381_);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = l_Lean_MessageData_note(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_msg_1347_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1392_);
v___x_1394_ = v___x_1376_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_c_1365_);
v___x_1398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11);
v___x_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_MessageData_ofName(v_mod_1381_);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_MessageData_note(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_msg_1347_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1405_);
v___x_1407_ = v___x_1376_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1413_, lean_object* v_declHint_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1413_, v_declHint_1414_, v___y_1415_);
lean_dec(v___y_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(lean_object* v_msg_1418_, lean_object* v_declHint_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v___x_1427_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1418_, v_declHint_1419_, v___y_1425_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = l_Lean_unknownIdentifierMessageTag;
v___x_1433_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1433_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(lean_object* v_msg_1438_, lean_object* v_declHint_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1438_, v_declHint_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(lean_object* v_ref_1448_, lean_object* v_msg_1449_, lean_object* v_declHint_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1460_; 
v___x_1458_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1449_, v_declHint_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1448_, v_a_1459_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v_declHint_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1461_, v_msg_1462_, v_declHint_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_ref_1461_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object* v_as_1472_, lean_object* v_k_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_m_1478_; lean_object* v_a_1479_; uint8_t v___x_1480_; 
v___x_1476_ = lean_nat_add(v_x_1474_, v_x_1475_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v_m_1478_ = lean_nat_shiftr(v___x_1476_, v___x_1477_);
lean_dec(v___x_1476_);
v_a_1479_ = lean_array_fget_borrowed(v_as_1472_, v_m_1478_);
v___x_1480_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_1479_, v_k_1473_);
if (v___x_1480_ == 0)
{
uint8_t v___x_1481_; 
lean_dec(v_x_1475_);
v___x_1481_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_k_1473_, v_a_1479_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec(v_m_1478_);
lean_dec(v_x_1474_);
lean_inc(v_a_1479_);
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1479_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_nat_dec_eq(v_m_1478_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = lean_nat_sub(v_m_1478_, v___x_1477_);
lean_dec(v_m_1478_);
v___x_1486_ = lean_nat_dec_lt(v___x_1485_, v_x_1474_);
if (v___x_1486_ == 0)
{
v_x_1475_ = v___x_1485_;
goto _start;
}
else
{
lean_object* v___x_1488_; 
lean_dec(v___x_1485_);
lean_dec(v_x_1474_);
v___x_1488_ = lean_box(0);
return v___x_1488_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec(v_m_1478_);
lean_dec(v_x_1474_);
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
}
}
else
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
lean_dec(v_x_1474_);
v___x_1490_ = lean_nat_add(v_m_1478_, v___x_1477_);
lean_dec(v_m_1478_);
v___x_1491_ = lean_nat_dec_le(v___x_1490_, v_x_1475_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec(v___x_1490_);
lean_dec(v_x_1475_);
v___x_1492_ = lean_box(0);
return v___x_1492_;
}
else
{
v_x_1474_ = v___x_1490_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object* v_as_1494_, lean_object* v_k_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1494_, v_k_1495_, v_x_1496_, v_x_1497_);
lean_dec_ref(v_k_1495_);
lean_dec_ref(v_as_1494_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object* v_incorrectName_1499_, lean_object* v_as_1500_, size_t v_i_1501_, size_t v_stop_1502_, lean_object* v_b_1503_){
_start:
{
lean_object* v___y_1505_; uint8_t v___x_1509_; 
v___x_1509_ = lean_usize_dec_eq(v_i_1501_, v_stop_1502_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1510_ = lean_array_uget_borrowed(v_as_1500_, v_i_1501_);
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = lean_array_get_size(v___x_1510_);
v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
v___y_1505_ = v_b_1503_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_nat_sub(v___x_1512_, v___x_1514_);
v___x_1516_ = lean_nat_dec_le(v___x_1511_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_dec(v___x_1515_);
v___y_1505_ = v_b_1503_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
lean_inc(v_incorrectName_1499_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_incorrectName_1499_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v___x_1510_, v___x_1518_, v___x_1511_, v___x_1515_);
lean_dec_ref_known(v___x_1518_, 2);
if (lean_obj_tag(v___x_1519_) == 0)
{
v___y_1505_ = v_b_1503_;
goto v___jp_1504_;
}
else
{
lean_object* v_val_1520_; lean_object* v_snd_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v_snd_1521_ = lean_ctor_get(v_val_1520_, 1);
lean_inc(v_snd_1521_);
lean_dec(v_val_1520_);
v___x_1522_ = lean_array_get_size(v_snd_1521_);
v___x_1523_ = lean_nat_dec_lt(v___x_1511_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec(v_snd_1521_);
v___y_1505_ = v_b_1503_;
goto v___jp_1504_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_nat_dec_le(v___x_1522_, v___x_1522_);
if (v___x_1524_ == 0)
{
if (v___x_1523_ == 0)
{
lean_dec(v_snd_1521_);
v___y_1505_ = v_b_1503_;
goto v___jp_1504_;
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1522_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1521_, v___x_1525_, v___x_1526_, v_b_1503_);
lean_dec(v_snd_1521_);
v___y_1505_ = v___x_1527_;
goto v___jp_1504_;
}
}
else
{
size_t v___x_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = lean_usize_of_nat(v___x_1522_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1521_, v___x_1528_, v___x_1529_, v_b_1503_);
lean_dec(v_snd_1521_);
v___y_1505_ = v___x_1530_;
goto v___jp_1504_;
}
}
}
}
}
}
else
{
lean_dec(v_incorrectName_1499_);
return v_b_1503_;
}
v___jp_1504_:
{
size_t v___x_1506_; size_t v___x_1507_; 
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1501_, v___x_1506_);
v_i_1501_ = v___x_1507_;
v_b_1503_ = v___y_1505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object* v_incorrectName_1531_, lean_object* v_as_1532_, lean_object* v_i_1533_, lean_object* v_stop_1534_, lean_object* v_b_1535_){
_start:
{
size_t v_i_boxed_1536_; size_t v_stop_boxed_1537_; lean_object* v_res_1538_; 
v_i_boxed_1536_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_stop_boxed_1537_ = lean_unbox_usize(v_stop_1534_);
lean_dec(v_stop_1534_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1531_, v_as_1532_, v_i_boxed_1536_, v_stop_boxed_1537_, v_b_1535_);
lean_dec_ref(v_as_1532_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object* v_incorrectName_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v_env_1543_; lean_object* v___x_1544_; lean_object* v_snd_1545_; lean_object* v_toEnvExtension_1546_; lean_object* v_asyncMode_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_importedEntries_1551_; lean_object* v_state_1552_; lean_object* v___y_1554_; lean_object* v___x_1569_; 
v___x_1542_ = lean_st_ref_get(v___y_1540_);
v_env_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc_ref(v_env_1543_);
lean_dec(v___x_1542_);
v___x_1544_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_1545_ = lean_ctor_get(v___x_1544_, 1);
v_toEnvExtension_1546_ = lean_ctor_get(v_snd_1545_, 0);
v_asyncMode_1547_ = lean_ctor_get(v_toEnvExtension_1546_, 2);
v___x_1548_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___x_1549_ = lean_box(0);
v___x_1550_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1548_, v_toEnvExtension_1546_, v_env_1543_, v_asyncMode_1547_, v___x_1549_);
v_importedEntries_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc_ref(v_importedEntries_1551_);
v_state_1552_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_state_1552_);
lean_dec(v___x_1550_);
v___x_1569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1552_, v_incorrectName_1539_);
lean_dec(v_state_1552_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_NameSet_empty;
v___y_1554_ = v___x_1570_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1571_; 
v_val_1571_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1571_);
lean_dec_ref_known(v___x_1569_, 1);
v___y_1554_ = v_val_1571_;
goto v___jp_1553_;
}
v___jp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_importedEntries_1551_);
v___x_1557_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_dec_ref(v_importedEntries_1551_);
lean_dec(v_incorrectName_1539_);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___y_1554_);
return v___x_1558_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_le(v___x_1556_, v___x_1556_);
if (v___x_1559_ == 0)
{
if (v___x_1557_ == 0)
{
lean_object* v___x_1560_; 
lean_dec_ref(v_importedEntries_1551_);
lean_dec(v_incorrectName_1539_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___y_1554_);
return v___x_1560_;
}
else
{
size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = lean_usize_of_nat(v___x_1556_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1539_, v_importedEntries_1551_, v___x_1561_, v___x_1562_, v___y_1554_);
lean_dec_ref(v_importedEntries_1551_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
else
{
size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = lean_usize_of_nat(v___x_1556_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1539_, v_importedEntries_1551_, v___x_1565_, v___x_1566_, v___y_1554_);
lean_dec_ref(v_importedEntries_1551_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object* v_incorrectName_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1572_, v___y_1573_);
lean_dec(v___y_1573_);
return v_res_1575_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg(lean_object* v_constName_1594_, lean_object* v_idOrConst_1595_, lean_object* v_declHint_1596_, lean_object* v_ref_x3f_1597_, lean_object* v_extraMsg_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___y_1607_; lean_object* v_hint_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___x_1675_; lean_object* v_a_1676_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1699_; 
lean_inc(v_constName_1594_);
v___x_1675_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_constName_1594_, v_a_1604_);
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
if (lean_obj_tag(v_a_1676_) == 0)
{
lean_object* v_size_1704_; 
v_size_1704_ = lean_ctor_get(v_a_1676_, 0);
lean_inc(v_size_1704_);
v___y_1699_ = v_size_1704_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_unsigned_to_nat(0u);
v___y_1699_ = v___x_1705_;
goto v___jp_1698_;
}
v___jp_1606_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1615_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1);
v___x_1616_ = l_Lean_stringToMessageData(v_idOrConst_1595_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = 0;
v___x_1621_ = l_Lean_MessageData_ofConstName(v_constName_1594_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_extraMsg_1598_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v_hint_1608_);
v___x_1627_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v___y_1607_, v___x_1626_, v_declHint_1596_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1607_);
return v___x_1627_;
}
v___jp_1628_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; size_t v_sz_1643_; size_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1638_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___y_1633_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v___y_1637_);
v___x_1641_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v_sz_1643_ = lean_array_size(v___y_1636_);
v___x_1644_ = ((size_t)0ULL);
lean_inc(v___y_1634_);
lean_inc(v___y_1630_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___y_1632_, v___y_1629_, v___y_1630_, v___y_1634_, v_sz_1643_, v___x_1644_, v___y_1636_);
lean_dec(v___y_1632_);
lean_inc(v___y_1635_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1635_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Lean_MessageData_hint(v___x_1642_, v___x_1645_, v___x_1646_, v___x_1647_, v___y_1631_, v_a_1603_, v_a_1604_);
lean_dec_ref(v___x_1645_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___y_1607_ = v___y_1635_;
v_hint_1608_ = v_a_1649_;
v___y_1609_ = v_a_1599_;
v___y_1610_ = v_a_1600_;
v___y_1611_ = v_a_1601_;
v___y_1612_ = v_a_1602_;
v___y_1613_ = v_a_1603_;
v___y_1614_ = v_a_1604_;
goto v___jp_1606_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v___y_1635_);
lean_dec_ref(v_extraMsg_1598_);
lean_dec(v_declHint_1596_);
lean_dec_ref(v_idOrConst_1595_);
lean_dec(v_constName_1594_);
v_a_1650_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1648_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
v___jp_1658_:
{
uint8_t v___x_1668_; 
v___x_1668_ = l_Lean_Name_isAnonymous(v___y_1663_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9);
v___x_1670_ = l_Lean_MessageData_ofName(v___y_1663_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___y_1629_ = v___y_1659_;
v___y_1630_ = v___y_1660_;
v___y_1631_ = v___y_1661_;
v___y_1632_ = v___y_1662_;
v___y_1633_ = v___y_1667_;
v___y_1634_ = v___y_1664_;
v___y_1635_ = v___y_1666_;
v___y_1636_ = v___y_1665_;
v___y_1637_ = v___x_1673_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1674_; 
lean_dec(v___y_1663_);
v___x_1674_ = l_Lean_MessageData_nil;
v___y_1629_ = v___y_1659_;
v___y_1630_ = v___y_1660_;
v___y_1631_ = v___y_1661_;
v___y_1632_ = v___y_1662_;
v___y_1633_ = v___y_1667_;
v___y_1634_ = v___y_1664_;
v___y_1635_ = v___y_1666_;
v___y_1636_ = v___y_1665_;
v___y_1637_ = v___x_1674_;
goto v___jp_1628_;
}
}
v___jp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = lean_array_get_size(v___y_1678_);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_nat_dec_eq(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v_env_1684_; lean_object* v_currNamespace_1685_; lean_object* v_openDecls_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1683_ = lean_st_ref_get(v_a_1604_);
v_env_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc_ref(v_env_1684_);
lean_dec(v___x_1683_);
v_currNamespace_1685_ = lean_ctor_get(v_a_1603_, 6);
v_openDecls_1686_ = lean_ctor_get(v_a_1603_, 7);
v___x_1687_ = l_Lean_Syntax_getId(v___y_1679_);
lean_inc(v_constName_1594_);
v___x_1688_ = l_Lean_Name_eraseSuffix_x3f(v_constName_1594_, v___x_1687_);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_dec_eq(v___x_1680_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11);
v___y_1659_ = v_env_1684_;
v___y_1660_ = v_currNamespace_1685_;
v___y_1661_ = v___x_1682_;
v___y_1662_ = v___x_1688_;
v___y_1663_ = v___x_1687_;
v___y_1664_ = v_openDecls_1686_;
v___y_1665_ = v___y_1678_;
v___y_1666_ = v___y_1679_;
v___y_1667_ = v___x_1691_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1692_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1693_ = lean_array_fget_borrowed(v___y_1678_, v___x_1681_);
lean_inc(v___x_1693_);
v___x_1694_ = l_Lean_MessageData_ofConstName(v___x_1693_, v___x_1682_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1692_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v___x_1692_);
v___y_1659_ = v_env_1684_;
v___y_1660_ = v_currNamespace_1685_;
v___y_1661_ = v___x_1682_;
v___y_1662_ = v___x_1688_;
v___y_1663_ = v___x_1687_;
v___y_1664_ = v_openDecls_1686_;
v___y_1665_ = v___y_1678_;
v___y_1666_ = v___y_1679_;
v___y_1667_ = v___x_1696_;
goto v___jp_1658_;
}
}
else
{
lean_object* v___x_1697_; 
lean_dec_ref(v___y_1678_);
v___x_1697_ = l_Lean_MessageData_nil;
v___y_1607_ = v___y_1679_;
v_hint_1608_ = v___x_1697_;
v___y_1609_ = v_a_1599_;
v___y_1610_ = v_a_1600_;
v___y_1611_ = v_a_1601_;
v___y_1612_ = v_a_1602_;
v___y_1613_ = v_a_1603_;
v___y_1614_ = v_a_1604_;
goto v___jp_1606_;
}
}
v___jp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_mk_empty_array_with_capacity(v___y_1699_);
lean_dec(v___y_1699_);
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_1700_, v_a_1676_);
if (lean_obj_tag(v_ref_x3f_1597_) == 0)
{
lean_object* v_ref_1702_; 
v_ref_1702_ = lean_ctor_get(v_a_1603_, 5);
lean_inc(v_ref_1702_);
v___y_1678_ = v___x_1701_;
v___y_1679_ = v_ref_1702_;
goto v___jp_1677_;
}
else
{
lean_object* v_val_1703_; 
v_val_1703_ = lean_ctor_get(v_ref_x3f_1597_, 0);
lean_inc(v_val_1703_);
lean_dec_ref_known(v_ref_x3f_1597_, 1);
v___y_1678_ = v___x_1701_;
v___y_1679_ = v_val_1703_;
goto v___jp_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(lean_object* v_constName_1706_, lean_object* v_idOrConst_1707_, lean_object* v_declHint_1708_, lean_object* v_ref_x3f_1709_, lean_object* v_extraMsg_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1706_, v_idOrConst_1707_, v_declHint_1708_, v_ref_x3f_1709_, v_extraMsg_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions(lean_object* v_00_u03b1_1719_, lean_object* v_constName_1720_, lean_object* v_idOrConst_1721_, lean_object* v_declHint_1722_, lean_object* v_ref_x3f_1723_, lean_object* v_extraMsg_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1720_, v_idOrConst_1721_, v_declHint_1722_, v_ref_x3f_1723_, v_extraMsg_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_constName_1734_, lean_object* v_idOrConst_1735_, lean_object* v_declHint_1736_, lean_object* v_ref_x3f_1737_, lean_object* v_extraMsg_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_throwUnknownNameWithSuggestions(v_00_u03b1_1733_, v_constName_1734_, v_idOrConst_1735_, v_declHint_1736_, v_ref_x3f_1737_, v_extraMsg_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(lean_object* v_incorrectName_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1747_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(lean_object* v_incorrectName_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(v_incorrectName_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_object* v_00_u03b1_1765_, lean_object* v_ref_1766_, lean_object* v_msg_1767_, lean_object* v_declHint_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1766_, v_msg_1767_, v_declHint_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(lean_object* v_00_u03b1_1777_, lean_object* v_ref_1778_, lean_object* v_msg_1779_, lean_object* v_declHint_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(v_00_u03b1_1777_, v_ref_1778_, v_msg_1779_, v_declHint_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v_ref_1778_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(lean_object* v_as_1789_, lean_object* v_k_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1789_, v_k_1790_, v_x_1791_, v_x_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(lean_object* v_as_1795_, lean_object* v_k_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(v_as_1795_, v_k_1796_, v_x_1797_, v_x_1798_, v_x_1799_);
lean_dec_ref(v_k_1796_);
lean_dec_ref(v_as_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(lean_object* v_msg_1801_, lean_object* v_declHint_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1801_, v_declHint_1802_, v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1811_, lean_object* v_declHint_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_1811_, v_declHint_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_object* v_00_u03b1_1821_, lean_object* v_ref_1822_, lean_object* v_msg_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1822_, v_msg_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1832_, lean_object* v_ref_1833_, lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(v_00_u03b1_1832_, v_ref_1833_, v_msg_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_ref_1833_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1843_, lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1853_, lean_object* v_msg_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(v_00_u03b1_1853_, v_msg_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(lean_object* v_msgData_1863_, lean_object* v_macroStack_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1863_, v_macroStack_1864_, v___y_1869_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(lean_object* v_msgData_1873_, lean_object* v_macroStack_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_1873_, v_macroStack_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1882_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(lean_object* v_exp_1883_, lean_object* v_as_1884_, size_t v_i_1885_, size_t v_stop_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_eq(v_i_1885_, v_stop_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_array_uget_borrowed(v_as_1884_, v_i_1885_);
v___x_1889_ = lean_expr_eqv(v___x_1888_, v_exp_1883_);
if (v___x_1889_ == 0)
{
size_t v___x_1890_; size_t v___x_1891_; 
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1885_, v___x_1890_);
v_i_1885_ = v___x_1891_;
goto _start;
}
else
{
return v___x_1889_;
}
}
else
{
uint8_t v___x_1893_; 
v___x_1893_ = 0;
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(lean_object* v_exp_1894_, lean_object* v_as_1895_, lean_object* v_i_1896_, lean_object* v_stop_1897_){
_start:
{
size_t v_i_boxed_1898_; size_t v_stop_boxed_1899_; uint8_t v_res_1900_; lean_object* v_r_1901_; 
v_i_boxed_1898_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_stop_boxed_1899_ = lean_unbox_usize(v_stop_1897_);
lean_dec(v_stop_1897_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1894_, v_as_1895_, v_i_boxed_1898_, v_stop_boxed_1899_);
lean_dec_ref(v_as_1895_);
lean_dec_ref(v_exp_1894_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(lean_object* v_exp_1902_, lean_object* v_x_1903_){
_start:
{
if (lean_obj_tag(v_x_1903_) == 0)
{
lean_object* v_cs_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_cs_1904_ = lean_ctor_get(v_x_1903_, 0);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_array_get_size(v_cs_1904_);
v___x_1907_ = lean_nat_dec_lt(v___x_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
return v___x_1907_;
}
else
{
if (v___x_1907_ == 0)
{
return v___x_1907_;
}
else
{
size_t v___x_1908_; size_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = ((size_t)0ULL);
v___x_1909_ = lean_usize_of_nat(v___x_1906_);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1902_, v_cs_1904_, v___x_1908_, v___x_1909_);
return v___x_1910_;
}
}
}
else
{
lean_object* v_vs_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_vs_1911_ = lean_ctor_get(v_x_1903_, 0);
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_array_get_size(v_vs_1911_);
v___x_1914_ = lean_nat_dec_lt(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
return v___x_1914_;
}
else
{
if (v___x_1914_ == 0)
{
return v___x_1914_;
}
else
{
size_t v___x_1915_; size_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = lean_usize_of_nat(v___x_1913_);
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1902_, v_vs_1911_, v___x_1915_, v___x_1916_);
return v___x_1917_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(lean_object* v_exp_1918_, lean_object* v_as_1919_, size_t v_i_1920_, size_t v_stop_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_eq(v_i_1920_, v_stop_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = lean_array_uget_borrowed(v_as_1919_, v_i_1920_);
v___x_1924_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1918_, v___x_1923_);
if (v___x_1924_ == 0)
{
size_t v___x_1925_; size_t v___x_1926_; 
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1920_, v___x_1925_);
v_i_1920_ = v___x_1926_;
goto _start;
}
else
{
return v___x_1924_;
}
}
else
{
uint8_t v___x_1928_; 
v___x_1928_ = 0;
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(lean_object* v_exp_1929_, lean_object* v_as_1930_, lean_object* v_i_1931_, lean_object* v_stop_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1932_);
lean_dec(v_stop_1932_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1929_, v_as_1930_, v_i_boxed_1933_, v_stop_boxed_1934_);
lean_dec_ref(v_as_1930_);
lean_dec_ref(v_exp_1929_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(lean_object* v_exp_1937_, lean_object* v_x_1938_){
_start:
{
uint8_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1937_, v_x_1938_);
lean_dec_ref(v_x_1938_);
lean_dec_ref(v_exp_1937_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(lean_object* v_exp_1941_, lean_object* v_t_1942_){
_start:
{
lean_object* v_root_1943_; lean_object* v_tail_1944_; uint8_t v___x_1945_; 
v_root_1943_ = lean_ctor_get(v_t_1942_, 0);
v_tail_1944_ = lean_ctor_get(v_t_1942_, 1);
v___x_1945_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1941_, v_root_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_array_get_size(v_tail_1944_);
v___x_1948_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
return v___x_1945_;
}
else
{
if (v___x_1948_ == 0)
{
return v___x_1945_;
}
else
{
size_t v___x_1949_; size_t v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = lean_usize_of_nat(v___x_1947_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1941_, v_tail_1944_, v___x_1949_, v___x_1950_);
return v___x_1951_;
}
}
}
else
{
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(lean_object* v_exp_1952_, lean_object* v_t_1953_){
_start:
{
uint8_t v_res_1954_; lean_object* v_r_1955_; 
v_res_1954_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_1952_, v_t_1953_);
lean_dec_ref(v_t_1953_);
lean_dec_ref(v_exp_1952_);
v_r_1955_ = lean_box(v_res_1954_);
return v_r_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(lean_object* v_init_1956_, lean_object* v_x_1957_){
_start:
{
if (lean_obj_tag(v_x_1957_) == 0)
{
lean_object* v_k_1958_; lean_object* v_l_1959_; lean_object* v_r_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_k_1958_ = lean_ctor_get(v_x_1957_, 1);
v_l_1959_ = lean_ctor_get(v_x_1957_, 3);
v_r_1960_ = lean_ctor_get(v_x_1957_, 4);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1956_, v_r_1960_);
lean_inc(v_k_1958_);
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_k_1958_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v_init_1956_ = v___x_1962_;
v_x_1957_ = v_l_1959_;
goto _start;
}
else
{
return v_init_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(lean_object* v_init_1964_, lean_object* v_x_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1964_, v_x_1965_);
lean_dec(v_x_1965_);
return v_res_1966_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
if (lean_obj_tag(v_a_1970_) == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = l_List_reverse___redArg(v_a_1971_);
return v___x_1972_;
}
else
{
lean_object* v_head_1973_; lean_object* v_tail_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1989_; 
v_head_1973_ = lean_ctor_get(v_a_1970_, 0);
v_tail_1974_ = lean_ctor_get(v_a_1970_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_a_1970_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1976_ = v_a_1970_;
v_isShared_1977_ = v_isSharedCheck_1989_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_tail_1974_);
lean_inc(v_head_1973_);
lean_dec(v_a_1970_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1989_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1978_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1);
v___x_1979_ = 0;
v___x_1980_ = l_Lean_MessageData_ofConstName(v_head_1973_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1978_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = l_Lean_indentD(v___x_1983_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_a_1971_);
lean_ctor_set(v___x_1976_, 0, v___x_1984_);
v___x_1986_ = v___x_1976_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_a_1971_);
v___x_1986_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v_a_1970_ = v_tail_1974_;
v_a_1971_ = v___x_1986_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2));
v___x_1995_ = l_Lean_stringToMessageData(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9));
v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
return v___x_2006_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11));
v___x_2009_ = l_Lean_stringToMessageData(v___x_2008_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15));
v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(lean_object* v_exp_2019_, lean_object* v_expected_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_autoBoundImplicitContext_2029_; 
v_autoBoundImplicitContext_2029_ = lean_ctor_get(v_a_2021_, 2);
if (lean_obj_tag(v_autoBoundImplicitContext_2029_) == 0)
{
lean_dec_ref(v_expected_2020_);
goto v___jp_2026_;
}
else
{
lean_object* v_val_2030_; uint8_t v___x_2031_; 
v_val_2030_ = lean_ctor_get(v_autoBoundImplicitContext_2029_, 0);
v___x_2031_ = l_Lean_Expr_isFVar(v_exp_2019_);
if (v___x_2031_ == 0)
{
lean_dec_ref(v_expected_2020_);
goto v___jp_2026_;
}
else
{
lean_object* v_boundVariables_2032_; uint8_t v___x_2033_; 
v_boundVariables_2032_ = lean_ctor_get(v_val_2030_, 0);
v___x_2033_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_2019_, v_boundVariables_2032_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v_expected_2020_);
goto v___jp_2026_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l_Lean_Expr_fvarId_x21(v_exp_2019_);
v___x_2035_ = l_Lean_FVarId_getUserName___redArg(v___x_2034_, v_a_2022_, v_a_2023_, v_a_2024_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2094_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc_n(v_a_2036_, 2);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l_Lean_MessageData_ofName(v_a_2036_);
v___x_2038_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_a_2036_, v_a_2024_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2094_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2094_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___y_2055_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2043_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1);
lean_inc_ref(v___x_2037_);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2037_);
v___x_2045_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_stringToMessageData(v_expected_2020_);
lean_inc_ref(v___x_2047_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v___x_2047_);
v___x_2052_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v___x_2061_, v_a_2039_);
lean_dec(v_a_2039_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref(v___x_2037_);
v___x_2063_ = l_Lean_MessageData_nil;
v___y_2055_ = v___x_2063_;
goto v___jp_2054_;
}
else
{
lean_object* v_tail_2064_; 
v_tail_2064_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_tail_2064_);
if (lean_obj_tag(v_tail_2064_) == 0)
{
lean_object* v_head_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2082_; 
v_head_2065_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2062_, 1);
lean_dec(v_unused_2083_);
v___x_2067_ = v___x_2062_;
v_isShared_2068_ = v_isSharedCheck_2082_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_head_2065_);
lean_dec(v___x_2062_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2082_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2069_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10);
v___x_2071_ = 0;
v___x_2072_ = l_Lean_MessageData_ofConstName(v_head_2065_, v___x_2071_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 7);
lean_ctor_set(v___x_2067_, 1, v___x_2072_);
lean_ctor_set(v___x_2067_, 0, v___x_2070_);
v___x_2074_ = v___x_2067_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2037_);
v___x_2078_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2069_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___y_2055_ = v___x_2080_;
goto v___jp_2054_;
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v_tail_2064_);
v___x_2084_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2085_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2037_);
v___x_2087_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2084_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(v___x_2062_, v___x_2061_);
v___x_2091_ = l_Lean_MessageData_nil;
v___x_2092_ = l_Lean_MessageData_joinSep(v___x_2090_, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2089_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___y_2055_ = v___x_2093_;
goto v___jp_2054_;
}
}
v___jp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___y_2055_);
v___x_2057_ = l_Lean_MessageData_hint_x27(v___x_2056_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2057_);
v___x_2059_ = v___x_2041_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_expected_2020_);
v_a_2095_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2035_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2035_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
v___jp_2026_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = l_Lean_MessageData_nil;
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(lean_object* v_exp_2103_, lean_object* v_expected_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2103_, v_expected_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_exp_2103_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure(lean_object* v_exp_2111_, lean_object* v_expected_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2111_, v_expected_2112_, v_a_2113_, v_a_2115_, v_a_2117_, v_a_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(lean_object* v_exp_2121_, lean_object* v_expected_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Elab_Term_hintAutoImplicitFailure(v_exp_2121_, v_expected_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_exp_2121_);
return v_res_2130_;
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
