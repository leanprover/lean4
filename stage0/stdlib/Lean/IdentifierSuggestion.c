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
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
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
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Cannot make suggestions for private names"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid `[suggest_for]` attribute syntax "};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value;
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
v___x_459_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_464_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_464_, 10, v___x_462_);
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
lean_object* v___x_482_; lean_object* v_toCold_483_; lean_object* v_env_484_; lean_object* v_options_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_482_ = lean_st_ref_get(v___y_480_);
v_toCold_483_ = lean_ctor_get(v___y_479_, 0);
v_env_484_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref(v_env_484_);
lean_dec(v___x_482_);
v_options_485_ = lean_ctor_get(v_toCold_483_, 2);
v___x_486_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_487_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_485_);
v___x_488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_488_, 0, v_env_484_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
lean_ctor_set(v___x_488_, 3, v_options_485_);
v___x_489_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_msgData_478_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_ref_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_ref_500_ = lean_ctor_get(v___y_497_, 2);
v___x_501_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msg_496_, v___y_497_, v___y_498_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_inc(v_ref_500_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_ref_500_);
lean_ctor_set(v___x_506_, 1, v_a_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(lean_object* v_name_528_, uint8_t v_kind_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___y_539_; 
v___x_533_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_534_ = l_Lean_MessageData_ofName(v_name_528_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
switch(v_kind_529_)
{
case 0:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6));
v___y_539_ = v___x_546_;
goto v___jp_538_;
}
case 1:
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7));
v___y_539_ = v___x_547_;
goto v___jp_538_;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8));
v___y_539_ = v___x_548_;
goto v___jp_538_;
}
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_inc_ref(v___y_539_);
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___y_539_);
v___x_541_ = l_Lean_MessageData_ofFormat(v___x_540_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_537_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_544_, v___y_530_, v___y_531_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_name_549_, lean_object* v_kind_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v_kind_boxed_554_; lean_object* v_res_555_; 
v_kind_boxed_554_ = lean_unbox(v_kind_550_);
v_res_555_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_549_, v_kind_boxed_554_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(size_t v_sz_556_, size_t v_i_557_, lean_object* v_bs_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_557_, v_sz_556_);
if (v___x_559_ == 0)
{
return v_bs_558_;
}
else
{
lean_object* v_v_560_; lean_object* v___x_561_; lean_object* v_bs_x27_562_; lean_object* v___x_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v_v_560_ = lean_array_uget(v_bs_558_, v_i_557_);
v___x_561_ = lean_unsigned_to_nat(0u);
v_bs_x27_562_ = lean_array_uset(v_bs_558_, v_i_557_, v___x_561_);
v___x_563_ = l_Lean_Syntax_getId(v_v_560_);
lean_dec(v_v_560_);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_557_, v___x_564_);
v___x_566_ = lean_array_uset(v_bs_x27_562_, v_i_557_, v___x_563_);
v_i_557_ = v___x_565_;
v_bs_558_ = v___x_566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_568_, lean_object* v_i_569_, lean_object* v_bs_570_){
_start:
{
size_t v_sz_boxed_571_; size_t v_i_boxed_572_; lean_object* v_res_573_; 
v_sz_boxed_571_ = lean_unbox_usize(v_sz_568_);
lean_dec(v_sz_568_);
v_i_boxed_572_ = lean_unbox_usize(v_i_569_);
lean_dec(v_i_569_);
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_boxed_571_, v_i_boxed_572_, v_bs_570_);
return v_res_573_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
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
size_t v_sz_604_; size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_toEnvExtension_608_; lean_object* v_env_609_; lean_object* v_nextMacroScope_610_; lean_object* v_ngen_611_; lean_object* v_auxDeclNGen_612_; lean_object* v_traceState_613_; lean_object* v_messages_614_; lean_object* v_infoState_615_; lean_object* v_snapshotTasks_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_651_; 
v_sz_604_ = lean_array_size(v___y_602_);
v___x_605_ = ((size_t)0ULL);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_604_, v___x_605_, v___y_602_);
v___x_607_ = lean_st_ref_take(v___y_603_);
v_toEnvExtension_608_ = lean_ctor_get(v_a_588_, 0);
v_env_609_ = lean_ctor_get(v___x_607_, 0);
v_nextMacroScope_610_ = lean_ctor_get(v___x_607_, 1);
v_ngen_611_ = lean_ctor_get(v___x_607_, 2);
v_auxDeclNGen_612_ = lean_ctor_get(v___x_607_, 3);
v_traceState_613_ = lean_ctor_get(v___x_607_, 4);
v_messages_614_ = lean_ctor_get(v___x_607_, 6);
v_infoState_615_ = lean_ctor_get(v___x_607_, 7);
v_snapshotTasks_616_ = lean_ctor_get(v___x_607_, 8);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_607_, 5);
lean_dec(v_unused_652_);
v___x_618_ = v___x_607_;
v_isShared_619_ = v_isSharedCheck_651_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snapshotTasks_616_);
lean_inc(v_infoState_615_);
lean_inc(v_messages_614_);
lean_inc(v_traceState_613_);
lean_inc(v_auxDeclNGen_612_);
lean_inc(v_ngen_611_);
lean_inc(v_nextMacroScope_610_);
lean_inc(v_env_609_);
lean_dec(v___x_607_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_651_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_asyncMode_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_asyncMode_620_ = lean_ctor_get(v_toEnvExtension_608_, 2);
lean_inc(v_asyncMode_620_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_decl_595_);
lean_ctor_set(v___x_621_, 1, v___x_606_);
lean_inc(v___x_589_);
lean_inc_ref(v___x_621_);
v___x_622_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_588_, v_env_609_, v___x_621_, v_asyncMode_620_, v___x_589_);
lean_dec(v_asyncMode_620_);
v___x_623_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 5, v___x_623_);
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_nextMacroScope_610_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_ngen_611_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_auxDeclNGen_612_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_traceState_613_);
lean_ctor_set(v_reuseFailAlloc_650_, 5, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_650_, 6, v_messages_614_);
lean_ctor_set(v_reuseFailAlloc_650_, 7, v_infoState_615_);
lean_ctor_set(v_reuseFailAlloc_650_, 8, v_snapshotTasks_616_);
v___x_625_ = v_reuseFailAlloc_650_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_toEnvExtension_628_; lean_object* v_env_629_; lean_object* v_nextMacroScope_630_; lean_object* v_ngen_631_; lean_object* v_auxDeclNGen_632_; lean_object* v_traceState_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_648_; 
v___x_626_ = lean_st_ref_put(v___y_603_, v___x_625_);
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
lean_object* v_asyncMode_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v_asyncMode_640_ = lean_ctor_get(v_toEnvExtension_628_, 2);
lean_inc(v_asyncMode_640_);
v___x_641_ = lean_box(0);
v___x_642_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_590_, v_env_629_, v___x_621_, v_asyncMode_640_, v___x_589_);
lean_dec(v_asyncMode_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 5, v___x_623_);
lean_ctor_set(v___x_638_, 0, v___x_642_);
v___x_644_ = v___x_638_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_nextMacroScope_630_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_ngen_631_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_auxDeclNGen_632_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_traceState_633_);
lean_ctor_set(v_reuseFailAlloc_647_, 5, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_647_, 6, v_messages_634_);
lean_ctor_set(v_reuseFailAlloc_647_, 7, v_infoState_635_);
lean_ctor_set(v_reuseFailAlloc_647_, 8, v_snapshotTasks_636_);
v___x_644_ = v_reuseFailAlloc_647_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_st_ref_put(v___y_603_, v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_641_);
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
v___x_658_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
v___x_659_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_658_, v___y_655_, v___y_656_);
return v___x_659_;
}
}
v___jp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v___x_663_ = lean_obj_once(&l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_, &l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once, _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
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
v___x_697_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
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
v___x_707_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
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
v___x_709_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
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
v___x_711_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
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
v___x_728_ = ((lean_object*)(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_));
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(lean_object* v_as_1091_, lean_object* v_k_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_m_1097_; lean_object* v_a_1098_; uint8_t v___x_1099_; 
v___x_1095_ = lean_nat_add(v_x_1093_, v_x_1094_);
v___x_1096_ = lean_unsigned_to_nat(1u);
v_m_1097_ = lean_nat_shiftr(v___x_1095_, v___x_1096_);
lean_dec(v___x_1095_);
v_a_1098_ = lean_array_fget_borrowed(v_as_1091_, v_m_1097_);
v___x_1099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_1098_, v_k_1092_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; 
lean_dec(v_x_1094_);
v___x_1100_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_k_1092_, v_a_1098_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_m_1097_);
lean_dec(v_x_1093_);
lean_inc(v_a_1098_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_a_1098_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; uint8_t v___y_1106_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_nat_dec_eq(v_m_1097_, v___x_1102_);
v___x_1104_ = lean_nat_sub(v_m_1097_, v___x_1096_);
lean_dec(v_m_1097_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_lt(v___x_1104_, v_x_1093_);
v___y_1106_ = v___x_1109_;
goto v___jp_1105_;
}
else
{
v___y_1106_ = v___x_1103_;
goto v___jp_1105_;
}
v___jp_1105_:
{
if (v___y_1106_ == 0)
{
v_x_1094_ = v___x_1104_;
goto _start;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v___x_1104_);
lean_dec(v_x_1093_);
v___x_1108_ = lean_box(0);
return v___x_1108_;
}
}
}
}
else
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
lean_dec(v_x_1093_);
v___x_1110_ = lean_nat_add(v_m_1097_, v___x_1096_);
lean_dec(v_m_1097_);
v___x_1111_ = lean_nat_dec_le(v___x_1110_, v_x_1094_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v___x_1110_);
lean_dec(v_x_1094_);
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
v_x_1093_ = v___x_1110_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(lean_object* v_as_1114_, lean_object* v_k_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1114_, v_k_1115_, v_x_1116_, v_x_1117_);
lean_dec_ref(v_k_1115_);
lean_dec_ref(v_as_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(lean_object* v_incorrectName_1119_, lean_object* v_as_1120_, size_t v_i_1121_, size_t v_stop_1122_, lean_object* v_b_1123_){
_start:
{
lean_object* v___y_1125_; uint8_t v___x_1129_; 
v___x_1129_ = lean_usize_dec_eq(v_i_1121_, v_stop_1122_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1130_ = lean_array_uget_borrowed(v_as_1120_, v_i_1121_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_array_get_size(v___x_1130_);
v___x_1133_ = lean_nat_dec_lt(v___x_1131_, v___x_1132_);
if (v___x_1133_ == 0)
{
v___y_1125_ = v_b_1123_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_nat_sub(v___x_1132_, v___x_1134_);
v___x_1136_ = lean_nat_dec_le(v___x_1131_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec(v___x_1135_);
v___y_1125_ = v_b_1123_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((lean_object*)(l_Lean_getSuggestions___redArg___lam__1___closed__0));
lean_inc(v_incorrectName_1119_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_incorrectName_1119_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v___x_1130_, v___x_1138_, v___x_1131_, v___x_1135_);
lean_dec_ref_known(v___x_1138_, 2);
if (lean_obj_tag(v___x_1139_) == 0)
{
v___y_1125_ = v_b_1123_;
goto v___jp_1124_;
}
else
{
lean_object* v_val_1140_; lean_object* v_snd_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v_val_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v_snd_1141_ = lean_ctor_get(v_val_1140_, 1);
lean_inc(v_snd_1141_);
lean_dec(v_val_1140_);
v___x_1142_ = lean_array_get_size(v_snd_1141_);
v___x_1143_ = lean_nat_dec_lt(v___x_1131_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_dec(v_snd_1141_);
v___y_1125_ = v_b_1123_;
goto v___jp_1124_;
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1142_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_1141_, v___x_1144_, v___x_1145_, v_b_1123_);
lean_dec(v_snd_1141_);
v___y_1125_ = v___x_1146_;
goto v___jp_1124_;
}
}
}
}
}
else
{
lean_dec(v_incorrectName_1119_);
return v_b_1123_;
}
v___jp_1124_:
{
size_t v___x_1126_; size_t v___x_1127_; 
v___x_1126_ = ((size_t)1ULL);
v___x_1127_ = lean_usize_add(v_i_1121_, v___x_1126_);
v_i_1121_ = v___x_1127_;
v_b_1123_ = v___y_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(lean_object* v_incorrectName_1147_, lean_object* v_as_1148_, lean_object* v_i_1149_, lean_object* v_stop_1150_, lean_object* v_b_1151_){
_start:
{
size_t v_i_boxed_1152_; size_t v_stop_boxed_1153_; lean_object* v_res_1154_; 
v_i_boxed_1152_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_stop_boxed_1153_ = lean_unbox_usize(v_stop_1150_);
lean_dec(v_stop_1150_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1147_, v_as_1148_, v_i_boxed_1152_, v_stop_boxed_1153_, v_b_1151_);
lean_dec_ref(v_as_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(lean_object* v_incorrectName_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_env_1160_; lean_object* v___x_1161_; lean_object* v_snd_1162_; lean_object* v_toEnvExtension_1163_; lean_object* v_asyncMode_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_importedEntries_1167_; lean_object* v_state_1168_; lean_object* v___y_1170_; lean_object* v___x_1179_; 
v___x_1158_ = lean_obj_once(&l_Lean_getSuggestions___redArg___closed__2, &l_Lean_getSuggestions___redArg___closed__2_once, _init_l_Lean_getSuggestions___redArg___closed__2);
v___x_1159_ = lean_st_ref_get(v___y_1156_);
v_env_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_env_1160_);
lean_dec(v___x_1159_);
v___x_1161_ = l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
v_snd_1162_ = lean_ctor_get(v___x_1161_, 1);
v_toEnvExtension_1163_ = lean_ctor_get(v_snd_1162_, 0);
v_asyncMode_1164_ = lean_ctor_get(v_toEnvExtension_1163_, 2);
v___x_1165_ = lean_box(0);
v___x_1166_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1158_, v_toEnvExtension_1163_, v_env_1160_, v_asyncMode_1164_, v___x_1165_);
v_importedEntries_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc_ref(v_importedEntries_1167_);
v_state_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_state_1168_);
lean_dec(v___x_1166_);
v___x_1179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_1168_, v_incorrectName_1155_);
lean_dec(v_state_1168_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_NameSet_empty;
v___y_1170_ = v___x_1180_;
goto v___jp_1169_;
}
else
{
lean_object* v_val_1181_; 
v_val_1181_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v___x_1179_, 1);
v___y_1170_ = v_val_1181_;
goto v___jp_1169_;
}
v___jp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_array_get_size(v_importedEntries_1167_);
v___x_1173_ = lean_nat_dec_lt(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref(v_importedEntries_1167_);
lean_dec(v_incorrectName_1155_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1170_);
return v___x_1174_;
}
else
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = lean_usize_of_nat(v___x_1172_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_1155_, v_importedEntries_1167_, v___x_1175_, v___x_1176_, v___y_1170_);
lean_dec_ref(v_importedEntries_1167_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(lean_object* v_incorrectName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1182_, v___y_1183_);
lean_dec(v___y_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(lean_object* v_x_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0));
v___x_1189_ = lean_string_append(v___x_1188_, v_x_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(lean_object* v_x_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(v_x_1190_);
lean_dec_ref(v_x_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, size_t v_sz_1200_, size_t v_i_1201_, lean_object* v_bs_1202_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_usize_dec_lt(v_i_1201_, v_sz_1200_);
if (v___x_1203_ == 0)
{
lean_dec(v___x_1199_);
lean_dec(v___x_1198_);
lean_dec_ref(v___x_1197_);
return v_bs_1202_;
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v_v_1206_; lean_object* v_bs_x27_1207_; lean_object* v___y_1209_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_nat_dec_eq(v___x_1195_, v___x_1204_);
v_v_1206_ = lean_array_uget(v_bs_1202_, v_i_1201_);
v_bs_x27_1207_ = lean_array_uset(v_bs_1202_, v_i_1201_, v___x_1204_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_inc(v_v_1206_);
v___y_1209_ = v_v_1206_;
goto v___jp_1208_;
}
else
{
lean_object* v_val_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_val_1226_ = lean_ctor_get(v___x_1196_, 0);
v___x_1227_ = lean_box(0);
lean_inc(v_v_1206_);
v___x_1228_ = l_Lean_Name_replacePrefix(v_v_1206_, v_val_1226_, v___x_1227_);
v___x_1229_ = l_Lean_Options_empty;
lean_inc(v___x_1228_);
lean_inc(v___x_1199_);
lean_inc(v___x_1198_);
lean_inc_ref(v___x_1197_);
v___x_1230_ = l_Lean_ResolveName_resolveGlobalName(v___x_1197_, v___x_1229_, v___x_1198_, v___x_1199_, v___x_1228_);
v___x_1231_ = l_List_lengthTR___redArg(v___x_1230_);
lean_dec(v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_dec_eq(v___x_1231_, v___x_1232_);
lean_dec(v___x_1231_);
if (v___x_1233_ == 0)
{
lean_dec(v___x_1228_);
lean_inc(v_v_1206_);
v___y_1209_ = v_v_1206_;
goto v___jp_1208_;
}
else
{
v___y_1209_ = v___x_1228_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_1209_, v___x_1203_);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1214_ = l_Lean_MessageData_ofConstName(v_v_1206_, v___x_1205_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1213_);
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1));
v___x_1219_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1211_);
lean_ctor_set(v___x_1219_, 1, v___x_1212_);
lean_ctor_set(v___x_1219_, 2, v___x_1212_);
lean_ctor_set(v___x_1219_, 3, v___x_1212_);
lean_ctor_set(v___x_1219_, 4, v___x_1217_);
lean_ctor_set(v___x_1219_, 5, v___x_1218_);
v___x_1220_ = 0;
v___x_1221_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1212_);
lean_ctor_set(v___x_1221_, 2, v___x_1212_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*3, v___x_1220_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1201_, v___x_1222_);
v___x_1224_ = lean_array_uset(v_bs_x27_1207_, v_i_1201_, v___x_1221_);
v_i_1201_ = v___x_1223_;
v_bs_1202_ = v___x_1224_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(lean_object* v___x_1234_, lean_object* v___x_1235_, lean_object* v___x_1236_, lean_object* v___x_1237_, lean_object* v___x_1238_, lean_object* v_sz_1239_, lean_object* v_i_1240_, lean_object* v_bs_1241_){
_start:
{
size_t v_sz_boxed_1242_; size_t v_i_boxed_1243_; lean_object* v_res_1244_; 
v_sz_boxed_1242_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_i_boxed_1243_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_1234_, v___x_1235_, v___x_1236_, v___x_1237_, v___x_1238_, v_sz_boxed_1242_, v_i_boxed_1243_, v_bs_1241_);
lean_dec(v___x_1235_);
lean_dec(v___x_1234_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(lean_object* v_msgData_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v_env_1252_; lean_object* v___x_1253_; lean_object* v_toCold_1254_; lean_object* v_mctx_1255_; lean_object* v_lctx_1256_; lean_object* v_options_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1251_ = lean_st_ref_get(v___y_1249_);
v_env_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_ref(v_env_1252_);
lean_dec(v___x_1251_);
v___x_1253_ = lean_st_ref_get(v___y_1247_);
v_toCold_1254_ = lean_ctor_get(v___y_1248_, 0);
v_mctx_1255_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref(v_mctx_1255_);
lean_dec(v___x_1253_);
v_lctx_1256_ = lean_ctor_get(v___y_1246_, 2);
v_options_1257_ = lean_ctor_get(v_toCold_1254_, 2);
lean_inc_ref(v_options_1257_);
lean_inc_ref(v_lctx_1256_);
v___x_1258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1258_, 0, v_env_1252_);
lean_ctor_set(v___x_1258_, 1, v_mctx_1255_);
lean_ctor_set(v___x_1258_, 2, v_lctx_1256_);
lean_ctor_set(v___x_1258_, 3, v_options_1257_);
v___x_1259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_msgData_1245_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1267_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_box(1);
v___x_1269_ = l_Lean_MessageData_ofFormat(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2));
v___x_1274_ = l_Lean_MessageData_ofFormat(v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
return v_x_1275_;
}
else
{
lean_object* v_head_1277_; lean_object* v_tail_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1300_; 
v_head_1277_ = lean_ctor_get(v_x_1276_, 0);
v_tail_1278_ = lean_ctor_get(v_x_1276_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1280_ = v_x_1276_;
v_isShared_1281_ = v_isSharedCheck_1300_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_tail_1278_);
lean_inc(v_head_1277_);
lean_dec(v_x_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1300_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_before_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1298_; 
v_before_1282_ = lean_ctor_get(v_head_1277_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_head_1277_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_head_1277_, 1);
lean_dec(v_unused_1299_);
v___x_1284_ = v_head_1277_;
v_isShared_1285_ = v_isSharedCheck_1298_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_before_1282_);
lean_dec(v_head_1277_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1298_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 7);
lean_ctor_set(v___x_1284_, 1, v___x_1286_);
lean_ctor_set(v___x_1284_, 0, v_x_1275_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_x_1275_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3);
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 7);
lean_ctor_set(v___x_1280_, 1, v___x_1289_);
lean_ctor_set(v___x_1280_, 0, v___x_1288_);
v___x_1291_ = v___x_1280_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = l_Lean_MessageData_ofSyntax(v_before_1282_);
v___x_1293_ = l_Lean_indentD(v___x_1292_);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v_x_1275_ = v___x_1294_;
v_x_1276_ = v_tail_1278_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(lean_object* v_opts_1301_, lean_object* v_opt_1302_){
_start:
{
lean_object* v_name_1303_; lean_object* v_defValue_1304_; lean_object* v_map_1305_; lean_object* v___x_1306_; 
v_name_1303_ = lean_ctor_get(v_opt_1302_, 0);
v_defValue_1304_ = lean_ctor_get(v_opt_1302_, 1);
v_map_1305_ = lean_ctor_get(v_opts_1301_, 0);
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1305_, v_name_1303_);
if (lean_obj_tag(v___x_1306_) == 0)
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_unbox(v_defValue_1304_);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; 
v_val_1308_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1306_, 1);
if (lean_obj_tag(v_val_1308_) == 1)
{
uint8_t v_v_1309_; 
v_v_1309_ = lean_ctor_get_uint8(v_val_1308_, 0);
lean_dec_ref_known(v_val_1308_, 0);
return v_v_1309_;
}
else
{
uint8_t v___x_1310_; 
lean_dec(v_val_1308_);
v___x_1310_ = lean_unbox(v_defValue_1304_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(lean_object* v_opts_1311_, lean_object* v_opt_1312_){
_start:
{
uint8_t v_res_1313_; lean_object* v_r_1314_; 
v_res_1313_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_1311_, v_opt_1312_);
lean_dec_ref(v_opt_1312_);
lean_dec_ref(v_opts_1311_);
v_r_1314_ = lean_box(v_res_1313_);
return v_r_1314_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1));
v___x_1319_ = l_Lean_MessageData_ofFormat(v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(lean_object* v_msgData_1320_, lean_object* v_macroStack_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_toCold_1324_; lean_object* v_options_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_toCold_1324_ = lean_ctor_get(v___y_1322_, 0);
v_options_1325_ = lean_ctor_get(v_toCold_1324_, 2);
v___x_1326_ = l_Lean_Elab_pp_macroStack;
v___x_1327_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_options_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec(v_macroStack_1321_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_msgData_1320_);
return v___x_1328_;
}
else
{
if (lean_obj_tag(v_macroStack_1321_) == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_msgData_1320_);
return v___x_1329_;
}
else
{
lean_object* v_head_1330_; lean_object* v_after_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1346_; 
v_head_1330_ = lean_ctor_get(v_macroStack_1321_, 0);
lean_inc(v_head_1330_);
v_after_1331_ = lean_ctor_get(v_head_1330_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_head_1330_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_head_1330_, 0);
lean_dec(v_unused_1347_);
v___x_1333_ = v_head_1330_;
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_after_1331_);
lean_dec(v_head_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 7);
lean_ctor_set(v___x_1333_, 1, v___x_1335_);
lean_ctor_set(v___x_1333_, 0, v_msgData_1320_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_msgData_1320_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_msgData_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1338_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_MessageData_ofSyntax(v_after_1331_);
v___x_1341_ = l_Lean_indentD(v___x_1340_);
v_msgData_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1342_, 0, v___x_1339_);
lean_ctor_set(v_msgData_1342_, 1, v___x_1341_);
v___x_1343_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(v_msgData_1342_, v_macroStack_1321_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_1348_, lean_object* v_macroStack_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1348_, v_macroStack_1349_, v___y_1350_);
lean_dec_ref(v___y_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_ref_1361_; lean_object* v_macroStack_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_ref_1361_ = lean_ctor_get(v___y_1358_, 2);
v_macroStack_1362_ = lean_ctor_get(v___y_1354_, 1);
v___x_1363_ = l_Lean_Elab_getBetterRef(v_ref_1361_, v_macroStack_1362_);
v___x_1364_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msg_1353_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
lean_inc(v_macroStack_1362_);
v___x_1366_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_a_1365_, v_macroStack_1362_, v___y_1358_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1363_);
lean_ctor_set(v___x_1371_, 1, v_a_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(lean_object* v_ref_1385_, lean_object* v_msg_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_toCold_1394_; lean_object* v_currRecDepth_1395_; lean_object* v_ref_1396_; uint8_t v_diag_1397_; uint8_t v_suppressElabErrors_1398_; lean_object* v_ref_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_toCold_1394_ = lean_ctor_get(v___y_1391_, 0);
v_currRecDepth_1395_ = lean_ctor_get(v___y_1391_, 1);
v_ref_1396_ = lean_ctor_get(v___y_1391_, 2);
v_diag_1397_ = lean_ctor_get_uint8(v___y_1391_, sizeof(void*)*3);
v_suppressElabErrors_1398_ = lean_ctor_get_uint8(v___y_1391_, sizeof(void*)*3 + 1);
v_ref_1399_ = l_Lean_replaceRef(v_ref_1385_, v_ref_1396_);
lean_inc(v_currRecDepth_1395_);
lean_inc_ref(v_toCold_1394_);
v___x_1400_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1400_, 0, v_toCold_1394_);
lean_ctor_set(v___x_1400_, 1, v_currRecDepth_1395_);
lean_ctor_set(v___x_1400_, 2, v_ref_1399_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*3, v_diag_1397_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*3 + 1, v_suppressElabErrors_1398_);
v___x_1401_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___x_1400_, v___y_1392_);
lean_dec_ref_known(v___x_1400_, 3);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_ref_1402_);
return v_res_1411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2));
v___x_1417_ = l_Lean_stringToMessageData(v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4));
v___x_1420_ = l_Lean_stringToMessageData(v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6));
v___x_1423_ = l_Lean_stringToMessageData(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8));
v___x_1426_ = l_Lean_stringToMessageData(v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(lean_object* v_msg_1433_, lean_object* v_declHint_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_env_1439_; uint8_t v___x_1440_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_st_ref_get(v___y_1435_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = l_Lean_Name_isAnonymous(v_declHint_1434_);
if (v___x_1440_ == 0)
{
uint8_t v_isExporting_1441_; 
v_isExporting_1441_ = lean_ctor_get_uint8(v_env_1439_, sizeof(void*)*8);
if (v_isExporting_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_msg_1433_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
lean_inc_ref(v_env_1439_);
v___x_1443_ = l_Lean_Environment_setExporting(v_env_1439_, v___x_1440_);
lean_inc(v_declHint_1434_);
lean_inc_ref(v___x_1443_);
v___x_1444_ = l_Lean_Environment_contains(v___x_1443_, v_declHint_1434_, v_isExporting_1441_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref(v___x_1443_);
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_msg_1433_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_c_1451_; lean_object* v___x_1452_; 
v___x_1446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1447_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1448_ = l_Lean_Options_empty;
v___x_1449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1443_);
lean_ctor_set(v___x_1449_, 1, v___x_1446_);
lean_ctor_set(v___x_1449_, 2, v___x_1447_);
lean_ctor_set(v___x_1449_, 3, v___x_1448_);
lean_inc(v_declHint_1434_);
v___x_1450_ = l_Lean_MessageData_ofConstName(v_declHint_1434_, v___x_1440_);
v_c_1451_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1451_, 0, v___x_1449_);
lean_ctor_set(v_c_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1439_, v_declHint_1434_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v_c_1451_);
v___x_1455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_Lean_MessageData_note(v___x_1456_);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_msg_1433_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1494_; 
v_val_1460_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1462_ = v___x_1452_;
v_isShared_1463_ = v_isSharedCheck_1494_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_val_1460_);
lean_dec(v___x_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1494_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_mod_1466_; uint8_t v___x_1467_; 
v___x_1464_ = l_Lean_Environment_header(v_env_1439_);
lean_dec_ref(v_env_1439_);
v___x_1465_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1464_);
v_mod_1466_ = lean_array_get(v___x_1437_, v___x_1465_, v_val_1460_);
lean_dec(v_val_1460_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = l_Lean_isPrivateName(v_declHint_1434_);
lean_dec(v_declHint_1434_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1468_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_c_1451_);
v___x_1470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_MessageData_ofName(v_mod_1466_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Lean_MessageData_note(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_msg_1433_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1477_);
v___x_1479_ = v___x_1462_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_c_1451_);
v___x_1483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_MessageData_ofName(v_mod_1466_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_MessageData_note(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_msg_1433_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1490_);
v___x_1492_ = v___x_1462_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1495_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_msg_1433_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1496_, v_declHint_1497_, v___y_1498_);
lean_dec(v___y_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(lean_object* v_msg_1501_, lean_object* v_declHint_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1520_; 
v___x_1510_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1501_, v_declHint_1502_, v___y_1508_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1515_ = l_Lean_unknownIdentifierMessageTag;
v___x_1516_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(lean_object* v_msg_1521_, lean_object* v_declHint_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1521_, v_declHint_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(lean_object* v_ref_1531_, lean_object* v_msg_1532_, lean_object* v_declHint_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v___x_1543_; 
v___x_1541_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_1532_, v_declHint_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1531_, v_a_1542_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(lean_object* v_ref_1544_, lean_object* v_msg_1545_, lean_object* v_declHint_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1544_, v_msg_1545_, v_declHint_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_ref_1544_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg(lean_object* v_constName_1573_, lean_object* v_idOrConst_1574_, lean_object* v_declHint_1575_, lean_object* v_ref_x3f_1576_, lean_object* v_extraMsg_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___y_1586_; lean_object* v_hint_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1639_; uint8_t v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1681_; 
lean_inc(v_constName_1573_);
v___x_1656_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_constName_1573_, v_a_1583_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
if (lean_obj_tag(v_a_1657_) == 0)
{
lean_object* v_size_1686_; 
v_size_1686_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_size_1686_);
v___y_1681_ = v_size_1686_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_unsigned_to_nat(0u);
v___y_1681_ = v___x_1687_;
goto v___jp_1680_;
}
v___jp_1585_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1594_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1);
v___x_1595_ = l_Lean_stringToMessageData(v_idOrConst_1574_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = 0;
v___x_1600_ = l_Lean_MessageData_ofConstName(v_constName_1573_, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1598_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_extraMsg_1577_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v_hint_1587_);
v___x_1606_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v___y_1586_, v___x_1605_, v_declHint_1575_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1586_);
return v___x_1606_;
}
v___jp_1607_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; size_t v_sz_1623_; size_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1618_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___y_1610_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v___y_1617_);
v___x_1621_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v_sz_1623_ = lean_array_size(v___y_1615_);
v___x_1624_ = ((size_t)0ULL);
lean_inc(v___y_1609_);
lean_inc(v___y_1612_);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___y_1611_, v___y_1613_, v___y_1614_, v___y_1612_, v___y_1609_, v_sz_1623_, v___x_1624_, v___y_1615_);
lean_dec(v___y_1613_);
lean_dec(v___y_1611_);
lean_inc(v___y_1616_);
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1616_);
v___x_1627_ = lean_box(0);
v___x_1628_ = l_Lean_MessageData_hint(v___x_1622_, v___x_1625_, v___x_1626_, v___x_1627_, v___y_1608_, v_a_1582_, v_a_1583_);
lean_dec_ref(v___x_1625_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___y_1586_ = v___y_1616_;
v_hint_1587_ = v_a_1629_;
v___y_1588_ = v_a_1578_;
v___y_1589_ = v_a_1579_;
v___y_1590_ = v_a_1580_;
v___y_1591_ = v_a_1581_;
v___y_1592_ = v_a_1582_;
v___y_1593_ = v_a_1583_;
goto v___jp_1585_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v___y_1616_);
lean_dec_ref(v_extraMsg_1577_);
lean_dec(v_declHint_1575_);
lean_dec_ref(v_idOrConst_1574_);
lean_dec(v_constName_1573_);
v_a_1630_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1628_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
v___jp_1638_:
{
uint8_t v___x_1649_; 
v___x_1649_ = l_Lean_Name_isAnonymous(v___y_1644_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1650_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9);
v___x_1651_ = l_Lean_MessageData_ofName(v___y_1644_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___y_1608_ = v___y_1640_;
v___y_1609_ = v___y_1639_;
v___y_1610_ = v___y_1648_;
v___y_1611_ = v___y_1641_;
v___y_1612_ = v___y_1642_;
v___y_1613_ = v___y_1643_;
v___y_1614_ = v___y_1646_;
v___y_1615_ = v___y_1645_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___x_1654_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1655_; 
lean_dec(v___y_1644_);
v___x_1655_ = l_Lean_MessageData_nil;
v___y_1608_ = v___y_1640_;
v___y_1609_ = v___y_1639_;
v___y_1610_ = v___y_1648_;
v___y_1611_ = v___y_1641_;
v___y_1612_ = v___y_1642_;
v___y_1613_ = v___y_1643_;
v___y_1614_ = v___y_1646_;
v___y_1615_ = v___y_1645_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___x_1655_;
goto v___jp_1607_;
}
}
v___jp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1661_ = lean_array_get_size(v___y_1659_);
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = lean_nat_dec_eq(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v_toCold_1666_; lean_object* v_env_1667_; lean_object* v_currNamespace_1668_; lean_object* v_openDecls_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1664_ = l_Lean_Syntax_getId(v___y_1660_);
v___x_1665_ = lean_st_ref_get(v_a_1583_);
v_toCold_1666_ = lean_ctor_get(v_a_1582_, 0);
v_env_1667_ = lean_ctor_get(v___x_1665_, 0);
lean_inc_ref(v_env_1667_);
lean_dec(v___x_1665_);
v_currNamespace_1668_ = lean_ctor_get(v_toCold_1666_, 4);
v_openDecls_1669_ = lean_ctor_get(v_toCold_1666_, 5);
lean_inc(v_constName_1573_);
v___x_1670_ = l_Lean_Name_eraseSuffix_x3f(v_constName_1573_, v___x_1664_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_dec_eq(v___x_1661_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_obj_once(&l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11, &l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once, _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11);
v___y_1639_ = v_openDecls_1669_;
v___y_1640_ = v___x_1663_;
v___y_1641_ = v___x_1661_;
v___y_1642_ = v_currNamespace_1668_;
v___y_1643_ = v___x_1670_;
v___y_1644_ = v___x_1664_;
v___y_1645_ = v___y_1659_;
v___y_1646_ = v_env_1667_;
v___y_1647_ = v___y_1660_;
v___y_1648_ = v___x_1673_;
goto v___jp_1638_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1674_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1675_ = lean_array_fget_borrowed(v___y_1659_, v___x_1662_);
lean_inc(v___x_1675_);
v___x_1676_ = l_Lean_MessageData_ofConstName(v___x_1675_, v___x_1663_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1674_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v___x_1674_);
v___y_1639_ = v_openDecls_1669_;
v___y_1640_ = v___x_1663_;
v___y_1641_ = v___x_1661_;
v___y_1642_ = v_currNamespace_1668_;
v___y_1643_ = v___x_1670_;
v___y_1644_ = v___x_1664_;
v___y_1645_ = v___y_1659_;
v___y_1646_ = v_env_1667_;
v___y_1647_ = v___y_1660_;
v___y_1648_ = v___x_1678_;
goto v___jp_1638_;
}
}
else
{
lean_object* v___x_1679_; 
lean_dec_ref(v___y_1659_);
v___x_1679_ = l_Lean_MessageData_nil;
v___y_1586_ = v___y_1660_;
v_hint_1587_ = v___x_1679_;
v___y_1588_ = v_a_1578_;
v___y_1589_ = v_a_1579_;
v___y_1590_ = v_a_1580_;
v___y_1591_ = v_a_1581_;
v___y_1592_ = v_a_1582_;
v___y_1593_ = v_a_1583_;
goto v___jp_1585_;
}
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_mk_empty_array_with_capacity(v___y_1681_);
lean_dec(v___y_1681_);
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_1682_, v_a_1657_);
if (lean_obj_tag(v_ref_x3f_1576_) == 0)
{
lean_object* v_ref_1684_; 
v_ref_1684_ = lean_ctor_get(v_a_1582_, 2);
lean_inc(v_ref_1684_);
v___y_1659_ = v___x_1683_;
v___y_1660_ = v_ref_1684_;
goto v___jp_1658_;
}
else
{
lean_object* v_val_1685_; 
v_val_1685_ = lean_ctor_get(v_ref_x3f_1576_, 0);
lean_inc(v_val_1685_);
lean_dec_ref_known(v_ref_x3f_1576_, 1);
v___y_1659_ = v___x_1683_;
v___y_1660_ = v_val_1685_;
goto v___jp_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(lean_object* v_constName_1688_, lean_object* v_idOrConst_1689_, lean_object* v_declHint_1690_, lean_object* v_ref_x3f_1691_, lean_object* v_extraMsg_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1688_, v_idOrConst_1689_, v_declHint_1690_, v_ref_x3f_1691_, v_extraMsg_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions(lean_object* v_00_u03b1_1701_, lean_object* v_constName_1702_, lean_object* v_idOrConst_1703_, lean_object* v_declHint_1704_, lean_object* v_ref_x3f_1705_, lean_object* v_extraMsg_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_throwUnknownNameWithSuggestions___redArg(v_constName_1702_, v_idOrConst_1703_, v_declHint_1704_, v_ref_x3f_1705_, v_extraMsg_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownNameWithSuggestions___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_constName_1716_, lean_object* v_idOrConst_1717_, lean_object* v_declHint_1718_, lean_object* v_ref_x3f_1719_, lean_object* v_extraMsg_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_throwUnknownNameWithSuggestions(v_00_u03b1_1715_, v_constName_1716_, v_idOrConst_1717_, v_declHint_1718_, v_ref_x3f_1719_, v_extraMsg_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(lean_object* v_incorrectName_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_incorrectName_1729_, v___y_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(lean_object* v_incorrectName_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(v_incorrectName_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(lean_object* v_00_u03b1_1747_, lean_object* v_ref_1748_, lean_object* v_msg_1749_, lean_object* v_declHint_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_1748_, v_msg_1749_, v_declHint_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_ref_1760_, lean_object* v_msg_1761_, lean_object* v_declHint_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(v_00_u03b1_1759_, v_ref_1760_, v_msg_1761_, v_declHint_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v_ref_1760_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(lean_object* v_as_1771_, lean_object* v_k_1772_, lean_object* v_x_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_1771_, v_k_1772_, v_x_1773_, v_x_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(lean_object* v_as_1777_, lean_object* v_k_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(v_as_1777_, v_k_1778_, v_x_1779_, v_x_1780_, v_x_1781_);
lean_dec_ref(v_k_1778_);
lean_dec_ref(v_as_1777_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(lean_object* v_msg_1783_, lean_object* v_declHint_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_1783_, v_declHint_1784_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1793_, lean_object* v_declHint_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_1793_, v_declHint_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(lean_object* v_00_u03b1_1803_, lean_object* v_ref_1804_, lean_object* v_msg_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_1804_, v_msg_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1814_, lean_object* v_ref_1815_, lean_object* v_msg_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(v_00_u03b1_1814_, v_ref_1815_, v_msg_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v_ref_1815_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1825_, lean_object* v_msg_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(v_00_u03b1_1835_, v_msg_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(lean_object* v_msgData_1845_, lean_object* v_macroStack_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_1845_, v_macroStack_1846_, v___y_1851_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(lean_object* v_msgData_1855_, lean_object* v_macroStack_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_1855_, v_macroStack_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(lean_object* v_exp_1865_, lean_object* v_as_1866_, size_t v_i_1867_, size_t v_stop_1868_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_usize_dec_eq(v_i_1867_, v_stop_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_array_uget_borrowed(v_as_1866_, v_i_1867_);
v___x_1871_ = lean_expr_eqv(v___x_1870_, v_exp_1865_);
if (v___x_1871_ == 0)
{
size_t v___x_1872_; size_t v___x_1873_; 
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_add(v_i_1867_, v___x_1872_);
v_i_1867_ = v___x_1873_;
goto _start;
}
else
{
return v___x_1871_;
}
}
else
{
uint8_t v___x_1875_; 
v___x_1875_ = 0;
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(lean_object* v_exp_1876_, lean_object* v_as_1877_, lean_object* v_i_1878_, lean_object* v_stop_1879_){
_start:
{
size_t v_i_boxed_1880_; size_t v_stop_boxed_1881_; uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_i_boxed_1880_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_stop_boxed_1881_ = lean_unbox_usize(v_stop_1879_);
lean_dec(v_stop_1879_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1876_, v_as_1877_, v_i_boxed_1880_, v_stop_boxed_1881_);
lean_dec_ref(v_as_1877_);
lean_dec_ref(v_exp_1876_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(lean_object* v_exp_1884_, lean_object* v_x_1885_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_cs_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v_cs_1886_ = lean_ctor_get(v_x_1885_, 0);
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = lean_array_get_size(v_cs_1886_);
v___x_1889_ = lean_nat_dec_lt(v___x_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
return v___x_1889_;
}
else
{
if (v___x_1889_ == 0)
{
return v___x_1889_;
}
else
{
size_t v___x_1890_; size_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = ((size_t)0ULL);
v___x_1891_ = lean_usize_of_nat(v___x_1888_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1884_, v_cs_1886_, v___x_1890_, v___x_1891_);
return v___x_1892_;
}
}
}
else
{
lean_object* v_vs_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_vs_1893_ = lean_ctor_get(v_x_1885_, 0);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_array_get_size(v_vs_1893_);
v___x_1896_ = lean_nat_dec_lt(v___x_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
return v___x_1896_;
}
else
{
if (v___x_1896_ == 0)
{
return v___x_1896_;
}
else
{
size_t v___x_1897_; size_t v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = ((size_t)0ULL);
v___x_1898_ = lean_usize_of_nat(v___x_1895_);
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1884_, v_vs_1893_, v___x_1897_, v___x_1898_);
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(lean_object* v_exp_1900_, lean_object* v_as_1901_, size_t v_i_1902_, size_t v_stop_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_eq(v_i_1902_, v_stop_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = lean_array_uget_borrowed(v_as_1901_, v_i_1902_);
v___x_1906_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1900_, v___x_1905_);
if (v___x_1906_ == 0)
{
size_t v___x_1907_; size_t v___x_1908_; 
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1902_, v___x_1907_);
v_i_1902_ = v___x_1908_;
goto _start;
}
else
{
return v___x_1906_;
}
}
else
{
uint8_t v___x_1910_; 
v___x_1910_ = 0;
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(lean_object* v_exp_1911_, lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_stop_1914_){
_start:
{
size_t v_i_boxed_1915_; size_t v_stop_boxed_1916_; uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_i_boxed_1915_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_stop_boxed_1916_ = lean_unbox_usize(v_stop_1914_);
lean_dec(v_stop_1914_);
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_1911_, v_as_1912_, v_i_boxed_1915_, v_stop_boxed_1916_);
lean_dec_ref(v_as_1912_);
lean_dec_ref(v_exp_1911_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(lean_object* v_exp_1919_, lean_object* v_x_1920_){
_start:
{
uint8_t v_res_1921_; lean_object* v_r_1922_; 
v_res_1921_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1919_, v_x_1920_);
lean_dec_ref(v_x_1920_);
lean_dec_ref(v_exp_1919_);
v_r_1922_ = lean_box(v_res_1921_);
return v_r_1922_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(lean_object* v_exp_1923_, lean_object* v_t_1924_){
_start:
{
lean_object* v_root_1925_; lean_object* v_tail_1926_; uint8_t v___x_1927_; 
v_root_1925_ = lean_ctor_get(v_t_1924_, 0);
v_tail_1926_ = lean_ctor_get(v_t_1924_, 1);
v___x_1927_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_1923_, v_root_1925_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_array_get_size(v_tail_1926_);
v___x_1930_ = lean_nat_dec_lt(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
return v___x_1930_;
}
else
{
if (v___x_1930_ == 0)
{
return v___x_1930_;
}
else
{
size_t v___x_1931_; size_t v___x_1932_; uint8_t v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1929_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_1923_, v_tail_1926_, v___x_1931_, v___x_1932_);
return v___x_1933_;
}
}
}
else
{
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(lean_object* v_exp_1934_, lean_object* v_t_1935_){
_start:
{
uint8_t v_res_1936_; lean_object* v_r_1937_; 
v_res_1936_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_1934_, v_t_1935_);
lean_dec_ref(v_t_1935_);
lean_dec_ref(v_exp_1934_);
v_r_1937_ = lean_box(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(lean_object* v_init_1938_, lean_object* v_x_1939_){
_start:
{
if (lean_obj_tag(v_x_1939_) == 0)
{
lean_object* v_k_1940_; lean_object* v_l_1941_; lean_object* v_r_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_k_1940_ = lean_ctor_get(v_x_1939_, 1);
v_l_1941_ = lean_ctor_get(v_x_1939_, 3);
v_r_1942_ = lean_ctor_get(v_x_1939_, 4);
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1938_, v_r_1942_);
lean_inc(v_k_1940_);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_k_1940_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v_init_1938_ = v___x_1944_;
v_x_1939_ = v_l_1941_;
goto _start;
}
else
{
return v_init_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(lean_object* v_init_1946_, lean_object* v_x_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_1946_, v_x_1947_);
lean_dec(v_x_1947_);
return v_res_1948_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0));
v___x_1951_ = l_Lean_stringToMessageData(v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
if (lean_obj_tag(v_a_1952_) == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = l_List_reverse___redArg(v_a_1953_);
return v___x_1954_;
}
else
{
lean_object* v_head_1955_; lean_object* v_tail_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1971_; 
v_head_1955_ = lean_ctor_get(v_a_1952_, 0);
v_tail_1956_ = lean_ctor_get(v_a_1952_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_a_1952_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1958_ = v_a_1952_;
v_isShared_1959_ = v_isSharedCheck_1971_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_tail_1956_);
lean_inc(v_head_1955_);
lean_dec(v_a_1952_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1971_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1960_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1);
v___x_1961_ = 0;
v___x_1962_ = l_Lean_MessageData_ofConstName(v_head_1955_, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1960_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = l_Lean_indentD(v___x_1965_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v_a_1953_);
lean_ctor_set(v___x_1958_, 0, v___x_1966_);
v___x_1968_ = v___x_1958_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_a_1953_);
v___x_1968_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
v_a_1952_ = v_tail_1956_;
v_a_1953_ = v___x_1968_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0));
v___x_1974_ = l_Lean_stringToMessageData(v___x_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4));
v___x_1980_ = l_Lean_stringToMessageData(v___x_1979_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6));
v___x_1983_ = l_Lean_stringToMessageData(v___x_1982_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13));
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15));
v___x_1997_ = l_Lean_stringToMessageData(v___x_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(lean_object* v_exp_2001_, lean_object* v_expected_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_autoBoundImplicitContext_2011_; 
v_autoBoundImplicitContext_2011_ = lean_ctor_get(v_a_2003_, 2);
if (lean_obj_tag(v_autoBoundImplicitContext_2011_) == 0)
{
lean_dec_ref(v_expected_2002_);
goto v___jp_2008_;
}
else
{
lean_object* v_val_2012_; uint8_t v___x_2013_; 
v_val_2012_ = lean_ctor_get(v_autoBoundImplicitContext_2011_, 0);
v___x_2013_ = l_Lean_Expr_isFVar(v_exp_2001_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v_expected_2002_);
goto v___jp_2008_;
}
else
{
lean_object* v_boundVariables_2014_; uint8_t v___x_2015_; 
v_boundVariables_2014_ = lean_ctor_get(v_val_2012_, 0);
v___x_2015_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_2001_, v_boundVariables_2014_);
if (v___x_2015_ == 0)
{
lean_dec_ref(v_expected_2002_);
goto v___jp_2008_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = l_Lean_Expr_fvarId_x21(v_exp_2001_);
v___x_2017_ = l_Lean_FVarId_getUserName___redArg(v___x_2016_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2076_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_n(v_a_2018_, 2);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1);
v___x_2020_ = l_Lean_MessageData_ofName(v_a_2018_);
lean_inc_ref(v___x_2020_);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_stringToMessageData(v_expected_2002_);
lean_inc_ref(v___x_2024_);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2024_);
v___x_2029_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_a_2018_, v_a_2006_);
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2076_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2076_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___y_2037_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_box(0);
v___x_2044_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v___x_2043_, v_a_2032_);
lean_dec(v_a_2032_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2045_; 
lean_dec_ref(v___x_2020_);
v___x_2045_ = l_Lean_MessageData_nil;
v___y_2037_ = v___x_2045_;
goto v___jp_2036_;
}
else
{
lean_object* v_tail_2046_; 
v_tail_2046_ = lean_ctor_get(v___x_2044_, 1);
lean_inc(v_tail_2046_);
if (lean_obj_tag(v_tail_2046_) == 0)
{
lean_object* v_head_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2064_; 
v_head_2047_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2044_, 1);
lean_dec(v_unused_2065_);
v___x_2049_ = v___x_2044_;
v_isShared_2050_ = v_isSharedCheck_2064_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_head_2047_);
lean_dec(v___x_2044_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2064_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2051_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2052_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10);
v___x_2053_ = 0;
v___x_2054_ = l_Lean_MessageData_ofConstName(v_head_2047_, v___x_2053_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 7);
lean_ctor_set(v___x_2049_, 1, v___x_2054_);
lean_ctor_set(v___x_2049_, 0, v___x_2052_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2057_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___x_2020_);
v___x_2060_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2059_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2051_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___y_2037_ = v___x_2062_;
goto v___jp_2036_;
}
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_tail_2046_);
v___x_2066_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8);
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2020_);
v___x_2069_ = lean_obj_once(&l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18, &l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once, _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2066_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(v___x_2044_, v___x_2043_);
v___x_2073_ = l_Lean_MessageData_nil;
v___x_2074_ = l_Lean_MessageData_joinSep(v___x_2072_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2071_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___y_2037_ = v___x_2075_;
goto v___jp_2036_;
}
}
v___jp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2030_);
lean_ctor_set(v___x_2038_, 1, v___y_2037_);
v___x_2039_ = l_Lean_MessageData_hint_x27(v___x_2038_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2039_);
v___x_2041_ = v___x_2034_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_expected_2002_);
v_a_2077_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2017_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2017_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
v___jp_2008_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = l_Lean_MessageData_nil;
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(lean_object* v_exp_2085_, lean_object* v_expected_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2085_, v_expected_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec_ref(v_exp_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure(lean_object* v_exp_2093_, lean_object* v_expected_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(v_exp_2093_, v_expected_2094_, v_a_2095_, v_a_2097_, v_a_2099_, v_a_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(lean_object* v_exp_2103_, lean_object* v_expected_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_Elab_Term_hintAutoImplicitFailure(v_exp_2103_, v_expected_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_exp_2103_);
return v_res_2112_;
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
