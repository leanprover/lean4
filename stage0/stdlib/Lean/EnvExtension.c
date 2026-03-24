// Lean compiler output
// Module: Lean.EnvExtension
// Imports: public import Lean.Environment
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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Option_isSome___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4_value;
static const lean_array_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16_value;
static const lean_string_object l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17 = (const lean_object*)&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2(lean_object*);
static const lean_array_object l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0 = (const lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1 = (const lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1_value;
static const lean_array_object l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2 = (const lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__0_value)}};
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3_value;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___auto__1;
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_mkTagDeclarationExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkTagDeclarationExtension___closed__0 = (const lean_object*)&l_Lean_mkTagDeclarationExtension___closed__0_value;
static const lean_closure_object l_Lean_mkTagDeclarationExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkTagDeclarationExtension___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkTagDeclarationExtension___closed__1 = (const lean_object*)&l_Lean_mkTagDeclarationExtension___closed__1_value;
static const lean_closure_object l_Lean_mkTagDeclarationExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkTagDeclarationExtension___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkTagDeclarationExtension___closed__2 = (const lean_object*)&l_Lean_mkTagDeclarationExtension___closed__2_value;
static const lean_closure_object l_Lean_mkTagDeclarationExtension___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkTagDeclarationExtension___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkTagDeclarationExtension___closed__3 = (const lean_object*)&l_Lean_mkTagDeclarationExtension___closed__3_value;
static const lean_closure_object l_Lean_mkTagDeclarationExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkTagDeclarationExtension___closed__3_value),((lean_object*)&l_Lean_mkTagDeclarationExtension___closed__0_value)} };
static const lean_object* l_Lean_mkTagDeclarationExtension___closed__4 = (const lean_object*)&l_Lean_mkTagDeclarationExtension___closed__4_value;
static const lean_ctor_object l_Lean_mkTagDeclarationExtension___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkTagDeclarationExtension___closed__4_value)}};
static const lean_object* l_Lean_mkTagDeclarationExtension___closed__5 = (const lean_object*)&l_Lean_mkTagDeclarationExtension___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0_value;
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1_value;
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2_value;
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3_value;
static lean_once_cell_t l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4;
static lean_once_cell_t l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1;
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited;
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_TagDeclarationExtension_tag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.EnvExtension"};
static const lean_object* l_Lean_TagDeclarationExtension_tag___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_tag___closed__0_value;
static const lean_string_object l_Lean_TagDeclarationExtension_tag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.TagDeclarationExtension.tag"};
static const lean_object* l_Lean_TagDeclarationExtension_tag___closed__1 = (const lean_object*)&l_Lean_TagDeclarationExtension_tag___closed__1_value;
static const lean_string_object l_Lean_TagDeclarationExtension_tag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "assertion violation: env.getModuleIdxFor\? declName |>.isNone -- See comment at `TagDeclarationExtension`\n    "};
static const lean_object* l_Lean_TagDeclarationExtension_tag___closed__2 = (const lean_object*)&l_Lean_TagDeclarationExtension_tag___closed__2_value;
static lean_once_cell_t l_Lean_TagDeclarationExtension_tag___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagDeclarationExtension_tag___closed__3;
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_TagDeclarationExtension_isTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_TagDeclarationExtension_isTagged___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_isTagged___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedMapDeclarationExtension_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedMapDeclarationExtension_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedMapDeclarationExtension___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMapDeclarationExtension___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___auto__3;
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mkMapDeclarationExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkMapDeclarationExtension___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkMapDeclarationExtension___redArg___closed__0 = (const lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__0_value;
static const lean_closure_object l_Lean_mkMapDeclarationExtension___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkMapDeclarationExtension___redArg___closed__1 = (const lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__1_value;
static const lean_closure_object l_Lean_mkMapDeclarationExtension___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mkMapDeclarationExtension___redArg___closed__2 = (const lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__2_value;
static const lean_closure_object l_Lean_mkMapDeclarationExtension___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_mkMapDeclarationExtension___redArg___closed__3 = (const lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__3_value;
static const lean_closure_object l_Lean_mkMapDeclarationExtension___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_mkMapDeclarationExtension___redArg___closed__4 = (const lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__4_value;
static const lean_ctor_object l_Lean_mkMapDeclarationExtension___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__1_value)}};
static const lean_object* l_Lean_mkMapDeclarationExtension___redArg___closed__5 = (const lean_object*)&l_Lean_mkMapDeclarationExtension___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MapDeclarationExtension_insert___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.MapDeclarationExtension.insert"};
static const lean_object* l_Lean_MapDeclarationExtension_insert___redArg___closed__0 = (const lean_object*)&l_Lean_MapDeclarationExtension_insert___redArg___closed__0_value;
static const lean_string_object l_Lean_MapDeclarationExtension_insert___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "cannot insert `"};
static const lean_object* l_Lean_MapDeclarationExtension_insert___redArg___closed__1 = (const lean_object*)&l_Lean_MapDeclarationExtension_insert___redArg___closed__1_value;
static const lean_string_object l_Lean_MapDeclarationExtension_insert___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "` into `"};
static const lean_object* l_Lean_MapDeclarationExtension_insert___redArg___closed__2 = (const lean_object*)&l_Lean_MapDeclarationExtension_insert___redArg___closed__2_value;
static const lean_string_object l_Lean_MapDeclarationExtension_insert___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "`, it is not defined in the current module but in `"};
static const lean_object* l_Lean_MapDeclarationExtension_insert___redArg___closed__3 = (const lean_object*)&l_Lean_MapDeclarationExtension_insert___redArg___closed__3_value;
static const lean_string_object l_Lean_MapDeclarationExtension_insert___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_MapDeclarationExtension_insert___redArg___closed__4 = (const lean_object*)&l_Lean_MapDeclarationExtension_insert___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MapDeclarationExtension_contains___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_isSome___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_MapDeclarationExtension_contains___redArg___closed__0 = (const lean_object*)&l_Lean_MapDeclarationExtension_contains___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__0(lean_object* v_addEntryFn_1_, lean_object* v_x1_2_, lean_object* v_x2_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_addEntryFn_1_, v_x1_2_, v_x2_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg___lam__1(lean_object* v___f_24_, lean_object* v_x1_25_, lean_object* v_x2_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_array_get_size(v_x2_26_);
v___x_29_ = ((lean_object*)(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9));
v___x_30_ = lean_nat_dec_lt(v___x_27_, v___x_28_);
if (v___x_30_ == 0)
{
lean_dec_ref(v_x2_26_);
lean_dec(v___f_24_);
return v_x1_25_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_le(v___x_28_, v___x_28_);
if (v___x_31_ == 0)
{
if (v___x_30_ == 0)
{
lean_dec_ref(v_x2_26_);
lean_dec(v___f_24_);
return v_x1_25_;
}
else
{
size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; 
v___x_32_ = ((size_t)0ULL);
v___x_33_ = lean_usize_of_nat(v___x_28_);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_29_, v___f_24_, v_x2_26_, v___x_32_, v___x_33_, v_x1_25_);
return v___x_34_;
}
}
else
{
size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = ((size_t)0ULL);
v___x_36_ = lean_usize_of_nat(v___x_28_);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_29_, v___f_24_, v_x2_26_, v___x_35_, v___x_36_, v_x1_25_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg(lean_object* v_addEntryFn_38_, lean_object* v_initState_39_, lean_object* v_as_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_array_get_size(v_as_40_);
v___x_43_ = ((lean_object*)(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9));
v___x_44_ = lean_nat_dec_lt(v___x_41_, v___x_42_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_as_40_);
lean_dec(v_addEntryFn_38_);
return v_initState_39_;
}
else
{
lean_object* v___f_45_; lean_object* v___f_46_; uint8_t v___x_47_; 
v___f_45_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___redArg___lam__0), 3, 1);
lean_closure_set(v___f_45_, 0, v_addEntryFn_38_);
v___f_46_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___redArg___lam__1), 3, 1);
lean_closure_set(v___f_46_, 0, v___f_45_);
v___x_47_ = lean_nat_dec_le(v___x_42_, v___x_42_);
if (v___x_47_ == 0)
{
if (v___x_44_ == 0)
{
lean_dec_ref(v___f_46_);
lean_dec_ref(v_as_40_);
return v_initState_39_;
}
else
{
size_t v___x_48_; size_t v___x_49_; lean_object* v___x_50_; 
v___x_48_ = ((size_t)0ULL);
v___x_49_ = lean_usize_of_nat(v___x_42_);
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_43_, v___f_46_, v_as_40_, v___x_48_, v___x_49_, v_initState_39_);
return v___x_50_;
}
}
else
{
size_t v___x_51_; size_t v___x_52_; lean_object* v___x_53_; 
v___x_51_ = ((size_t)0ULL);
v___x_52_ = lean_usize_of_nat(v___x_42_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_43_, v___f_46_, v_as_40_, v___x_51_, v___x_52_, v_initState_39_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries(lean_object* v_00_u03b1_54_, lean_object* v_00_u03c3_55_, lean_object* v_addEntryFn_56_, lean_object* v_initState_57_, lean_object* v_as_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_mkStateFromImportedEntries___redArg(v_addEntryFn_56_, v_initState_57_, v_as_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10));
v___x_87_ = l_Lean_mkAtom(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12);
v___x_89_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17));
v___x_100_ = l_Lean_mkAtom(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18);
v___x_102_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19);
v___x_105_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20);
v___x_109_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13);
v___x_110_ = lean_array_push(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21);
v___x_112_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11));
v___x_113_ = lean_box(2);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22);
v___x_116_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_117_ = lean_array_push(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23);
v___x_119_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9));
v___x_120_ = lean_box(2);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24);
v___x_123_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25);
v___x_126_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7));
v___x_127_ = lean_box(2);
v___x_128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26);
v___x_130_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27);
v___x_133_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4));
v___x_134_ = lean_box(2);
v___x_135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
lean_ctor_set(v___x_135_, 2, v___x_132_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(lean_object* v_addEntryFn_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_dec(v_addEntryFn_137_);
return v_x_138_;
}
else
{
lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_142_; 
v_head_140_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_head_140_);
v_tail_141_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_tail_141_);
lean_dec_ref(v_x_139_);
lean_inc(v_addEntryFn_137_);
v___x_142_ = lean_apply_2(v_addEntryFn_137_, v_x_138_, v_head_140_);
v_x_138_ = v___x_142_;
v_x_139_ = v_tail_141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(lean_object* v___x_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
if (lean_obj_tag(v_a_145_) == 0)
{
lean_object* v___x_147_; 
lean_dec_ref(v___x_144_);
v___x_147_ = l_List_reverse___redArg(v_a_146_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_head_148_ = lean_ctor_get(v_a_145_, 0);
v_tail_149_ = lean_ctor_get(v_a_145_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_a_145_);
if (v_isSharedCheck_160_ == 0)
{
v___x_151_ = v_a_145_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_tail_149_);
lean_inc(v_head_148_);
lean_dec(v_a_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
lean_inc_ref(v___x_144_);
lean_inc(v_head_148_);
v___x_153_ = lean_apply_1(v___x_144_, v_head_148_);
v___x_154_ = lean_unbox(v___x_153_);
if (v___x_154_ == 0)
{
lean_del_object(v___x_151_);
lean_dec(v_head_148_);
v_a_145_ = v_tail_149_;
goto _start;
}
else
{
lean_object* v___x_157_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_a_146_);
v___x_157_ = v___x_151_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_head_148_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_a_146_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v_a_145_ = v_tail_149_;
v_a_146_ = v___x_157_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(lean_object* v_p_161_, lean_object* v_addEntryFn_162_, lean_object* v_newEntries_163_, lean_object* v_s_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_newEntries_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc(v_s_164_);
v___x_165_ = lean_apply_1(v_p_161_, v_s_164_);
v___x_166_ = lean_box(0);
v_newEntries_167_ = l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(v___x_165_, v_newEntries_163_, v___x_166_);
lean_inc(v_newEntries_167_);
v___x_168_ = l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(v_addEntryFn_162_, v_s_164_, v_newEntries_167_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v_newEntries_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter(lean_object* v_00_u03c3_170_, lean_object* v_00_u03b1_171_, lean_object* v_p_172_, lean_object* v_addEntryFn_173_, lean_object* v_newEntries_174_, lean_object* v_x_175_, lean_object* v_s_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(v_p_172_, v_addEntryFn_173_, v_newEntries_174_, v_s_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object* v_00_u03c3_178_, lean_object* v_00_u03b1_179_, lean_object* v_p_180_, lean_object* v_addEntryFn_181_, lean_object* v_newEntries_182_, lean_object* v_x_183_, lean_object* v_s_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_SimplePersistentEnvExtension_replayOfFilter(v_00_u03c3_178_, v_00_u03b1_179_, v_p_180_, v_addEntryFn_181_, v_newEntries_182_, v_x_183_, v_s_184_);
lean_dec(v_x_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0(lean_object* v_00_u03b1_186_, lean_object* v___x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(v___x_187_, v_a_188_, v_a_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1(lean_object* v_00_u03c3_191_, lean_object* v_00_u03b1_192_, lean_object* v_addEntryFn_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(v_addEntryFn_193_, v_x_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0(lean_object* v_addEntryFn_197_, lean_object* v_s_198_, lean_object* v_e_199_){
_start:
{
lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_210_; 
v_fst_200_ = lean_ctor_get(v_s_198_, 0);
v_snd_201_ = lean_ctor_get(v_s_198_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_s_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_203_ = v_s_198_;
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_snd_201_);
lean_inc(v_fst_200_);
lean_dec(v_s_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
lean_inc(v_e_199_);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v_e_199_);
lean_ctor_set(v___x_205_, 1, v_fst_200_);
v___x_206_ = lean_apply_2(v_addEntryFn_197_, v_snd_201_, v_e_199_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_206_);
lean_ctor_set(v___x_203_, 0, v___x_205_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(lean_object* v_exportEntriesFnEx_x3f_211_, lean_object* v_toArrayFn_212_, lean_object* v_env_213_, lean_object* v_s_214_, uint8_t v_level_215_){
_start:
{
if (lean_obj_tag(v_exportEntriesFnEx_x3f_211_) == 0)
{
lean_object* v_fst_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_env_213_);
v_fst_216_ = lean_ctor_get(v_s_214_, 0);
lean_inc(v_fst_216_);
lean_dec_ref(v_s_214_);
v___x_217_ = l_List_reverse___redArg(v_fst_216_);
v___x_218_ = lean_apply_1(v_toArrayFn_212_, v___x_217_);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec_ref(v_toArrayFn_212_);
v_val_219_ = lean_ctor_get(v_exportEntriesFnEx_x3f_211_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v_exportEntriesFnEx_x3f_211_);
v_fst_220_ = lean_ctor_get(v_s_214_, 0);
lean_inc(v_fst_220_);
v_snd_221_ = lean_ctor_get(v_s_214_, 1);
lean_inc(v_snd_221_);
lean_dec_ref(v_s_214_);
v___x_222_ = l_List_reverse___redArg(v_fst_220_);
v___x_223_ = lean_box(v_level_215_);
v___x_224_ = lean_apply_4(v_val_219_, v_env_213_, v_snd_221_, v___x_222_, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1___boxed(lean_object* v_exportEntriesFnEx_x3f_225_, lean_object* v_toArrayFn_226_, lean_object* v_env_227_, lean_object* v_s_228_, lean_object* v_level_229_){
_start:
{
uint8_t v_level_boxed_230_; lean_object* v_res_231_; 
v_level_boxed_230_ = lean_unbox(v_level_229_);
v_res_231_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(v_exportEntriesFnEx_x3f_225_, v_toArrayFn_226_, v_env_227_, v_s_228_, v_level_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2(lean_object* v_s_235_){
_start:
{
lean_object* v_fst_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_247_; 
v_fst_236_ = lean_ctor_get(v_s_235_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_s_235_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v_s_235_, 1);
lean_dec(v_unused_248_);
v___x_238_ = v_s_235_;
v_isShared_239_ = v_isSharedCheck_247_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_fst_236_);
lean_dec(v_s_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_247_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_240_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1));
v___x_241_ = l_List_lengthTR___redArg(v_fst_236_);
lean_dec(v_fst_236_);
v___x_242_ = l_Nat_reprFast(v___x_241_);
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 5);
lean_ctor_set(v___x_238_, 1, v___x_243_);
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_245_ = v___x_238_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(lean_object* v_x_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed(lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(v_x_253_);
lean_dec_ref(v_x_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(lean_object* v_addImportedFn_255_, lean_object* v___x_256_, lean_object* v_as_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_apply_1(v_addImportedFn_255_, v_as_257_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_256_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed(lean_object* v_addImportedFn_263_, lean_object* v___x_264_, lean_object* v_as_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(v_addImportedFn_263_, v___x_264_, v_as_265_, v___y_266_);
lean_dec_ref(v___y_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object* v___x_269_, lean_object* v_val_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v_fst_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_newEntries_284_; lean_object* v___x_285_; lean_object* v_fst_286_; lean_object* v_snd_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_fst_275_ = lean_ctor_get(v___y_274_, 0);
lean_inc(v_fst_275_);
v_snd_276_ = lean_ctor_get(v___y_274_, 1);
lean_inc(v_snd_276_);
lean_dec_ref(v___y_274_);
v_fst_277_ = lean_ctor_get(v___y_272_, 0);
lean_inc(v_fst_277_);
v_snd_278_ = lean_ctor_get(v___y_272_, 1);
lean_inc(v_snd_278_);
lean_dec_ref(v___y_272_);
v_fst_279_ = lean_ctor_get(v___y_271_, 0);
v___x_280_ = l_List_lengthTR___redArg(v_fst_277_);
v___x_281_ = l_List_lengthTR___redArg(v_fst_279_);
v___x_282_ = lean_nat_sub(v___x_280_, v___x_281_);
lean_dec(v___x_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_269_);
lean_inc(v_fst_277_);
v_newEntries_284_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_277_, v_fst_277_, v___x_282_, v___x_283_);
lean_dec(v_fst_277_);
v___x_285_ = lean_apply_3(v_val_270_, v_newEntries_284_, v_snd_278_, v_snd_276_);
v_fst_286_ = lean_ctor_get(v___x_285_, 0);
v_snd_287_ = lean_ctor_get(v___x_285_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_295_ == 0)
{
v___x_289_ = v___x_285_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_snd_287_);
lean_inc(v_fst_286_);
lean_dec(v___x_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = l_List_appendTR___redArg(v_fst_286_, v_fst_275_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_snd_287_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object* v___x_296_, lean_object* v_val_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(v___x_296_, v_val_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_298_);
lean_dec(v___x_296_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object* v_descr_307_){
_start:
{
lean_object* v_name_309_; lean_object* v_addEntryFn_310_; lean_object* v_addImportedFn_311_; lean_object* v_toArrayFn_312_; lean_object* v_exportEntriesFnEx_x3f_313_; lean_object* v_asyncMode_314_; lean_object* v_replay_x3f_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___f_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___y_328_; 
v_name_309_ = lean_ctor_get(v_descr_307_, 0);
lean_inc(v_name_309_);
v_addEntryFn_310_ = lean_ctor_get(v_descr_307_, 1);
lean_inc(v_addEntryFn_310_);
v_addImportedFn_311_ = lean_ctor_get(v_descr_307_, 2);
lean_inc(v_addImportedFn_311_);
v_toArrayFn_312_ = lean_ctor_get(v_descr_307_, 3);
lean_inc_ref(v_toArrayFn_312_);
v_exportEntriesFnEx_x3f_313_ = lean_ctor_get(v_descr_307_, 4);
lean_inc(v_exportEntriesFnEx_x3f_313_);
v_asyncMode_314_ = lean_ctor_get(v_descr_307_, 5);
lean_inc(v_asyncMode_314_);
v_replay_x3f_315_ = lean_ctor_get(v_descr_307_, 6);
lean_inc(v_replay_x3f_315_);
lean_dec_ref(v_descr_307_);
v___f_316_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0), 3, 1);
lean_closure_set(v___f_316_, 0, v_addEntryFn_310_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_317_, 0, v_exportEntriesFnEx_x3f_313_);
lean_closure_set(v___f_317_, 1, v_toArrayFn_312_);
v___f_318_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0));
v___f_319_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1));
v___x_320_ = lean_box(0);
lean_inc(v_addImportedFn_311_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_321_, 0, v_addImportedFn_311_);
lean_closure_set(v___f_321_, 1, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2));
v___x_324_ = lean_apply_1(v_addImportedFn_311_, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_320_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_326_, 0, lean_box(0));
lean_closure_set(v___x_326_, 1, lean_box(0));
lean_closure_set(v___x_326_, 2, v___x_325_);
if (lean_obj_tag(v_replay_x3f_315_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
v___y_328_ = v___x_332_;
goto v___jp_327_;
}
else
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_val_333_ = lean_ctor_get(v_replay_x3f_315_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_replay_x3f_315_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v_replay_x3f_315_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v_replay_x3f_315_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___f_337_; lean_object* v___x_339_; 
v___f_337_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_337_, 0, v___x_322_);
lean_closure_set(v___f_337_, 1, v_val_333_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___f_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___f_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v___y_328_ = v___x_339_;
goto v___jp_327_;
}
}
}
v___jp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_329_, 0, v_name_309_);
lean_ctor_set(v___x_329_, 1, v___x_326_);
lean_ctor_set(v___x_329_, 2, v___f_321_);
lean_ctor_set(v___x_329_, 3, v___f_316_);
lean_ctor_set(v___x_329_, 4, v___f_317_);
lean_ctor_set(v___x_329_, 5, v___f_318_);
lean_ctor_set(v___x_329_, 6, v_asyncMode_314_);
lean_ctor_set(v___x_329_, 7, v___y_328_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___f_319_);
v___x_331_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object* v_descr_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* v_00_u03b1_345_, lean_object* v_00_u03c3_346_, lean_object* v_inst_347_, lean_object* v_descr_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* v_00_u03b1_351_, lean_object* v_00_u03c3_352_, lean_object* v_inst_353_, lean_object* v_descr_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_registerSimplePersistentEnvExtension(v_00_u03b1_351_, v_00_u03c3_352_, v_inst_353_, v_descr_354_);
lean_dec(v_inst_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(lean_object* v_x_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(v_x_365_, v___y_366_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v_x_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(lean_object* v_s_369_, lean_object* v_x_370_){
_start:
{
lean_inc_ref(v_s_369_);
return v_s_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(v_s_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec_ref(v_s_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(lean_object* v_x_374_, lean_object* v_x_375_, uint8_t v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_x_90__boxed_381_; lean_object* v_res_382_; 
v_x_90__boxed_381_ = lean_unbox(v_x_380_);
v_res_382_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(v_x_378_, v_x_379_, v_x_90__boxed_381_);
lean_dec_ref(v_x_379_);
lean_dec_ref(v_x_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(v_x_385_);
lean_dec_ref(v_x_385_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_391_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5(void){
_start:
{
lean_object* v___f_392_; lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___f_392_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3));
v___f_393_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2));
v___f_394_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1));
v___f_395_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0));
v___x_396_ = lean_box(0);
v___x_397_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4);
v___x_398_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___f_395_);
lean_ctor_set(v___x_398_, 3, v___f_394_);
lean_ctor_set(v___x_398_, 4, v___f_393_);
lean_ctor_set(v___x_398_, 5, v___f_392_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object* v_00_u03b1_399_, lean_object* v_00_u03c3_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object* v_00_u03b1_402_, lean_object* v_00_u03c3_403_, lean_object* v_inst_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object* v_00_u03b1_406_, lean_object* v_00_u03c3_407_, lean_object* v_inst_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_SimplePersistentEnvExtension_instInhabited(v_00_u03b1_406_, v_00_u03c3_407_, v_inst_408_);
lean_dec(v_inst_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object* v_inst_410_, lean_object* v_ext_411_, lean_object* v_env_412_, lean_object* v_asyncMode_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_fst_418_; 
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v_inst_410_);
v___x_416_ = lean_box(0);
v___x_417_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_415_, v_ext_411_, v_env_412_, v_asyncMode_413_, v___x_416_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_fst_418_);
lean_dec(v___x_417_);
return v_fst_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object* v_inst_419_, lean_object* v_ext_420_, lean_object* v_env_421_, lean_object* v_asyncMode_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_419_, v_ext_420_, v_env_421_, v_asyncMode_422_);
lean_dec(v_asyncMode_422_);
lean_dec_ref(v_ext_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* v_00_u03b1_424_, lean_object* v_00_u03c3_425_, lean_object* v_inst_426_, lean_object* v_ext_427_, lean_object* v_env_428_, lean_object* v_asyncMode_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_426_, v_ext_427_, v_env_428_, v_asyncMode_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object* v_00_u03b1_431_, lean_object* v_00_u03c3_432_, lean_object* v_inst_433_, lean_object* v_ext_434_, lean_object* v_env_435_, lean_object* v_asyncMode_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_SimplePersistentEnvExtension_getEntries(v_00_u03b1_431_, v_00_u03c3_432_, v_inst_433_, v_ext_434_, v_env_435_, v_asyncMode_436_);
lean_dec(v_asyncMode_436_);
lean_dec_ref(v_ext_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object* v_inst_438_, lean_object* v_ext_439_, lean_object* v_env_440_, lean_object* v_asyncMode_441_, lean_object* v_asyncDecl_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_snd_446_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_inst_438_);
v___x_445_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_444_, v_ext_439_, v_env_440_, v_asyncMode_441_, v_asyncDecl_442_);
v_snd_446_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_snd_446_);
lean_dec(v___x_445_);
return v_snd_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object* v_inst_447_, lean_object* v_ext_448_, lean_object* v_env_449_, lean_object* v_asyncMode_450_, lean_object* v_asyncDecl_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_447_, v_ext_448_, v_env_449_, v_asyncMode_450_, v_asyncDecl_451_);
lean_dec(v_asyncMode_450_);
lean_dec_ref(v_ext_448_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* v_00_u03b1_453_, lean_object* v_00_u03c3_454_, lean_object* v_inst_455_, lean_object* v_ext_456_, lean_object* v_env_457_, lean_object* v_asyncMode_458_, lean_object* v_asyncDecl_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_455_, v_ext_456_, v_env_457_, v_asyncMode_458_, v_asyncDecl_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object* v_00_u03b1_461_, lean_object* v_00_u03c3_462_, lean_object* v_inst_463_, lean_object* v_ext_464_, lean_object* v_env_465_, lean_object* v_asyncMode_466_, lean_object* v_asyncDecl_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_SimplePersistentEnvExtension_getState(v_00_u03b1_461_, v_00_u03c3_462_, v_inst_463_, v_ext_464_, v_env_465_, v_asyncMode_466_, v_asyncDecl_467_);
lean_dec(v_asyncMode_466_);
lean_dec_ref(v_ext_464_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object* v_s_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_fst_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_fst_471_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_x_470_, 1);
lean_dec(v_unused_479_);
v___x_473_ = v_x_470_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_fst_471_);
lean_dec(v_x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_s_469_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_s_469_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object* v_ext_480_, lean_object* v_env_481_, lean_object* v_s_482_){
_start:
{
lean_object* v_toEnvExtension_483_; lean_object* v_asyncMode_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_toEnvExtension_483_ = lean_ctor_get(v_ext_480_, 0);
v_asyncMode_484_ = lean_ctor_get(v_toEnvExtension_483_, 2);
lean_inc(v_asyncMode_484_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_485_, 0, v_s_482_);
v___x_486_ = lean_box(0);
v___x_487_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_480_, v_env_481_, v___f_485_, v_asyncMode_484_, v___x_486_);
lean_dec(v_asyncMode_484_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* v_00_u03b1_488_, lean_object* v_00_u03c3_489_, lean_object* v_ext_490_, lean_object* v_env_491_, lean_object* v_s_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_490_, v_env_491_, v_s_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_fst_496_ = lean_ctor_get(v_x_495_, 0);
v_snd_497_ = lean_ctor_get(v_x_495_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v_x_495_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_inc(v_fst_496_);
lean_dec(v_x_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_apply_1(v_f_494_, v_snd_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_fst_496_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object* v_ext_506_, lean_object* v_env_507_, lean_object* v_f_508_){
_start:
{
lean_object* v_toEnvExtension_509_; lean_object* v_asyncMode_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_toEnvExtension_509_ = lean_ctor_get(v_ext_506_, 0);
v_asyncMode_510_ = lean_ctor_get(v_toEnvExtension_509_, 2);
lean_inc(v_asyncMode_510_);
v___f_511_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_511_, 0, v_f_508_);
v___x_512_ = lean_box(0);
v___x_513_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_506_, v_env_507_, v___f_511_, v_asyncMode_510_, v___x_512_);
lean_dec(v_asyncMode_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* v_00_u03b1_514_, lean_object* v_00_u03c3_515_, lean_object* v_ext_516_, lean_object* v_env_517_, lean_object* v_f_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(v_ext_516_, v_env_517_, v_f_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_NameSet_empty;
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_523_);
lean_dec_ref(v_x_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_as_526_, lean_object* v_lo_527_, lean_object* v_hi_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_lt(v_lo_527_, v_hi_528_);
if (v___x_529_ == 0)
{
lean_dec(v_lo_527_);
return v_as_526_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; uint8_t v___x_534_; 
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___closed__0));
lean_inc(v_lo_527_);
v___x_531_ = l_Array_qpartition___redArg(v_as_526_, v___x_530_, v_lo_527_, v_hi_528_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_531_);
v___x_534_ = lean_nat_dec_le(v_hi_528_, v_fst_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_snd_533_, v_lo_527_, v_fst_532_);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_fst_532_, v___x_536_);
lean_dec(v_fst_532_);
v_as_526_ = v___x_535_;
v_lo_527_ = v___x_537_;
goto _start;
}
else
{
lean_dec(v_fst_532_);
lean_dec(v_lo_527_);
return v_snd_533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_as_539_, lean_object* v_lo_540_, lean_object* v_hi_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_as_539_, v_lo_540_, v_hi_541_);
lean_dec(v_hi_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_544_ = lean_array_mk(v_es_543_);
v___x_545_ = lean_array_get_size(v___x_544_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_nat_dec_eq(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___y_551_; uint8_t v___x_555_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_sub(v___x_545_, v___x_548_);
v___x_555_ = lean_nat_dec_le(v___x_546_, v___x_549_);
if (v___x_555_ == 0)
{
lean_inc(v___x_549_);
v___y_551_ = v___x_549_;
goto v___jp_550_;
}
else
{
v___y_551_ = v___x_546_;
goto v___jp_550_;
}
v___jp_550_:
{
uint8_t v___x_552_; 
v___x_552_ = lean_nat_dec_le(v___y_551_, v___x_549_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec(v___x_549_);
lean_inc(v___y_551_);
v___x_553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_544_, v___y_551_, v___y_551_);
lean_dec(v___y_551_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_544_, v___y_551_, v___x_549_);
lean_dec(v___x_549_);
return v___x_554_;
}
}
}
else
{
return v___x_544_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_556_, lean_object* v_x2_557_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = l_Lean_NameSet_contains(v_x1_556_, v_x2_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = 1;
return v___x_559_;
}
else
{
uint8_t v___x_560_; 
v___x_560_ = 0;
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_561_, lean_object* v_x2_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_561_, v_x2_562_);
lean_dec(v_x2_562_);
lean_dec(v_x1_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_574_, lean_object* v_asyncMode_575_){
_start:
{
lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___f_577_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_578_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_579_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_580_ = lean_box(0);
v___x_581_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_582_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_582_, 0, v_name_574_);
lean_ctor_set(v___x_582_, 1, v___f_577_);
lean_ctor_set(v___x_582_, 2, v___f_578_);
lean_ctor_set(v___x_582_, 3, v___f_579_);
lean_ctor_set(v___x_582_, 4, v___x_580_);
lean_ctor_set(v___x_582_, 5, v_asyncMode_575_);
lean_ctor_set(v___x_582_, 6, v___x_581_);
v___x_583_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_584_, lean_object* v_asyncMode_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_mkTagDeclarationExtension(v_name_584_, v_asyncMode_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_588_, lean_object* v_as_589_, lean_object* v_lo_590_, lean_object* v_hi_591_, lean_object* v_w_592_, lean_object* v_hlo_593_, lean_object* v_hhi_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_as_589_, v_lo_590_, v_hi_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_596_, lean_object* v_as_597_, lean_object* v_lo_598_, lean_object* v_hi_599_, lean_object* v_w_600_, lean_object* v_hlo_601_, lean_object* v_hhi_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_596_, v_as_597_, v_lo_598_, v_hi_599_, v_w_600_, v_hlo_601_, v_hhi_602_);
lean_dec(v_hi_599_);
lean_dec(v_n_596_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_609_, v___y_610_);
lean_dec_ref(v___y_610_);
lean_dec_ref(v_x_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_613_, lean_object* v_x_614_){
_start:
{
lean_inc_ref(v_s_613_);
return v_s_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_615_, v_x_616_);
lean_dec(v_x_616_);
lean_dec_ref(v_s_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_620_, lean_object* v_x_621_, uint8_t v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0));
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_x_64__boxed_627_; lean_object* v_res_628_; 
v_x_64__boxed_627_ = lean_unbox(v_x_626_);
v_res_628_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_624_, v_x_625_, v_x_64__boxed_627_);
lean_dec_ref(v_x_625_);
lean_dec_ref(v_x_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_631_);
lean_dec_ref(v_x_631_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_637_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5(void){
_start:
{
lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___f_638_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_639_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_640_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_641_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_642_ = lean_box(0);
v___x_643_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
v___x_644_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___f_641_);
lean_ctor_set(v___x_644_, 3, v___f_640_);
lean_ctor_set(v___x_644_, 4, v___f_639_);
lean_ctor_set(v___x_644_, 5, v___f_638_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_647_, lean_object* v_msg_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_panic_fn(v_env_647_, v_msg_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_654_ = lean_unsigned_to_nat(4u);
v___x_655_ = lean_unsigned_to_nat(115u);
v___x_656_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_657_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_658_ = l_mkPanicMessageWithDecl(v___x_657_, v___x_656_, v___x_655_, v___x_654_, v___x_653_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_659_, lean_object* v_env_660_, lean_object* v_declName_661_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = l_Lean_Name_isAnonymous(v_declName_661_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_660_, v_declName_661_);
if (lean_obj_tag(v___x_667_) == 0)
{
goto v___jp_662_;
}
else
{
lean_dec_ref(v___x_667_);
if (v___x_666_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v_declName_661_);
lean_dec_ref(v_ext_659_);
v___x_668_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_669_ = lean_panic_fn(v_env_660_, v___x_668_);
return v___x_669_;
}
else
{
goto v___jp_662_;
}
}
}
else
{
lean_dec(v_declName_661_);
lean_dec_ref(v_ext_659_);
return v_env_660_;
}
v___jp_662_:
{
lean_object* v_toEnvExtension_663_; lean_object* v_asyncMode_664_; lean_object* v___x_665_; 
v_toEnvExtension_663_ = lean_ctor_get(v_ext_659_, 0);
v_asyncMode_664_ = lean_ctor_get(v_toEnvExtension_663_, 2);
lean_inc(v_asyncMode_664_);
lean_inc(v_declName_661_);
v___x_665_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_659_, v_env_660_, v_declName_661_, v_asyncMode_664_, v_declName_661_);
lean_dec(v_asyncMode_664_);
return v___x_665_;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object* v_as_670_, lean_object* v_k_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_m_676_; lean_object* v_a_677_; uint8_t v___x_678_; 
v___x_674_ = lean_nat_add(v_x_672_, v_x_673_);
v___x_675_ = lean_unsigned_to_nat(1u);
v_m_676_ = lean_nat_shiftr(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
v_a_677_ = lean_array_fget_borrowed(v_as_670_, v_m_676_);
v___x_678_ = l_Lean_Name_quickLt(v_a_677_, v_k_671_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
lean_dec(v_x_673_);
v___x_679_ = l_Lean_Name_quickLt(v_k_671_, v_a_677_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
lean_dec(v_m_676_);
lean_dec(v_x_672_);
v___x_680_ = 1;
return v___x_680_;
}
else
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_dec_eq(v_m_676_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_nat_sub(v_m_676_, v___x_675_);
lean_dec(v_m_676_);
v___x_684_ = lean_nat_dec_lt(v___x_683_, v_x_672_);
if (v___x_684_ == 0)
{
v_x_673_ = v___x_683_;
goto _start;
}
else
{
lean_dec(v___x_683_);
lean_dec(v_x_672_);
return v___x_678_;
}
}
else
{
lean_dec(v_m_676_);
lean_dec(v_x_672_);
return v___x_678_;
}
}
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; 
lean_dec(v_x_672_);
v___x_686_ = lean_nat_add(v_m_676_, v___x_675_);
lean_dec(v_m_676_);
v___x_687_ = lean_nat_dec_le(v___x_686_, v_x_673_);
if (v___x_687_ == 0)
{
lean_dec(v___x_686_);
lean_dec(v_x_673_);
return v___x_687_;
}
else
{
v_x_672_ = v___x_686_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object* v_as_689_, lean_object* v_k_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v_as_689_, v_k_690_, v_x_691_, v_x_692_);
lean_dec(v_k_690_);
lean_dec_ref(v_as_689_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_698_, lean_object* v_env_699_, lean_object* v_declName_700_, lean_object* v_asyncMode_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(1);
v___x_703_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_699_, v_declName_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_704_; uint8_t v___x_705_; 
lean_inc(v_declName_700_);
v___x_704_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_702_, v_ext_698_, v_env_699_, v_asyncMode_701_, v_declName_700_);
v___x_705_ = l_Lean_NameSet_contains(v___x_704_, v_declName_700_);
lean_dec(v_declName_700_);
lean_dec(v___x_704_);
return v___x_705_;
}
else
{
lean_object* v_val_706_; lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_val_706_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_706_);
lean_dec_ref(v___x_703_);
v___x_707_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_708_ = 0;
v___x_709_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_707_, v_ext_698_, v_env_699_, v_val_706_, v___x_708_);
lean_dec(v_val_706_);
lean_dec_ref(v_env_699_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_array_get_size(v___x_709_);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_709_);
lean_dec(v_declName_700_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_nat_sub(v___x_711_, v___x_713_);
v___x_715_ = lean_nat_dec_le(v___x_710_, v___x_714_);
if (v___x_715_ == 0)
{
lean_dec(v___x_714_);
lean_dec_ref(v___x_709_);
lean_dec(v_declName_700_);
return v___x_715_;
}
else
{
uint8_t v___x_716_; 
v___x_716_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_709_, v_declName_700_, v___x_710_, v___x_714_);
lean_dec(v_declName_700_);
lean_dec_ref(v___x_709_);
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_717_, lean_object* v_env_718_, lean_object* v_declName_719_, lean_object* v_asyncMode_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_717_, v_env_718_, v_declName_719_, v_asyncMode_720_);
lean_dec(v_asyncMode_720_);
lean_dec_ref(v_ext_717_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object* v_as_723_, lean_object* v_k_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v_as_723_, v_k_724_, v_x_725_, v_x_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object* v_as_729_, lean_object* v_k_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v_as_729_, v_k_730_, v_x_731_, v_x_732_, v_x_733_);
lean_dec(v_k_730_);
lean_dec_ref(v_as_729_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(lean_object* v_x_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed(lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(v_x_741_, v___y_742_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v_x_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(lean_object* v_s_745_, lean_object* v_x_746_){
_start:
{
lean_inc(v_s_745_);
return v_s_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed(lean_object* v_s_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(v_s_747_, v_x_748_);
lean_dec_ref(v_x_748_);
lean_dec(v_s_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(lean_object* v_x_752_, lean_object* v_x_753_, uint8_t v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0));
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_x_70__boxed_759_; lean_object* v_res_760_; 
v_x_70__boxed_759_ = lean_unbox(v_x_758_);
v_res_760_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(v_x_756_, v_x_757_, v_x_70__boxed_759_);
lean_dec(v_x_757_);
lean_dec_ref(v_x_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_box(0);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed(lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(v_x_763_);
lean_dec(v_x_763_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__4(void){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_769_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__5(void){
_start:
{
lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___f_770_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__3));
v___f_771_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__2));
v___f_772_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__1));
v___f_773_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__0));
v___x_774_ = lean_box(0);
v___x_775_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__4);
v___x_776_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
lean_ctor_set(v___x_776_, 2, v___f_773_);
lean_ctor_set(v___x_776_, 3, v___f_772_);
lean_ctor_set(v___x_776_, 4, v___f_771_);
lean_ctor_set(v___x_776_, 5, v___f_770_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_a_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__5, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__5_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__5);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension___closed__0(void){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_instInhabitedMapDeclarationExtension_default(lean_box(0));
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension___closed__0, &l_Lean_instInhabitedMapDeclarationExtension___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension___closed__0);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_787_; 
v_fst_785_ = lean_ctor_get(v_x_784_, 0);
lean_inc(v_fst_785_);
v_snd_786_ = lean_ctor_get(v_x_784_, 1);
lean_inc(v_snd_786_);
lean_dec_ref(v_x_784_);
v___x_787_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_785_, v_snd_786_, v_s_783_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_788_, lean_object* v_env_789_, lean_object* v_s_790_, uint8_t v_level_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_box(v_level_791_);
v___x_793_ = lean_apply_3(v_exportEntriesFn_788_, v_env_789_, v_s_790_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1___boxed(lean_object* v_exportEntriesFn_794_, lean_object* v_env_795_, lean_object* v_s_796_, lean_object* v_level_797_){
_start:
{
uint8_t v_level_boxed_798_; lean_object* v_res_799_; 
v_level_boxed_798_ = lean_unbox(v_level_797_);
v_res_799_ = l_Lean_mkMapDeclarationExtension___redArg___lam__1(v_exportEntriesFn_794_, v_env_795_, v_s_796_, v_level_boxed_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
return v_x_801_;
}
else
{
lean_object* v_head_803_; lean_object* v_tail_804_; lean_object* v___x_805_; 
v_head_803_ = lean_ctor_get(v_x_802_, 0);
lean_inc(v_head_803_);
v_tail_804_ = lean_ctor_get(v_x_802_, 1);
lean_inc(v_tail_804_);
lean_dec_ref(v_x_802_);
v___x_805_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_800_, v_head_803_);
if (lean_obj_tag(v___x_805_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_807_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref(v___x_805_);
v___x_807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_803_, v_val_806_, v_x_801_);
v_x_801_ = v___x_807_;
v_x_802_ = v_tail_804_;
goto _start;
}
else
{
lean_dec(v___x_805_);
lean_dec(v_head_803_);
v_x_802_ = v_tail_804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_810_, v_x_811_, v_x_812_);
lean_dec(v_newState_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_814_, lean_object* v_newState_815_, lean_object* v_newConsts_816_, lean_object* v_s_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_815_, v_s_817_, v_newConsts_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_819_, lean_object* v_newState_820_, lean_object* v_newConsts_821_, lean_object* v_s_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_819_, v_newState_820_, v_newConsts_821_, v_s_822_);
lean_dec(v_newState_820_);
lean_dec(v_x_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_826_);
lean_dec(v_x_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_834_, lean_object* v_x_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_834_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_839_, v_x_840_, v___y_841_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v_x_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_853_, lean_object* v_asyncMode_854_, lean_object* v_exportEntriesFn_855_){
_start:
{
lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___f_857_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_858_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_858_, 0, v_exportEntriesFn_855_);
v___f_859_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__3));
v___f_860_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_861_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_862_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_863_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_864_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_864_, 0, v_name_853_);
lean_ctor_set(v___x_864_, 1, v___f_861_);
lean_ctor_set(v___x_864_, 2, v___f_862_);
lean_ctor_set(v___x_864_, 3, v___f_857_);
lean_ctor_set(v___x_864_, 4, v___f_858_);
lean_ctor_set(v___x_864_, 5, v___f_859_);
lean_ctor_set(v___x_864_, 6, v_asyncMode_854_);
lean_ctor_set(v___x_864_, 7, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___f_860_);
v___x_866_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
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
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_866_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_866_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_883_, lean_object* v_asyncMode_884_, lean_object* v_exportEntriesFn_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_883_, v_asyncMode_884_, v_exportEntriesFn_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_888_, lean_object* v_name_889_, lean_object* v_asyncMode_890_, lean_object* v_exportEntriesFn_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_889_, v_asyncMode_890_, v_exportEntriesFn_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_894_, lean_object* v_name_895_, lean_object* v_asyncMode_896_, lean_object* v_exportEntriesFn_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_894_, v_name_895_, v_asyncMode_896_, v_exportEntriesFn_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_900_, lean_object* v_newState_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_901_, v_x_902_, v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_905_, lean_object* v_newState_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_905_, v_newState_906_, v_x_907_, v_x_908_);
lean_dec(v_newState_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_915_, lean_object* v_env_916_, lean_object* v_declName_917_, lean_object* v_val_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_916_, v_declName_917_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v_val_920_; lean_object* v_name_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_val_918_);
v_val_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_920_);
lean_dec_ref(v___x_919_);
v_name_921_ = lean_ctor_get(v_ext_915_, 1);
lean_inc(v_name_921_);
lean_dec_ref(v_ext_915_);
v___x_922_ = lean_box(0);
v___x_923_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_924_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_925_ = lean_unsigned_to_nat(157u);
v___x_926_ = lean_unsigned_to_nat(4u);
v___x_927_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_928_ = 1;
v___x_929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_917_, v___x_928_);
v___x_930_ = lean_string_append(v___x_927_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_921_, v___x_928_);
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
v___x_937_ = l_Lean_Environment_allImportedModuleNames(v_env_916_);
v___x_938_ = lean_array_get(v___x_922_, v___x_937_, v_val_920_);
lean_dec(v_val_920_);
lean_dec_ref(v___x_937_);
v___x_939_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_938_, v___x_928_);
v___x_940_ = lean_string_append(v___x_936_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
v___x_943_ = l_mkPanicMessageWithDecl(v___x_923_, v___x_924_, v___x_925_, v___x_926_, v___x_942_);
lean_dec_ref(v___x_942_);
v___x_944_ = lean_panic_fn(v_env_916_, v___x_943_);
return v___x_944_;
}
else
{
lean_object* v_toEnvExtension_945_; lean_object* v_asyncMode_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v___x_919_);
v_toEnvExtension_945_ = lean_ctor_get(v_ext_915_, 0);
v_asyncMode_946_ = lean_ctor_get(v_toEnvExtension_945_, 2);
lean_inc(v_asyncMode_946_);
lean_inc(v_declName_917_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_declName_917_);
lean_ctor_set(v___x_947_, 1, v_val_918_);
v___x_948_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_915_, v_env_916_, v___x_947_, v_asyncMode_946_, v_declName_917_);
lean_dec(v_asyncMode_946_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_949_, lean_object* v_ext_950_, lean_object* v_env_951_, lean_object* v_declName_952_, lean_object* v_val_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_950_, v_env_951_, v_declName_952_, v_val_953_);
return v___x_954_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object* v_a_955_, lean_object* v_b_956_){
_start:
{
lean_object* v_fst_957_; lean_object* v_fst_958_; uint8_t v___x_959_; 
v_fst_957_ = lean_ctor_get(v_a_955_, 0);
v_fst_958_ = lean_ctor_get(v_b_956_, 0);
v___x_959_ = l_Lean_Name_quickLt(v_fst_957_, v_fst_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object* v_a_960_, lean_object* v_b_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_960_, v_b_961_);
lean_dec_ref(v_b_961_);
lean_dec_ref(v_a_960_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_inst_966_, lean_object* v_ext_967_, lean_object* v_env_968_, lean_object* v_declName_969_, lean_object* v_asyncMode_970_, uint8_t v_level_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_box(1);
v___x_973_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_968_, v_declName_969_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_inst_966_);
lean_inc(v_declName_969_);
v___x_974_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_972_, v_ext_967_, v_env_968_, v_asyncMode_970_, v_declName_969_);
v___x_975_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_974_, v_declName_969_);
lean_dec(v_declName_969_);
lean_dec(v___x_974_);
return v___x_975_;
}
else
{
lean_object* v_val_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_val_976_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_976_);
lean_dec_ref(v___x_973_);
v___x_977_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_972_, v_ext_967_, v_env_968_, v_val_976_, v_level_971_);
lean_dec(v_val_976_);
lean_dec_ref(v_env_968_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_array_get_size(v___x_977_);
v___x_980_ = lean_nat_dec_lt(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec_ref(v___x_977_);
lean_dec(v_declName_969_);
lean_dec(v_inst_966_);
v___x_981_ = lean_box(0);
return v___x_981_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_sub(v___x_979_, v___x_982_);
v___x_984_ = lean_nat_dec_le(v___x_978_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec(v___x_983_);
lean_dec_ref(v___x_977_);
lean_dec(v_declName_969_);
lean_dec(v_inst_966_);
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
lean_object* v___f_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___f_986_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_declName_969_);
lean_ctor_set(v___x_987_, 1, v_inst_966_);
v___x_988_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1));
v___x_989_ = l_Array_binSearchAux___redArg(v___f_986_, v___x_988_, v___x_977_, v___x_987_, v___x_978_, v___x_983_);
lean_dec_ref(v___x_977_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_box(0);
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_val_991_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_val_991_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_snd_995_; lean_object* v___x_997_; 
v_snd_995_ = lean_ctor_get(v_val_991_, 1);
lean_inc(v_snd_995_);
lean_dec(v_val_991_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_snd_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_snd_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_inst_1000_, lean_object* v_ext_1001_, lean_object* v_env_1002_, lean_object* v_declName_1003_, lean_object* v_asyncMode_1004_, lean_object* v_level_1005_){
_start:
{
uint8_t v_level_boxed_1006_; lean_object* v_res_1007_; 
v_level_boxed_1006_ = lean_unbox(v_level_1005_);
v_res_1007_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1000_, v_ext_1001_, v_env_1002_, v_declName_1003_, v_asyncMode_1004_, v_level_boxed_1006_);
lean_dec(v_asyncMode_1004_);
lean_dec_ref(v_ext_1001_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1008_, lean_object* v_inst_1009_, lean_object* v_ext_1010_, lean_object* v_env_1011_, lean_object* v_declName_1012_, lean_object* v_asyncMode_1013_, uint8_t v_level_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1009_, v_ext_1010_, v_env_1011_, v_declName_1012_, v_asyncMode_1013_, v_level_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_inst_1017_, lean_object* v_ext_1018_, lean_object* v_env_1019_, lean_object* v_declName_1020_, lean_object* v_asyncMode_1021_, lean_object* v_level_1022_){
_start:
{
uint8_t v_level_boxed_1023_; lean_object* v_res_1024_; 
v_level_boxed_1023_ = lean_unbox(v_level_1022_);
v_res_1024_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1016_, v_inst_1017_, v_ext_1018_, v_env_1019_, v_declName_1020_, v_asyncMode_1021_, v_level_boxed_1023_);
lean_dec(v_asyncMode_1021_);
lean_dec_ref(v_ext_1018_);
return v_res_1024_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_inst_1026_, lean_object* v_ext_1027_, lean_object* v_env_1028_, lean_object* v_declName_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_box(1);
v___x_1031_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1028_, v_declName_1029_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_toEnvExtension_1032_; lean_object* v_asyncMode_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
lean_dec(v_inst_1026_);
v_toEnvExtension_1032_ = lean_ctor_get(v_ext_1027_, 0);
v_asyncMode_1033_ = lean_ctor_get(v_toEnvExtension_1032_, 2);
lean_inc(v_declName_1029_);
v___x_1034_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1030_, v_ext_1027_, v_env_1028_, v_asyncMode_1033_, v_declName_1029_);
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1029_, v___x_1034_);
lean_dec(v___x_1034_);
lean_dec(v_declName_1029_);
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_val_1036_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1036_);
lean_dec_ref(v___x_1031_);
v___x_1037_ = 0;
v___x_1038_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1030_, v_ext_1027_, v_env_1028_, v_val_1036_, v___x_1037_);
lean_dec(v_val_1036_);
lean_dec_ref(v_env_1028_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v___x_1038_);
v___x_1041_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec_ref(v___x_1038_);
lean_dec(v_declName_1029_);
lean_dec(v_inst_1026_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_nat_sub(v___x_1040_, v___x_1042_);
v___x_1044_ = lean_nat_dec_le(v___x_1039_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec(v___x_1043_);
lean_dec_ref(v___x_1038_);
lean_dec(v_declName_1029_);
lean_dec(v_inst_1026_);
return v___x_1044_;
}
else
{
lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___f_1045_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_declName_1029_);
lean_ctor_set(v___x_1046_, 1, v_inst_1026_);
v___x_1047_ = ((lean_object*)(l_Lean_MapDeclarationExtension_contains___redArg___closed__0));
v___x_1048_ = l_Array_binSearchAux___redArg(v___f_1045_, v___x_1047_, v___x_1038_, v___x_1046_, v___x_1039_, v___x_1043_);
lean_dec_ref(v___x_1038_);
v___x_1049_ = lean_unbox(v___x_1048_);
lean_dec(v___x_1048_);
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_inst_1050_, lean_object* v_ext_1051_, lean_object* v_env_1052_, lean_object* v_declName_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1050_, v_ext_1051_, v_env_1052_, v_declName_1053_);
lean_dec_ref(v_ext_1051_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1056_, lean_object* v_inst_1057_, lean_object* v_ext_1058_, lean_object* v_env_1059_, lean_object* v_declName_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1057_, v_ext_1058_, v_env_1059_, v_declName_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1062_, lean_object* v_inst_1063_, lean_object* v_ext_1064_, lean_object* v_env_1065_, lean_object* v_declName_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1062_, v_inst_1063_, v_ext_1064_, v_env_1065_, v_declName_1066_);
lean_dec_ref(v_ext_1064_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TagDeclarationExtension_instInhabited___aux__1 = _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1();
lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabited___aux__1);
l_Lean_TagDeclarationExtension_instInhabited = _init_l_Lean_TagDeclarationExtension_instInhabited();
lean_mark_persistent(l_Lean_TagDeclarationExtension_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_EnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam = _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam();
lean_mark_persistent(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam);
l_Lean_mkTagDeclarationExtension___auto__1 = _init_l_Lean_mkTagDeclarationExtension___auto__1();
lean_mark_persistent(l_Lean_mkTagDeclarationExtension___auto__1);
l_Lean_mkMapDeclarationExtension___auto__3 = _init_l_Lean_mkMapDeclarationExtension___auto__3();
lean_mark_persistent(l_Lean_mkMapDeclarationExtension___auto__3);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_EnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_EnvExtension(builtin);
}
#ifdef __cplusplus
}
#endif
