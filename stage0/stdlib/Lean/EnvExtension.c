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
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value),((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value),((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value)}};
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value),((lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value),((lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__0_value)}};
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0_value;
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1 = (const lean_object*)&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1_value;
static const lean_closure_object l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_139_, 2);
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(lean_object* v_exportEntriesFnEx_x3f_211_, lean_object* v_toArrayFn_212_, lean_object* v_env_213_, lean_object* v_s_214_){
_start:
{
if (lean_obj_tag(v_exportEntriesFnEx_x3f_211_) == 0)
{
lean_object* v_fst_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_env_213_);
v_fst_215_ = lean_ctor_get(v_s_214_, 0);
lean_inc(v_fst_215_);
lean_dec_ref(v_s_214_);
v___x_216_ = l_List_reverse___redArg(v_fst_215_);
v___x_217_ = lean_apply_1(v_toArrayFn_212_, v___x_216_);
lean_inc_ref_n(v___x_217_, 2);
v___x_218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v_toArrayFn_212_);
v_val_219_ = lean_ctor_get(v_exportEntriesFnEx_x3f_211_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v_exportEntriesFnEx_x3f_211_, 1);
v_fst_220_ = lean_ctor_get(v_s_214_, 0);
lean_inc(v_fst_220_);
v_snd_221_ = lean_ctor_get(v_s_214_, 1);
lean_inc(v_snd_221_);
lean_dec_ref(v_s_214_);
v___x_222_ = l_List_reverse___redArg(v_fst_220_);
v___x_223_ = lean_apply_3(v_val_219_, v_env_213_, v_snd_221_, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2(lean_object* v_s_227_){
_start:
{
lean_object* v_fst_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_239_; 
v_fst_228_ = lean_ctor_get(v_s_227_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_s_227_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v_s_227_, 1);
lean_dec(v_unused_240_);
v___x_230_ = v_s_227_;
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_fst_228_);
lean_dec(v_s_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_232_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1));
v___x_233_ = l_List_lengthTR___redArg(v_fst_228_);
lean_dec(v_fst_228_);
v___x_234_ = l_Nat_reprFast(v___x_233_);
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 5);
lean_ctor_set(v___x_230_, 1, v___x_235_);
lean_ctor_set(v___x_230_, 0, v___x_232_);
v___x_237_ = v___x_230_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0));
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed(lean_object* v_x_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(v_x_245_);
lean_dec_ref(v_x_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(lean_object* v_addImportedFn_247_, lean_object* v___x_248_, lean_object* v_as_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_apply_1(v_addImportedFn_247_, v_as_249_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_248_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed(lean_object* v_addImportedFn_255_, lean_object* v___x_256_, lean_object* v_as_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(v_addImportedFn_255_, v___x_256_, v_as_257_, v___y_258_);
lean_dec_ref(v___y_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object* v___x_261_, lean_object* v_val_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_fst_267_; lean_object* v_snd_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v_fst_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_newEntries_276_; lean_object* v___x_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_fst_267_ = lean_ctor_get(v___y_266_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v___y_266_, 1);
lean_inc(v_snd_268_);
lean_dec_ref(v___y_266_);
v_fst_269_ = lean_ctor_get(v___y_264_, 0);
lean_inc_n(v_fst_269_, 2);
v_snd_270_ = lean_ctor_get(v___y_264_, 1);
lean_inc(v_snd_270_);
lean_dec_ref(v___y_264_);
v_fst_271_ = lean_ctor_get(v___y_263_, 0);
v___x_272_ = l_List_lengthTR___redArg(v_fst_269_);
v___x_273_ = l_List_lengthTR___redArg(v_fst_271_);
v___x_274_ = lean_nat_sub(v___x_272_, v___x_273_);
lean_dec(v___x_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_261_);
v_newEntries_276_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_269_, v_fst_269_, v___x_274_, v___x_275_);
lean_dec(v_fst_269_);
v___x_277_ = lean_apply_3(v_val_262_, v_newEntries_276_, v_snd_270_, v_snd_268_);
v_fst_278_ = lean_ctor_get(v___x_277_, 0);
v_snd_279_ = lean_ctor_get(v___x_277_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_277_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snd_279_);
lean_inc(v_fst_278_);
lean_dec(v___x_277_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = l_List_appendTR___redArg(v_fst_278_, v_fst_267_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_279_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object* v___x_288_, lean_object* v_val_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(v___x_288_, v_val_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_290_);
lean_dec(v___x_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object* v_descr_299_){
_start:
{
lean_object* v_name_301_; lean_object* v_addEntryFn_302_; lean_object* v_addImportedFn_303_; lean_object* v_toArrayFn_304_; lean_object* v_exportEntriesFnEx_x3f_305_; lean_object* v_asyncMode_306_; lean_object* v_replay_x3f_307_; lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v___f_310_; lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___y_320_; 
v_name_301_ = lean_ctor_get(v_descr_299_, 0);
lean_inc(v_name_301_);
v_addEntryFn_302_ = lean_ctor_get(v_descr_299_, 1);
lean_inc(v_addEntryFn_302_);
v_addImportedFn_303_ = lean_ctor_get(v_descr_299_, 2);
lean_inc_n(v_addImportedFn_303_, 2);
v_toArrayFn_304_ = lean_ctor_get(v_descr_299_, 3);
lean_inc_ref(v_toArrayFn_304_);
v_exportEntriesFnEx_x3f_305_ = lean_ctor_get(v_descr_299_, 4);
lean_inc(v_exportEntriesFnEx_x3f_305_);
v_asyncMode_306_ = lean_ctor_get(v_descr_299_, 5);
lean_inc(v_asyncMode_306_);
v_replay_x3f_307_ = lean_ctor_get(v_descr_299_, 6);
lean_inc(v_replay_x3f_307_);
lean_dec_ref(v_descr_299_);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0), 3, 1);
lean_closure_set(v___f_308_, 0, v_addEntryFn_302_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1), 4, 2);
lean_closure_set(v___f_309_, 0, v_exportEntriesFnEx_x3f_305_);
lean_closure_set(v___f_309_, 1, v_toArrayFn_304_);
v___f_310_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0));
v___f_311_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1));
v___x_312_ = lean_box(0);
v___f_313_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_313_, 0, v_addImportedFn_303_);
lean_closure_set(v___f_313_, 1, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2));
v___x_316_ = lean_apply_1(v_addImportedFn_303_, v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_312_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_318_, 0, lean_box(0));
lean_closure_set(v___x_318_, 1, lean_box(0));
lean_closure_set(v___x_318_, 2, v___x_317_);
if (lean_obj_tag(v_replay_x3f_307_) == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
v___y_320_ = v___x_324_;
goto v___jp_319_;
}
else
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_val_325_ = lean_ctor_get(v_replay_x3f_307_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_replay_x3f_307_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v_replay_x3f_307_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_replay_x3f_307_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___f_329_; lean_object* v___x_331_; 
v___f_329_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_329_, 0, v___x_314_);
lean_closure_set(v___f_329_, 1, v_val_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___f_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___f_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
v___y_320_ = v___x_331_;
goto v___jp_319_;
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_321_, 0, v_name_301_);
lean_ctor_set(v___x_321_, 1, v___x_318_);
lean_ctor_set(v___x_321_, 2, v___f_313_);
lean_ctor_set(v___x_321_, 3, v___f_308_);
lean_ctor_set(v___x_321_, 4, v___f_309_);
lean_ctor_set(v___x_321_, 5, v___f_310_);
lean_ctor_set(v___x_321_, 6, v_asyncMode_306_);
lean_ctor_set(v___x_321_, 7, v___y_320_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___f_311_);
v___x_323_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object* v_descr_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* v_00_u03b1_337_, lean_object* v_00_u03c3_338_, lean_object* v_inst_339_, lean_object* v_descr_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03c3_344_, lean_object* v_inst_345_, lean_object* v_descr_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_registerSimplePersistentEnvExtension(v_00_u03b1_343_, v_00_u03c3_344_, v_inst_345_, v_descr_346_);
lean_dec(v_inst_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(lean_object* v_x_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0(v_x_357_, v___y_358_);
lean_dec_ref(v___y_358_);
lean_dec_ref(v_x_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(lean_object* v_s_361_, lean_object* v_x_362_){
_start:
{
lean_inc_ref(v_s_361_);
return v_s_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__1(v_s_363_, v_x_364_);
lean_dec(v_x_364_);
lean_dec_ref(v_s_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___closed__0));
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__2(v_x_371_, v_x_372_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__3(v_x_376_);
lean_dec_ref(v_x_376_);
return v_res_377_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_382_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5(void){
_start:
{
lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___f_383_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__3));
v___f_384_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__2));
v___f_385_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__1));
v___f_386_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__0));
v___x_387_ = lean_box(0);
v___x_388_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__4);
v___x_389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___f_386_);
lean_ctor_set(v___x_389_, 3, v___f_385_);
lean_ctor_set(v___x_389_, 4, v___f_384_);
lean_ctor_set(v___x_389_, 5, v___f_383_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object* v_00_u03b1_390_, lean_object* v_00_u03c3_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object* v_00_u03b1_393_, lean_object* v_00_u03c3_394_, lean_object* v_inst_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___closed__5);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object* v_00_u03b1_397_, lean_object* v_00_u03c3_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_SimplePersistentEnvExtension_instInhabited(v_00_u03b1_397_, v_00_u03c3_398_, v_inst_399_);
lean_dec(v_inst_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object* v_inst_401_, lean_object* v_ext_402_, lean_object* v_env_403_, lean_object* v_asyncMode_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_fst_409_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_inst_401_);
v___x_407_ = lean_box(0);
v___x_408_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_406_, v_ext_402_, v_env_403_, v_asyncMode_404_, v___x_407_);
v_fst_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_fst_409_);
lean_dec(v___x_408_);
return v_fst_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object* v_inst_410_, lean_object* v_ext_411_, lean_object* v_env_412_, lean_object* v_asyncMode_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_410_, v_ext_411_, v_env_412_, v_asyncMode_413_);
lean_dec(v_asyncMode_413_);
lean_dec_ref(v_ext_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* v_00_u03b1_415_, lean_object* v_00_u03c3_416_, lean_object* v_inst_417_, lean_object* v_ext_418_, lean_object* v_env_419_, lean_object* v_asyncMode_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_417_, v_ext_418_, v_env_419_, v_asyncMode_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object* v_00_u03b1_422_, lean_object* v_00_u03c3_423_, lean_object* v_inst_424_, lean_object* v_ext_425_, lean_object* v_env_426_, lean_object* v_asyncMode_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_SimplePersistentEnvExtension_getEntries(v_00_u03b1_422_, v_00_u03c3_423_, v_inst_424_, v_ext_425_, v_env_426_, v_asyncMode_427_);
lean_dec(v_asyncMode_427_);
lean_dec_ref(v_ext_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object* v_inst_429_, lean_object* v_ext_430_, lean_object* v_env_431_, lean_object* v_asyncMode_432_, lean_object* v_asyncDecl_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_snd_437_; 
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_inst_429_);
v___x_436_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_435_, v_ext_430_, v_env_431_, v_asyncMode_432_, v_asyncDecl_433_);
v_snd_437_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_437_);
lean_dec(v___x_436_);
return v_snd_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object* v_inst_438_, lean_object* v_ext_439_, lean_object* v_env_440_, lean_object* v_asyncMode_441_, lean_object* v_asyncDecl_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_438_, v_ext_439_, v_env_440_, v_asyncMode_441_, v_asyncDecl_442_);
lean_dec(v_asyncMode_441_);
lean_dec_ref(v_ext_439_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* v_00_u03b1_444_, lean_object* v_00_u03c3_445_, lean_object* v_inst_446_, lean_object* v_ext_447_, lean_object* v_env_448_, lean_object* v_asyncMode_449_, lean_object* v_asyncDecl_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_446_, v_ext_447_, v_env_448_, v_asyncMode_449_, v_asyncDecl_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object* v_00_u03b1_452_, lean_object* v_00_u03c3_453_, lean_object* v_inst_454_, lean_object* v_ext_455_, lean_object* v_env_456_, lean_object* v_asyncMode_457_, lean_object* v_asyncDecl_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_SimplePersistentEnvExtension_getState(v_00_u03b1_452_, v_00_u03c3_453_, v_inst_454_, v_ext_455_, v_env_456_, v_asyncMode_457_, v_asyncDecl_458_);
lean_dec(v_asyncMode_457_);
lean_dec_ref(v_ext_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object* v_s_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_fst_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_fst_462_ = lean_ctor_get(v_x_461_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_x_461_, 1);
lean_dec(v_unused_470_);
v___x_464_ = v_x_461_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_fst_462_);
lean_dec(v_x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_s_460_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fst_462_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_s_460_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object* v_ext_471_, lean_object* v_env_472_, lean_object* v_s_473_){
_start:
{
lean_object* v_toEnvExtension_474_; lean_object* v_asyncMode_475_; lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_toEnvExtension_474_ = lean_ctor_get(v_ext_471_, 0);
v_asyncMode_475_ = lean_ctor_get(v_toEnvExtension_474_, 2);
lean_inc(v_asyncMode_475_);
v___f_476_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_476_, 0, v_s_473_);
v___x_477_ = lean_box(0);
v___x_478_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_471_, v_env_472_, v___f_476_, v_asyncMode_475_, v___x_477_);
lean_dec(v_asyncMode_475_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* v_00_u03b1_479_, lean_object* v_00_u03c3_480_, lean_object* v_ext_481_, lean_object* v_env_482_, lean_object* v_s_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_481_, v_env_482_, v_s_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_485_, lean_object* v_x_486_){
_start:
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_fst_487_ = lean_ctor_get(v_x_486_, 0);
v_snd_488_ = lean_ctor_get(v_x_486_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v_x_486_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_x_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_apply_1(v_f_485_, v_snd_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object* v_ext_497_, lean_object* v_env_498_, lean_object* v_f_499_){
_start:
{
lean_object* v_toEnvExtension_500_; lean_object* v_asyncMode_501_; lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_toEnvExtension_500_ = lean_ctor_get(v_ext_497_, 0);
v_asyncMode_501_ = lean_ctor_get(v_toEnvExtension_500_, 2);
lean_inc(v_asyncMode_501_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_502_, 0, v_f_499_);
v___x_503_ = lean_box(0);
v___x_504_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_497_, v_env_498_, v___f_502_, v_asyncMode_501_, v___x_503_);
lean_dec(v_asyncMode_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* v_00_u03b1_505_, lean_object* v_00_u03c3_506_, lean_object* v_ext_507_, lean_object* v_env_508_, lean_object* v_f_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(v_ext_507_, v_env_508_, v_f_509_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_NameSet_empty;
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_514_);
lean_dec_ref(v_x_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object* v_hi_516_, lean_object* v_pivot_517_, lean_object* v_as_518_, lean_object* v_i_519_, lean_object* v_k_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_lt(v_k_520_, v_hi_516_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_k_520_);
v___x_522_ = lean_array_fswap(v_as_518_, v_i_519_, v_hi_516_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_i_519_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_array_fget_borrowed(v_as_518_, v_k_520_);
v___x_525_ = l_Lean_Name_quickLt(v___x_524_, v_pivot_517_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_k_520_, v___x_526_);
lean_dec(v_k_520_);
v_k_520_ = v___x_527_;
goto _start;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_529_ = lean_array_fswap(v_as_518_, v_i_519_, v_k_520_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_i_519_, v___x_530_);
lean_dec(v_i_519_);
v___x_532_ = lean_nat_add(v_k_520_, v___x_530_);
lean_dec(v_k_520_);
v_as_518_ = v___x_529_;
v_i_519_ = v___x_531_;
v_k_520_ = v___x_532_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object* v_hi_534_, lean_object* v_pivot_535_, lean_object* v_as_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_534_, v_pivot_535_, v_as_536_, v_i_537_, v_k_538_);
lean_dec(v_pivot_535_);
lean_dec(v_hi_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_n_540_, lean_object* v_as_541_, lean_object* v_lo_542_, lean_object* v_hi_543_){
_start:
{
lean_object* v___y_545_; uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_lt(v_lo_542_, v_hi_543_);
if (v___x_555_ == 0)
{
lean_dec(v_lo_542_);
return v_as_541_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_mid_558_; lean_object* v___y_560_; lean_object* v___y_566_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_556_ = lean_nat_add(v_lo_542_, v_hi_543_);
v___x_557_ = lean_unsigned_to_nat(1u);
v_mid_558_ = lean_nat_shiftr(v___x_556_, v___x_557_);
lean_dec(v___x_556_);
v___x_571_ = lean_array_fget_borrowed(v_as_541_, v_mid_558_);
v___x_572_ = lean_array_fget_borrowed(v_as_541_, v_lo_542_);
v___x_573_ = l_Lean_Name_quickLt(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
v___y_566_ = v_as_541_;
goto v___jp_565_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = lean_array_fswap(v_as_541_, v_lo_542_, v_mid_558_);
v___y_566_ = v___x_574_;
goto v___jp_565_;
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_array_fget_borrowed(v___y_560_, v_mid_558_);
v___x_562_ = lean_array_fget_borrowed(v___y_560_, v_hi_543_);
v___x_563_ = l_Lean_Name_quickLt(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v_mid_558_);
v___y_545_ = v___y_560_;
goto v___jp_544_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_fswap(v___y_560_, v_mid_558_, v_hi_543_);
lean_dec(v_mid_558_);
v___y_545_ = v___x_564_;
goto v___jp_544_;
}
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_array_fget_borrowed(v___y_566_, v_hi_543_);
v___x_568_ = lean_array_fget_borrowed(v___y_566_, v_lo_542_);
v___x_569_ = l_Lean_Name_quickLt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
v___y_560_ = v___y_566_;
goto v___jp_559_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_array_fswap(v___y_566_, v_lo_542_, v_hi_543_);
v___y_560_ = v___x_570_;
goto v___jp_559_;
}
}
}
v___jp_544_:
{
lean_object* v_pivot_546_; lean_object* v___x_547_; lean_object* v_fst_548_; lean_object* v_snd_549_; uint8_t v___x_550_; 
v_pivot_546_ = lean_array_fget(v___y_545_, v_hi_543_);
lean_inc_n(v_lo_542_, 2);
v___x_547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_543_, v_pivot_546_, v___y_545_, v_lo_542_, v_lo_542_);
lean_dec(v_pivot_546_);
v_fst_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_fst_548_);
v_snd_549_ = lean_ctor_get(v___x_547_, 1);
lean_inc(v_snd_549_);
lean_dec_ref(v___x_547_);
v___x_550_ = lean_nat_dec_le(v_hi_543_, v_fst_548_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_540_, v_snd_549_, v_lo_542_, v_fst_548_);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_add(v_fst_548_, v___x_552_);
lean_dec(v_fst_548_);
v_as_541_ = v___x_551_;
v_lo_542_ = v___x_553_;
goto _start;
}
else
{
lean_dec(v_fst_548_);
lean_dec(v_lo_542_);
return v_snd_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_n_575_, lean_object* v_as_576_, lean_object* v_lo_577_, lean_object* v_hi_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_575_, v_as_576_, v_lo_577_, v_hi_578_);
lean_dec(v_hi_578_);
lean_dec(v_n_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_581_ = lean_array_mk(v_es_580_);
v___x_582_ = lean_array_get_size(v___x_581_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_nat_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___y_588_; uint8_t v___x_592_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_sub(v___x_582_, v___x_585_);
v___x_592_ = lean_nat_dec_le(v___x_583_, v___x_586_);
if (v___x_592_ == 0)
{
lean_inc(v___x_586_);
v___y_588_ = v___x_586_;
goto v___jp_587_;
}
else
{
v___y_588_ = v___x_583_;
goto v___jp_587_;
}
v___jp_587_:
{
uint8_t v___x_589_; 
v___x_589_ = lean_nat_dec_le(v___y_588_, v___x_586_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v___x_586_);
lean_inc(v___y_588_);
v___x_590_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_582_, v___x_581_, v___y_588_, v___y_588_);
lean_dec(v___y_588_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_582_, v___x_581_, v___y_588_, v___x_586_);
lean_dec(v___x_586_);
return v___x_591_;
}
}
}
else
{
return v___x_581_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_593_, lean_object* v_x2_594_){
_start:
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_NameSet_contains(v_x1_593_, v_x2_594_);
v___x_596_ = lean_bool_not(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_597_, lean_object* v_x2_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_597_, v_x2_598_);
lean_dec(v_x2_598_);
lean_dec(v_x1_597_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_610_, lean_object* v_asyncMode_611_){
_start:
{
lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___f_613_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_614_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_615_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_616_ = lean_box(0);
v___x_617_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_618_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_618_, 0, v_name_610_);
lean_ctor_set(v___x_618_, 1, v___f_613_);
lean_ctor_set(v___x_618_, 2, v___f_614_);
lean_ctor_set(v___x_618_, 3, v___f_615_);
lean_ctor_set(v___x_618_, 4, v___x_616_);
lean_ctor_set(v___x_618_, 5, v_asyncMode_611_);
lean_ctor_set(v___x_618_, 6, v___x_617_);
v___x_619_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_620_, lean_object* v_asyncMode_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_mkTagDeclarationExtension(v_name_620_, v_asyncMode_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_624_, lean_object* v_as_625_, lean_object* v_lo_626_, lean_object* v_hi_627_, lean_object* v_w_628_, lean_object* v_hlo_629_, lean_object* v_hhi_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_624_, v_as_625_, v_lo_626_, v_hi_627_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_632_, lean_object* v_as_633_, lean_object* v_lo_634_, lean_object* v_hi_635_, lean_object* v_w_636_, lean_object* v_hlo_637_, lean_object* v_hhi_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_632_, v_as_633_, v_lo_634_, v_hi_635_, v_w_636_, v_hlo_637_, v_hhi_638_);
lean_dec(v_hi_635_);
lean_dec(v_n_632_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object* v_n_640_, lean_object* v_lo_641_, lean_object* v_hi_642_, lean_object* v_hhi_643_, lean_object* v_pivot_644_, lean_object* v_as_645_, lean_object* v_i_646_, lean_object* v_k_647_, lean_object* v_ilo_648_, lean_object* v_ik_649_, lean_object* v_w_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_642_, v_pivot_644_, v_as_645_, v_i_646_, v_k_647_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object* v_n_652_, lean_object* v_lo_653_, lean_object* v_hi_654_, lean_object* v_hhi_655_, lean_object* v_pivot_656_, lean_object* v_as_657_, lean_object* v_i_658_, lean_object* v_k_659_, lean_object* v_ilo_660_, lean_object* v_ik_661_, lean_object* v_w_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_652_, v_lo_653_, v_hi_654_, v_hhi_655_, v_pivot_656_, v_as_657_, v_i_658_, v_k_659_, v_ilo_660_, v_ik_661_, v_w_662_);
lean_dec(v_pivot_656_);
lean_dec(v_hi_654_);
lean_dec(v_lo_653_);
lean_dec(v_n_652_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_669_, v___y_670_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v_x_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_673_, lean_object* v_x_674_){
_start:
{
lean_inc_ref(v_s_673_);
return v_s_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_675_, v_x_676_);
lean_dec(v_x_676_);
lean_dec_ref(v_s_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1));
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_685_, v_x_686_);
lean_dec_ref(v_x_686_);
lean_dec_ref(v_x_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_690_);
lean_dec_ref(v_x_690_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_696_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5(void){
_start:
{
lean_object* v___f_697_; lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___f_697_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_698_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_699_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_700_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_701_ = lean_box(0);
v___x_702_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
v___x_703_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
lean_ctor_set(v___x_703_, 2, v___f_700_);
lean_ctor_set(v___x_703_, 3, v___f_699_);
lean_ctor_set(v___x_703_, 4, v___f_698_);
lean_ctor_set(v___x_703_, 5, v___f_697_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__5);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_706_, lean_object* v_msg_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_panic_fn_borrowed(v_env_706_, v_msg_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object* v_env_709_, lean_object* v_msg_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_709_, v_msg_710_);
lean_dec_ref(v_env_709_);
return v_res_711_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_715_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = lean_unsigned_to_nat(115u);
v___x_718_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_719_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_720_ = l_mkPanicMessageWithDecl(v___x_719_, v___x_718_, v___x_717_, v___x_716_, v___x_715_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_721_, lean_object* v_env_722_, lean_object* v_declName_723_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_Name_isAnonymous(v_declName_723_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_722_, v_declName_723_);
if (lean_obj_tag(v___x_729_) == 0)
{
goto v___jp_724_;
}
else
{
lean_dec_ref_known(v___x_729_, 1);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v_declName_723_);
lean_dec_ref(v_ext_721_);
v___x_730_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_731_ = lean_panic_fn_borrowed(v_env_722_, v___x_730_);
lean_dec_ref(v_env_722_);
return v___x_731_;
}
else
{
goto v___jp_724_;
}
}
}
else
{
lean_dec(v_declName_723_);
lean_dec_ref(v_ext_721_);
return v_env_722_;
}
v___jp_724_:
{
lean_object* v_toEnvExtension_725_; lean_object* v_asyncMode_726_; lean_object* v___x_727_; 
v_toEnvExtension_725_ = lean_ctor_get(v_ext_721_, 0);
v_asyncMode_726_ = lean_ctor_get(v_toEnvExtension_725_, 2);
lean_inc(v_asyncMode_726_);
lean_inc(v_declName_723_);
v___x_727_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_721_, v_env_722_, v_declName_723_, v_asyncMode_726_, v_declName_723_);
lean_dec(v_asyncMode_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object* v_as_732_, lean_object* v_k_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_m_738_; lean_object* v_a_739_; uint8_t v___x_740_; 
v___x_736_ = lean_nat_add(v_x_734_, v_x_735_);
v___x_737_ = lean_unsigned_to_nat(1u);
v_m_738_ = lean_nat_shiftr(v___x_736_, v___x_737_);
lean_dec(v___x_736_);
v_a_739_ = lean_array_fget_borrowed(v_as_732_, v_m_738_);
v___x_740_ = l_Lean_Name_quickLt(v_a_739_, v_k_733_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; 
lean_dec(v_x_735_);
v___x_741_ = l_Lean_Name_quickLt(v_k_733_, v_a_739_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; 
lean_dec(v_m_738_);
lean_dec(v_x_734_);
v___x_742_ = 1;
return v___x_742_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_nat_dec_eq(v_m_738_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_nat_sub(v_m_738_, v___x_737_);
lean_dec(v_m_738_);
v___x_746_ = lean_nat_dec_lt(v___x_745_, v_x_734_);
if (v___x_746_ == 0)
{
v_x_735_ = v___x_745_;
goto _start;
}
else
{
lean_dec(v___x_745_);
lean_dec(v_x_734_);
return v___x_740_;
}
}
else
{
lean_dec(v_m_738_);
lean_dec(v_x_734_);
return v___x_740_;
}
}
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
lean_dec(v_x_734_);
v___x_748_ = lean_nat_add(v_m_738_, v___x_737_);
lean_dec(v_m_738_);
v___x_749_ = lean_nat_dec_le(v___x_748_, v_x_735_);
if (v___x_749_ == 0)
{
lean_dec(v___x_748_);
lean_dec(v_x_735_);
return v___x_749_;
}
else
{
v_x_734_ = v___x_748_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object* v_as_751_, lean_object* v_k_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v_as_751_, v_k_752_, v_x_753_, v_x_754_);
lean_dec(v_k_752_);
lean_dec_ref(v_as_751_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_760_, lean_object* v_env_761_, lean_object* v_declName_762_, lean_object* v_asyncMode_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(1);
v___x_765_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_761_, v_declName_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
lean_inc(v_declName_762_);
v___x_766_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_764_, v_ext_760_, v_env_761_, v_asyncMode_763_, v_declName_762_);
v___x_767_ = l_Lean_NameSet_contains(v___x_766_, v_declName_762_);
lean_dec(v_declName_762_);
lean_dec(v___x_766_);
return v___x_767_;
}
else
{
lean_object* v_val_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_val_768_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_768_);
lean_dec_ref_known(v___x_765_, 1);
v___x_769_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_770_ = 0;
v___x_771_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_769_, v_ext_760_, v_env_761_, v_val_768_, v___x_770_);
lean_dec(v_val_768_);
lean_dec_ref(v_env_761_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_array_get_size(v___x_771_);
v___x_774_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec_ref(v___x_771_);
lean_dec(v_declName_762_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_sub(v___x_773_, v___x_775_);
v___x_777_ = lean_nat_dec_le(v___x_772_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v___x_776_);
lean_dec_ref(v___x_771_);
lean_dec(v_declName_762_);
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_771_, v_declName_762_, v___x_772_, v___x_776_);
lean_dec(v_declName_762_);
lean_dec_ref(v___x_771_);
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_779_, lean_object* v_env_780_, lean_object* v_declName_781_, lean_object* v_asyncMode_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_779_, v_env_780_, v_declName_781_, v_asyncMode_782_);
lean_dec(v_asyncMode_782_);
lean_dec_ref(v_ext_779_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object* v_as_785_, lean_object* v_k_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v_as_785_, v_k_786_, v_x_787_, v_x_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object* v_as_791_, lean_object* v_k_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v_as_791_, v_k_792_, v_x_793_, v_x_794_, v_x_795_);
lean_dec(v_k_792_);
lean_dec_ref(v_as_791_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(lean_object* v_x_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__0___boxed(lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__0(v_x_803_, v___y_804_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_x_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(lean_object* v_s_807_, lean_object* v_x_808_){
_start:
{
lean_inc(v_s_807_);
return v_s_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__1___boxed(lean_object* v_s_809_, lean_object* v_x_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__1(v_s_809_, v_x_810_);
lean_dec_ref(v_x_810_);
lean_dec(v_s_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__1));
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___boxed(lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__2(v_x_819_, v_x_820_);
lean_dec(v_x_820_);
lean_dec_ref(v_x_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_box(0);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___lam__3___boxed(lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_instInhabitedMapDeclarationExtension_default___lam__3(v_x_824_);
lean_dec(v_x_824_);
return v_res_825_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__4(void){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_830_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__5(void){
_start:
{
lean_object* v___f_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___f_831_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__3));
v___f_832_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__2));
v___f_833_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__1));
v___f_834_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__0));
v___x_835_ = lean_box(0);
v___x_836_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__4);
v___x_837_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
lean_ctor_set(v___x_837_, 2, v___f_834_);
lean_ctor_set(v___x_837_, 3, v___f_833_);
lean_ctor_set(v___x_837_, 4, v___f_832_);
lean_ctor_set(v___x_837_, 5, v___f_831_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_00_u03b1_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__5, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__5_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__5);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension___closed__0(void){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_instInhabitedMapDeclarationExtension_default(lean_box(0));
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension___closed__0, &l_Lean_instInhabitedMapDeclarationExtension___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension___closed__0);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_848_; 
v_fst_846_ = lean_ctor_get(v_x_845_, 0);
lean_inc(v_fst_846_);
v_snd_847_ = lean_ctor_get(v_x_845_, 1);
lean_inc(v_snd_847_);
lean_dec_ref(v_x_845_);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_846_, v_snd_847_, v_s_844_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_849_, lean_object* v_env_850_, lean_object* v_s_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_apply_2(v_exportEntriesFn_849_, v_env_850_, v_s_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
return v_x_854_;
}
else
{
lean_object* v_head_856_; lean_object* v_tail_857_; lean_object* v___x_858_; 
v_head_856_ = lean_ctor_get(v_x_855_, 0);
lean_inc(v_head_856_);
v_tail_857_ = lean_ctor_get(v_x_855_, 1);
lean_inc(v_tail_857_);
lean_dec_ref_known(v_x_855_, 2);
v___x_858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_853_, v_head_856_);
if (lean_obj_tag(v___x_858_) == 1)
{
lean_object* v_val_859_; lean_object* v___x_860_; 
v_val_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_856_, v_val_859_, v_x_854_);
v_x_854_ = v___x_860_;
v_x_855_ = v_tail_857_;
goto _start;
}
else
{
lean_dec(v___x_858_);
lean_dec(v_head_856_);
v_x_855_ = v_tail_857_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_863_, v_x_864_, v_x_865_);
lean_dec(v_newState_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_867_, lean_object* v_newState_868_, lean_object* v_newConsts_869_, lean_object* v_s_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_868_, v_s_870_, v_newConsts_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_872_, lean_object* v_newState_873_, lean_object* v_newConsts_874_, lean_object* v_s_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_872_, v_newState_873_, v_newConsts_874_, v_s_875_);
lean_dec(v_newState_873_);
lean_dec(v_x_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___lam__2___closed__0));
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_879_);
lean_dec(v_x_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_887_, lean_object* v_x_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_892_, lean_object* v_x_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_892_, v_x_893_, v___y_894_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_x_893_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_906_, lean_object* v_asyncMode_907_, lean_object* v_exportEntriesFn_908_){
_start:
{
lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___f_910_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_911_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1), 3, 1);
lean_closure_set(v___f_911_, 0, v_exportEntriesFn_908_);
v___f_912_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___closed__3));
v___f_913_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_914_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_915_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_916_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_917_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_917_, 0, v_name_906_);
lean_ctor_set(v___x_917_, 1, v___f_914_);
lean_ctor_set(v___x_917_, 2, v___f_915_);
lean_ctor_set(v___x_917_, 3, v___f_910_);
lean_ctor_set(v___x_917_, 4, v___f_911_);
lean_ctor_set(v___x_917_, 5, v___f_912_);
lean_ctor_set(v___x_917_, 6, v_asyncMode_907_);
lean_ctor_set(v___x_917_, 7, v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___f_913_);
v___x_919_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_919_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_919_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_936_, lean_object* v_asyncMode_937_, lean_object* v_exportEntriesFn_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_936_, v_asyncMode_937_, v_exportEntriesFn_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_941_, lean_object* v_name_942_, lean_object* v_asyncMode_943_, lean_object* v_exportEntriesFn_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_942_, v_asyncMode_943_, v_exportEntriesFn_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_947_, lean_object* v_name_948_, lean_object* v_asyncMode_949_, lean_object* v_exportEntriesFn_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_947_, v_name_948_, v_asyncMode_949_, v_exportEntriesFn_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_953_, lean_object* v_newState_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_954_, v_x_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_958_, lean_object* v_newState_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_958_, v_newState_959_, v_x_960_, v_x_961_);
lean_dec(v_newState_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_968_, lean_object* v_env_969_, lean_object* v_declName_970_, lean_object* v_val_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_969_, v_declName_970_);
if (lean_obj_tag(v___x_972_) == 1)
{
lean_object* v_val_973_; lean_object* v_name_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_val_971_);
v_val_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_val_973_);
lean_dec_ref_known(v___x_972_, 1);
v_name_974_ = lean_ctor_get(v_ext_968_, 1);
lean_inc(v_name_974_);
lean_dec_ref(v_ext_968_);
v___x_975_ = lean_box(0);
v___x_976_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_977_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_978_ = lean_unsigned_to_nat(159u);
v___x_979_ = lean_unsigned_to_nat(4u);
v___x_980_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_981_ = 1;
v___x_982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_970_, v___x_981_);
v___x_983_ = lean_string_append(v___x_980_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___x_986_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_974_, v___x_981_);
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
v___x_990_ = l_Lean_Environment_allImportedModuleNames(v_env_969_);
v___x_991_ = lean_array_get(v___x_975_, v___x_990_, v_val_973_);
lean_dec(v_val_973_);
lean_dec_ref(v___x_990_);
v___x_992_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_991_, v___x_981_);
v___x_993_ = lean_string_append(v___x_989_, v___x_992_);
lean_dec_ref(v___x_992_);
v___x_994_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
v___x_996_ = l_mkPanicMessageWithDecl(v___x_976_, v___x_977_, v___x_978_, v___x_979_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = lean_panic_fn_borrowed(v_env_969_, v___x_996_);
lean_dec_ref(v_env_969_);
return v___x_997_;
}
else
{
lean_object* v_toEnvExtension_998_; lean_object* v_asyncMode_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v___x_972_);
v_toEnvExtension_998_ = lean_ctor_get(v_ext_968_, 0);
v_asyncMode_999_ = lean_ctor_get(v_toEnvExtension_998_, 2);
lean_inc(v_asyncMode_999_);
lean_inc(v_declName_970_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_declName_970_);
lean_ctor_set(v___x_1000_, 1, v_val_971_);
v___x_1001_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_968_, v_env_969_, v___x_1000_, v_asyncMode_999_, v_declName_970_);
lean_dec(v_asyncMode_999_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_1002_, lean_object* v_ext_1003_, lean_object* v_env_1004_, lean_object* v_declName_1005_, lean_object* v_val_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1003_, v_env_1004_, v_declName_1005_, v_val_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object* v_a_1008_, lean_object* v_b_1009_){
_start:
{
lean_object* v_fst_1010_; lean_object* v_fst_1011_; uint8_t v___x_1012_; 
v_fst_1010_ = lean_ctor_get(v_a_1008_, 0);
v_fst_1011_ = lean_ctor_get(v_b_1009_, 0);
v___x_1012_ = l_Lean_Name_quickLt(v_fst_1010_, v_fst_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object* v_a_1013_, lean_object* v_b_1014_){
_start:
{
uint8_t v_res_1015_; lean_object* v_r_1016_; 
v_res_1015_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_1013_, v_b_1014_);
lean_dec_ref(v_b_1014_);
lean_dec_ref(v_a_1013_);
v_r_1016_ = lean_box(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_inst_1019_, lean_object* v_ext_1020_, lean_object* v_env_1021_, lean_object* v_declName_1022_, lean_object* v_asyncMode_1023_, uint8_t v_level_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_box(1);
v___x_1026_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1021_, v_declName_1022_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_inst_1019_);
lean_inc(v_declName_1022_);
v___x_1027_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1025_, v_ext_1020_, v_env_1021_, v_asyncMode_1023_, v_declName_1022_);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1027_, v_declName_1022_);
lean_dec(v_declName_1022_);
lean_dec(v___x_1027_);
return v___x_1028_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_val_1029_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1030_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1025_, v_ext_1020_, v_env_1021_, v_val_1029_, v_level_1024_);
lean_dec(v_val_1029_);
lean_dec_ref(v_env_1021_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v___x_1030_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v___x_1030_);
lean_dec(v_declName_1022_);
lean_dec(v_inst_1019_);
v___x_1034_ = lean_box(0);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_sub(v___x_1032_, v___x_1035_);
v___x_1037_ = lean_nat_dec_le(v___x_1031_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec(v___x_1036_);
lean_dec_ref(v___x_1030_);
lean_dec(v_declName_1022_);
lean_dec(v_inst_1019_);
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
else
{
lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___f_1039_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_declName_1022_);
lean_ctor_set(v___x_1040_, 1, v_inst_1019_);
v___x_1041_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1));
v___x_1042_ = l_Array_binSearchAux___redArg(v___f_1039_, v___x_1041_, v___x_1030_, v___x_1040_, v___x_1031_, v___x_1036_);
lean_dec_ref(v___x_1030_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_box(0);
return v___x_1043_;
}
else
{
lean_object* v_val_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_val_1044_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v___x_1042_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_val_1044_);
lean_dec(v___x_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_snd_1048_; lean_object* v___x_1050_; 
v_snd_1048_ = lean_ctor_get(v_val_1044_, 1);
lean_inc(v_snd_1048_);
lean_dec(v_val_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_snd_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_snd_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_inst_1053_, lean_object* v_ext_1054_, lean_object* v_env_1055_, lean_object* v_declName_1056_, lean_object* v_asyncMode_1057_, lean_object* v_level_1058_){
_start:
{
uint8_t v_level_boxed_1059_; lean_object* v_res_1060_; 
v_level_boxed_1059_ = lean_unbox(v_level_1058_);
v_res_1060_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1053_, v_ext_1054_, v_env_1055_, v_declName_1056_, v_asyncMode_1057_, v_level_boxed_1059_);
lean_dec(v_asyncMode_1057_);
lean_dec_ref(v_ext_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1061_, lean_object* v_inst_1062_, lean_object* v_ext_1063_, lean_object* v_env_1064_, lean_object* v_declName_1065_, lean_object* v_asyncMode_1066_, uint8_t v_level_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1062_, v_ext_1063_, v_env_1064_, v_declName_1065_, v_asyncMode_1066_, v_level_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1069_, lean_object* v_inst_1070_, lean_object* v_ext_1071_, lean_object* v_env_1072_, lean_object* v_declName_1073_, lean_object* v_asyncMode_1074_, lean_object* v_level_1075_){
_start:
{
uint8_t v_level_boxed_1076_; lean_object* v_res_1077_; 
v_level_boxed_1076_ = lean_unbox(v_level_1075_);
v_res_1077_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1069_, v_inst_1070_, v_ext_1071_, v_env_1072_, v_declName_1073_, v_asyncMode_1074_, v_level_boxed_1076_);
lean_dec(v_asyncMode_1074_);
lean_dec_ref(v_ext_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_inst_1079_, lean_object* v_ext_1080_, lean_object* v_env_1081_, lean_object* v_declName_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(1);
v___x_1084_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1081_, v_declName_1082_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_toEnvExtension_1085_; lean_object* v_asyncMode_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
lean_dec(v_inst_1079_);
v_toEnvExtension_1085_ = lean_ctor_get(v_ext_1080_, 0);
v_asyncMode_1086_ = lean_ctor_get(v_toEnvExtension_1085_, 2);
lean_inc(v_declName_1082_);
v___x_1087_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1083_, v_ext_1080_, v_env_1081_, v_asyncMode_1086_, v_declName_1082_);
v___x_1088_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1082_, v___x_1087_);
lean_dec(v___x_1087_);
lean_dec(v_declName_1082_);
return v___x_1088_;
}
else
{
lean_object* v_val_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_val_1089_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1090_ = 0;
v___x_1091_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1083_, v_ext_1080_, v_env_1081_, v_val_1089_, v___x_1090_);
lean_dec(v_val_1089_);
lean_dec_ref(v_env_1081_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_array_get_size(v___x_1091_);
v___x_1094_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_dec_ref(v___x_1091_);
lean_dec(v_declName_1082_);
lean_dec(v_inst_1079_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_nat_sub(v___x_1093_, v___x_1095_);
v___x_1097_ = lean_nat_dec_le(v___x_1092_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec(v___x_1096_);
lean_dec_ref(v___x_1091_);
lean_dec(v_declName_1082_);
lean_dec(v_inst_1079_);
return v___x_1097_;
}
else
{
lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___f_1098_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_declName_1082_);
lean_ctor_set(v___x_1099_, 1, v_inst_1079_);
v___x_1100_ = ((lean_object*)(l_Lean_MapDeclarationExtension_contains___redArg___closed__0));
v___x_1101_ = l_Array_binSearchAux___redArg(v___f_1098_, v___x_1100_, v___x_1091_, v___x_1099_, v___x_1092_, v___x_1096_);
lean_dec_ref(v___x_1091_);
v___x_1102_ = lean_unbox(v___x_1101_);
lean_dec(v___x_1101_);
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_inst_1103_, lean_object* v_ext_1104_, lean_object* v_env_1105_, lean_object* v_declName_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1103_, v_ext_1104_, v_env_1105_, v_declName_1106_);
lean_dec_ref(v_ext_1104_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1109_, lean_object* v_inst_1110_, lean_object* v_ext_1111_, lean_object* v_env_1112_, lean_object* v_declName_1113_){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1110_, v_ext_1111_, v_env_1112_, v_declName_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1115_, lean_object* v_inst_1116_, lean_object* v_ext_1117_, lean_object* v_env_1118_, lean_object* v_declName_1119_){
_start:
{
uint8_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1115_, v_inst_1116_, v_ext_1117_, v_env_1118_, v_declName_1119_);
lean_dec_ref(v_ext_1117_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
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
