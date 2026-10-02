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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_takeNewEntries___redArg(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value),((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value),((lean_object*)&l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0_value)}};
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2_value;
static const lean_closure_object l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3 = (const lean_object*)&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3_value;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4;
static lean_once_cell_t l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0;
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_TagDeclarationExtension_isTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_TagDeclarationExtension_isTagged___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_isTagged___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3 = (const lean_object*)&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object* v_val_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v_fst_270_; lean_object* v_newEntries_271_; lean_object* v___x_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_fst_266_ = lean_ctor_get(v___y_265_, 0);
lean_inc(v_fst_266_);
v_snd_267_ = lean_ctor_get(v___y_265_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v___y_265_);
v_fst_268_ = lean_ctor_get(v___y_263_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v___y_263_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v___y_263_);
v_fst_270_ = lean_ctor_get(v___y_262_, 0);
v_newEntries_271_ = l_Lean_takeNewEntries___redArg(v_fst_268_, v_fst_270_);
v___x_272_ = lean_apply_3(v_val_261_, v_newEntries_271_, v_snd_269_, v_snd_267_);
v_fst_273_ = lean_ctor_get(v___x_272_, 0);
v_snd_274_ = lean_ctor_get(v___x_272_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v___x_272_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snd_274_);
lean_inc(v_fst_273_);
lean_dec(v___x_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = l_List_appendTR___redArg(v_fst_273_, v_fst_266_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_snd_274_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object* v_val_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(v_val_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object* v_descr_293_){
_start:
{
lean_object* v_name_295_; lean_object* v_addEntryFn_296_; lean_object* v_addImportedFn_297_; lean_object* v_toArrayFn_298_; lean_object* v_exportEntriesFnEx_x3f_299_; lean_object* v_asyncMode_300_; lean_object* v_replay_x3f_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___y_313_; 
v_name_295_ = lean_ctor_get(v_descr_293_, 0);
lean_inc(v_name_295_);
v_addEntryFn_296_ = lean_ctor_get(v_descr_293_, 1);
lean_inc(v_addEntryFn_296_);
v_addImportedFn_297_ = lean_ctor_get(v_descr_293_, 2);
lean_inc_n(v_addImportedFn_297_, 2);
v_toArrayFn_298_ = lean_ctor_get(v_descr_293_, 3);
lean_inc_ref(v_toArrayFn_298_);
v_exportEntriesFnEx_x3f_299_ = lean_ctor_get(v_descr_293_, 4);
lean_inc(v_exportEntriesFnEx_x3f_299_);
v_asyncMode_300_ = lean_ctor_get(v_descr_293_, 5);
lean_inc(v_asyncMode_300_);
v_replay_x3f_301_ = lean_ctor_get(v_descr_293_, 6);
lean_inc(v_replay_x3f_301_);
lean_dec_ref(v_descr_293_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0), 3, 1);
lean_closure_set(v___f_302_, 0, v_addEntryFn_296_);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1), 4, 2);
lean_closure_set(v___f_303_, 0, v_exportEntriesFnEx_x3f_299_);
lean_closure_set(v___f_303_, 1, v_toArrayFn_298_);
v___f_304_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0));
v___f_305_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1));
v___x_306_ = lean_box(0);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_307_, 0, v_addImportedFn_297_);
lean_closure_set(v___f_307_, 1, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2));
v___x_309_ = lean_apply_1(v_addImportedFn_297_, v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_306_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_311_, 0, lean_box(0));
lean_closure_set(v___x_311_, 1, lean_box(0));
lean_closure_set(v___x_311_, 2, v___x_310_);
if (lean_obj_tag(v_replay_x3f_301_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
v___y_313_ = v___x_318_;
goto v___jp_312_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_val_319_ = lean_ctor_get(v_replay_x3f_301_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_replay_x3f_301_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v_replay_x3f_301_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v_replay_x3f_301_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___f_323_; lean_object* v___x_325_; 
v___f_323_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed), 5, 1);
lean_closure_set(v___f_323_, 0, v_val_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___f_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___f_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v___y_313_ = v___x_325_;
goto v___jp_312_;
}
}
}
v___jp_312_:
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = 0;
v___x_315_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_315_, 0, v_name_295_);
lean_ctor_set(v___x_315_, 1, v___x_311_);
lean_ctor_set(v___x_315_, 2, v___f_307_);
lean_ctor_set(v___x_315_, 3, v___f_302_);
lean_ctor_set(v___x_315_, 4, v___f_303_);
lean_ctor_set(v___x_315_, 5, v___f_304_);
lean_ctor_set(v___x_315_, 6, v_asyncMode_300_);
lean_ctor_set(v___x_315_, 7, v___y_313_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*8, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___f_305_);
v___x_317_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object* v_descr_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* v_00_u03b1_331_, lean_object* v_00_u03c3_332_, lean_object* v_inst_333_, lean_object* v_descr_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* v_00_u03b1_337_, lean_object* v_00_u03c3_338_, lean_object* v_inst_339_, lean_object* v_descr_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_registerSimplePersistentEnvExtension(v_00_u03b1_337_, v_00_u03c3_338_, v_inst_339_, v_descr_340_);
lean_dec(v_inst_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object* v_x_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object* v_x_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_351_, v___y_352_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_x_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(lean_object* v_s_355_, lean_object* v_x_356_){
_start:
{
lean_inc_ref(v_s_355_);
return v_s_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1___boxed(lean_object* v_s_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(v_s_357_, v_x_358_);
lean_dec(v_x_358_);
lean_dec_ref(v_s_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0));
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(v_x_365_, v_x_366_);
lean_dec_ref(v_x_366_);
lean_dec_ref(v_x_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3___boxed(lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(v_x_370_);
lean_dec_ref(v_x_370_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_376_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5(void){
_start:
{
lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___f_377_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3));
v___f_378_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2));
v___f_379_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1));
v___f_380_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0));
v___x_381_ = lean_box(0);
v___x_382_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_383_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___f_380_);
lean_ctor_set(v___x_383_, 3, v___f_379_);
lean_ctor_set(v___x_383_, 4, v___f_378_);
lean_ctor_set(v___x_383_, 5, v___f_377_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg();
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object* v_00_u03b1_388_, lean_object* v_00_u03c3_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg(){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg___boxed(lean_object* v___dummy_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v_res_394_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object* v_00_u03b1_396_, lean_object* v_00_u03c3_397_, lean_object* v_inst_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0, &l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object* v_00_u03b1_400_, lean_object* v_00_u03c3_401_, lean_object* v_inst_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_SimplePersistentEnvExtension_instInhabited(v_00_u03b1_400_, v_00_u03c3_401_, v_inst_402_);
lean_dec(v_inst_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object* v_inst_404_, lean_object* v_ext_405_, lean_object* v_env_406_, lean_object* v_asyncMode_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_fst_412_; 
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_inst_404_);
v___x_410_ = lean_box(0);
v___x_411_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_409_, v_ext_405_, v_env_406_, v_asyncMode_407_, v___x_410_);
v_fst_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_fst_412_);
lean_dec(v___x_411_);
return v_fst_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object* v_inst_413_, lean_object* v_ext_414_, lean_object* v_env_415_, lean_object* v_asyncMode_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_413_, v_ext_414_, v_env_415_, v_asyncMode_416_);
lean_dec(v_asyncMode_416_);
lean_dec_ref(v_ext_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* v_00_u03b1_418_, lean_object* v_00_u03c3_419_, lean_object* v_inst_420_, lean_object* v_ext_421_, lean_object* v_env_422_, lean_object* v_asyncMode_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_420_, v_ext_421_, v_env_422_, v_asyncMode_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object* v_00_u03b1_425_, lean_object* v_00_u03c3_426_, lean_object* v_inst_427_, lean_object* v_ext_428_, lean_object* v_env_429_, lean_object* v_asyncMode_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_SimplePersistentEnvExtension_getEntries(v_00_u03b1_425_, v_00_u03c3_426_, v_inst_427_, v_ext_428_, v_env_429_, v_asyncMode_430_);
lean_dec(v_asyncMode_430_);
lean_dec_ref(v_ext_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object* v_inst_432_, lean_object* v_ext_433_, lean_object* v_env_434_, lean_object* v_asyncMode_435_, lean_object* v_asyncDecl_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_snd_440_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_inst_432_);
v___x_439_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_438_, v_ext_433_, v_env_434_, v_asyncMode_435_, v_asyncDecl_436_);
v_snd_440_ = lean_ctor_get(v___x_439_, 1);
lean_inc(v_snd_440_);
lean_dec(v___x_439_);
return v_snd_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object* v_inst_441_, lean_object* v_ext_442_, lean_object* v_env_443_, lean_object* v_asyncMode_444_, lean_object* v_asyncDecl_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_441_, v_ext_442_, v_env_443_, v_asyncMode_444_, v_asyncDecl_445_);
lean_dec(v_asyncMode_444_);
lean_dec_ref(v_ext_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* v_00_u03b1_447_, lean_object* v_00_u03c3_448_, lean_object* v_inst_449_, lean_object* v_ext_450_, lean_object* v_env_451_, lean_object* v_asyncMode_452_, lean_object* v_asyncDecl_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_449_, v_ext_450_, v_env_451_, v_asyncMode_452_, v_asyncDecl_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object* v_00_u03b1_455_, lean_object* v_00_u03c3_456_, lean_object* v_inst_457_, lean_object* v_ext_458_, lean_object* v_env_459_, lean_object* v_asyncMode_460_, lean_object* v_asyncDecl_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_SimplePersistentEnvExtension_getState(v_00_u03b1_455_, v_00_u03c3_456_, v_inst_457_, v_ext_458_, v_env_459_, v_asyncMode_460_, v_asyncDecl_461_);
lean_dec(v_asyncMode_460_);
lean_dec_ref(v_ext_458_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object* v_s_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_fst_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_fst_465_ = lean_ctor_get(v_x_464_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_x_464_, 1);
lean_dec(v_unused_473_);
v___x_467_ = v_x_464_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_fst_465_);
lean_dec(v_x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v_s_463_);
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_s_463_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object* v_ext_474_, lean_object* v_env_475_, lean_object* v_s_476_){
_start:
{
lean_object* v_toEnvExtension_477_; lean_object* v_asyncMode_478_; lean_object* v___f_479_; lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; 
v_toEnvExtension_477_ = lean_ctor_get(v_ext_474_, 0);
v_asyncMode_478_ = lean_ctor_get(v_toEnvExtension_477_, 2);
lean_inc(v_asyncMode_478_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_479_, 0, v_s_476_);
v___x_480_ = lean_box(0);
v___x_481_ = 1;
v___x_482_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_474_, v_env_475_, v___f_479_, v_asyncMode_478_, v___x_480_, v___x_481_);
lean_dec(v_asyncMode_478_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* v_00_u03b1_483_, lean_object* v_00_u03c3_484_, lean_object* v_ext_485_, lean_object* v_env_486_, lean_object* v_s_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_485_, v_env_486_, v_s_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_489_, lean_object* v_x_490_){
_start:
{
lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_500_; 
v_fst_491_ = lean_ctor_get(v_x_490_, 0);
v_snd_492_ = lean_ctor_get(v_x_490_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_x_490_);
if (v_isSharedCheck_500_ == 0)
{
v___x_494_ = v_x_490_;
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snd_492_);
lean_inc(v_fst_491_);
lean_dec(v_x_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_apply_1(v_f_489_, v_snd_492_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object* v_ext_501_, lean_object* v_env_502_, lean_object* v_f_503_){
_start:
{
lean_object* v_toEnvExtension_504_; lean_object* v_asyncMode_505_; lean_object* v___f_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; 
v_toEnvExtension_504_ = lean_ctor_get(v_ext_501_, 0);
v_asyncMode_505_ = lean_ctor_get(v_toEnvExtension_504_, 2);
lean_inc(v_asyncMode_505_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_506_, 0, v_f_503_);
v___x_507_ = lean_box(0);
v___x_508_ = 1;
v___x_509_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_501_, v_env_502_, v___f_506_, v_asyncMode_505_, v___x_507_, v___x_508_);
lean_dec(v_asyncMode_505_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* v_00_u03b1_510_, lean_object* v_00_u03c3_511_, lean_object* v_ext_512_, lean_object* v_env_513_, lean_object* v_f_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(v_ext_512_, v_env_513_, v_f_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_NameSet_empty;
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_519_);
lean_dec_ref(v_x_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object* v_hi_521_, lean_object* v_pivot_522_, lean_object* v_as_523_, lean_object* v_i_524_, lean_object* v_k_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_lt(v_k_525_, v_hi_521_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_k_525_);
v___x_527_ = lean_array_fswap(v_as_523_, v_i_524_, v_hi_521_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_i_524_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_fget_borrowed(v_as_523_, v_k_525_);
v___x_530_ = l_Lean_Name_quickLt(v___x_529_, v_pivot_522_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_k_525_, v___x_531_);
lean_dec(v_k_525_);
v_k_525_ = v___x_532_;
goto _start;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_array_fswap(v_as_523_, v_i_524_, v_k_525_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_i_524_, v___x_535_);
lean_dec(v_i_524_);
v___x_537_ = lean_nat_add(v_k_525_, v___x_535_);
lean_dec(v_k_525_);
v_as_523_ = v___x_534_;
v_i_524_ = v___x_536_;
v_k_525_ = v___x_537_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object* v_hi_539_, lean_object* v_pivot_540_, lean_object* v_as_541_, lean_object* v_i_542_, lean_object* v_k_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_539_, v_pivot_540_, v_as_541_, v_i_542_, v_k_543_);
lean_dec(v_pivot_540_);
lean_dec(v_hi_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_n_545_, lean_object* v_as_546_, lean_object* v_lo_547_, lean_object* v_hi_548_){
_start:
{
lean_object* v___y_550_; uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_lt(v_lo_547_, v_hi_548_);
if (v___x_560_ == 0)
{
lean_dec(v_lo_547_);
return v_as_546_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_mid_563_; lean_object* v___y_565_; lean_object* v___y_571_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_561_ = lean_nat_add(v_lo_547_, v_hi_548_);
v___x_562_ = lean_unsigned_to_nat(1u);
v_mid_563_ = lean_nat_shiftr(v___x_561_, v___x_562_);
lean_dec(v___x_561_);
v___x_576_ = lean_array_fget_borrowed(v_as_546_, v_mid_563_);
v___x_577_ = lean_array_fget_borrowed(v_as_546_, v_lo_547_);
v___x_578_ = l_Lean_Name_quickLt(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
v___y_571_ = v_as_546_;
goto v___jp_570_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lean_array_fswap(v_as_546_, v_lo_547_, v_mid_563_);
v___y_571_ = v___x_579_;
goto v___jp_570_;
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_array_fget_borrowed(v___y_565_, v_mid_563_);
v___x_567_ = lean_array_fget_borrowed(v___y_565_, v_hi_548_);
v___x_568_ = l_Lean_Name_quickLt(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v_mid_563_);
v___y_550_ = v___y_565_;
goto v___jp_549_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_array_fswap(v___y_565_, v_mid_563_, v_hi_548_);
lean_dec(v_mid_563_);
v___y_550_ = v___x_569_;
goto v___jp_549_;
}
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_array_fget_borrowed(v___y_571_, v_hi_548_);
v___x_573_ = lean_array_fget_borrowed(v___y_571_, v_lo_547_);
v___x_574_ = l_Lean_Name_quickLt(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
v___y_565_ = v___y_571_;
goto v___jp_564_;
}
else
{
lean_object* v___x_575_; 
v___x_575_ = lean_array_fswap(v___y_571_, v_lo_547_, v_hi_548_);
v___y_565_ = v___x_575_;
goto v___jp_564_;
}
}
}
v___jp_549_:
{
lean_object* v_pivot_551_; lean_object* v___x_552_; lean_object* v_fst_553_; lean_object* v_snd_554_; uint8_t v___x_555_; 
v_pivot_551_ = lean_array_fget(v___y_550_, v_hi_548_);
lean_inc_n(v_lo_547_, 2);
v___x_552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_548_, v_pivot_551_, v___y_550_, v_lo_547_, v_lo_547_);
lean_dec(v_pivot_551_);
v_fst_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_fst_553_);
v_snd_554_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_snd_554_);
lean_dec_ref(v___x_552_);
v___x_555_ = lean_nat_dec_le(v_hi_548_, v_fst_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_545_, v_snd_554_, v_lo_547_, v_fst_553_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_fst_553_, v___x_557_);
lean_dec(v_fst_553_);
v_as_546_ = v___x_556_;
v_lo_547_ = v___x_558_;
goto _start;
}
else
{
lean_dec(v_fst_553_);
lean_dec(v_lo_547_);
return v_snd_554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_n_580_, lean_object* v_as_581_, lean_object* v_lo_582_, lean_object* v_hi_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_580_, v_as_581_, v_lo_582_, v_hi_583_);
lean_dec(v_hi_583_);
lean_dec(v_n_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_586_ = lean_array_mk(v_es_585_);
v___x_587_ = lean_array_get_size(v___x_586_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_nat_dec_eq(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___y_593_; uint8_t v___x_597_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_sub(v___x_587_, v___x_590_);
v___x_597_ = lean_nat_dec_le(v___x_588_, v___x_591_);
if (v___x_597_ == 0)
{
lean_inc(v___x_591_);
v___y_593_ = v___x_591_;
goto v___jp_592_;
}
else
{
v___y_593_ = v___x_588_;
goto v___jp_592_;
}
v___jp_592_:
{
uint8_t v___x_594_; 
v___x_594_ = lean_nat_dec_le(v___y_593_, v___x_591_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v___x_591_);
lean_inc(v___y_593_);
v___x_595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_587_, v___x_586_, v___y_593_, v___y_593_);
lean_dec(v___y_593_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_587_, v___x_586_, v___y_593_, v___x_591_);
lean_dec(v___x_591_);
return v___x_596_;
}
}
}
else
{
return v___x_586_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_598_, lean_object* v_x2_599_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_NameSet_contains(v_x1_598_, v_x2_599_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
v___x_601_ = 1;
return v___x_601_;
}
else
{
uint8_t v___x_602_; 
v___x_602_ = 0;
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_603_, lean_object* v_x2_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_603_, v_x2_604_);
lean_dec(v_x2_604_);
lean_dec(v_x1_603_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_616_, lean_object* v_asyncMode_617_){
_start:
{
lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___f_619_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_620_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_621_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_622_ = lean_box(0);
v___x_623_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_624_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_624_, 0, v_name_616_);
lean_ctor_set(v___x_624_, 1, v___f_619_);
lean_ctor_set(v___x_624_, 2, v___f_620_);
lean_ctor_set(v___x_624_, 3, v___f_621_);
lean_ctor_set(v___x_624_, 4, v___x_622_);
lean_ctor_set(v___x_624_, 5, v_asyncMode_617_);
lean_ctor_set(v___x_624_, 6, v___x_623_);
v___x_625_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_626_, lean_object* v_asyncMode_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_mkTagDeclarationExtension(v_name_626_, v_asyncMode_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_630_, lean_object* v_as_631_, lean_object* v_lo_632_, lean_object* v_hi_633_, lean_object* v_w_634_, lean_object* v_hlo_635_, lean_object* v_hhi_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_630_, v_as_631_, v_lo_632_, v_hi_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_638_, lean_object* v_as_639_, lean_object* v_lo_640_, lean_object* v_hi_641_, lean_object* v_w_642_, lean_object* v_hlo_643_, lean_object* v_hhi_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_638_, v_as_639_, v_lo_640_, v_hi_641_, v_w_642_, v_hlo_643_, v_hhi_644_);
lean_dec(v_hi_641_);
lean_dec(v_n_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object* v_n_646_, lean_object* v_lo_647_, lean_object* v_hi_648_, lean_object* v_hhi_649_, lean_object* v_pivot_650_, lean_object* v_as_651_, lean_object* v_i_652_, lean_object* v_k_653_, lean_object* v_ilo_654_, lean_object* v_ik_655_, lean_object* v_w_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_648_, v_pivot_650_, v_as_651_, v_i_652_, v_k_653_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object* v_n_658_, lean_object* v_lo_659_, lean_object* v_hi_660_, lean_object* v_hhi_661_, lean_object* v_pivot_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_k_665_, lean_object* v_ilo_666_, lean_object* v_ik_667_, lean_object* v_w_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_658_, v_lo_659_, v_hi_660_, v_hhi_661_, v_pivot_662_, v_as_663_, v_i_664_, v_k_665_, v_ilo_666_, v_ik_667_, v_w_668_);
lean_dec(v_pivot_662_);
lean_dec(v_hi_660_);
lean_dec(v_lo_659_);
lean_dec(v_n_658_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_675_, v___y_676_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v_x_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_679_, lean_object* v_x_680_){
_start:
{
lean_inc_ref(v_s_679_);
return v_s_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_681_, v_x_682_);
lean_dec(v_x_682_);
lean_dec_ref(v_s_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1));
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_691_, v_x_692_);
lean_dec_ref(v_x_692_);
lean_dec_ref(v_x_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_box(0);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_696_);
lean_dec_ref(v_x_696_);
return v_res_697_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___f_702_; lean_object* v___f_703_; lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___f_702_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_703_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_704_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_705_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_706_ = lean_box(0);
v___x_707_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_708_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_706_);
lean_ctor_set(v___x_708_, 2, v___f_705_);
lean_ctor_set(v___x_708_, 3, v___f_704_);
lean_ctor_set(v___x_708_, 4, v___f_703_);
lean_ctor_set(v___x_708_, 5, v___f_702_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_711_, lean_object* v_msg_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_panic_fn_borrowed(v_env_711_, v_msg_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object* v_env_714_, lean_object* v_msg_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_714_, v_msg_715_);
lean_dec_ref(v_env_714_);
return v_res_716_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_720_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_unsigned_to_nat(115u);
v___x_723_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_724_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_725_ = l_mkPanicMessageWithDecl(v___x_724_, v___x_723_, v___x_722_, v___x_721_, v___x_720_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_726_, lean_object* v_env_727_, lean_object* v_declName_728_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Name_isAnonymous(v_declName_728_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_727_, v_declName_728_);
if (lean_obj_tag(v___x_734_) == 0)
{
goto v___jp_729_;
}
else
{
lean_dec_ref_known(v___x_734_, 1);
if (v___x_733_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v_declName_728_);
lean_dec_ref(v_ext_726_);
v___x_735_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_736_ = lean_panic_fn_borrowed(v_env_727_, v___x_735_);
lean_dec_ref(v_env_727_);
return v___x_736_;
}
else
{
goto v___jp_729_;
}
}
}
else
{
lean_dec(v_declName_728_);
lean_dec_ref(v_ext_726_);
return v_env_727_;
}
v___jp_729_:
{
lean_object* v_toEnvExtension_730_; lean_object* v_asyncMode_731_; lean_object* v___x_732_; 
v_toEnvExtension_730_ = lean_ctor_get(v_ext_726_, 0);
v_asyncMode_731_ = lean_ctor_get(v_toEnvExtension_730_, 2);
lean_inc(v_asyncMode_731_);
lean_inc(v_declName_728_);
v___x_732_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_726_, v_env_727_, v_declName_728_, v_asyncMode_731_, v_declName_728_);
lean_dec(v_asyncMode_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object* v___y_737_, lean_object* v_as_738_, lean_object* v_k_739_, lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_m_744_; lean_object* v_a_745_; uint8_t v___x_746_; 
v___x_742_ = lean_nat_add(v_x_740_, v_x_741_);
v___x_743_ = lean_unsigned_to_nat(1u);
v_m_744_ = lean_nat_shiftr(v___x_742_, v___x_743_);
lean_dec(v___x_742_);
v_a_745_ = lean_array_fget_borrowed(v_as_738_, v_m_744_);
v___x_746_ = l_Lean_Name_quickLt(v_a_745_, v_k_739_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; uint8_t v___x_748_; 
lean_dec(v_x_741_);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = l_Lean_Name_quickLt(v_k_739_, v_a_745_);
if (v___x_748_ == 0)
{
uint8_t v___x_749_; 
lean_dec(v_m_744_);
lean_dec(v_x_740_);
v___x_749_ = lean_nat_dec_le(v___x_747_, v___y_737_);
return v___x_749_;
}
else
{
uint8_t v___x_750_; lean_object* v___x_751_; uint8_t v___y_753_; 
v___x_750_ = lean_nat_dec_eq(v_m_744_, v___x_747_);
v___x_751_ = lean_nat_sub(v_m_744_, v___x_743_);
lean_dec(v_m_744_);
if (v___x_750_ == 0)
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_lt(v___x_751_, v_x_740_);
v___y_753_ = v___x_755_;
goto v___jp_752_;
}
else
{
v___y_753_ = v___x_750_;
goto v___jp_752_;
}
v___jp_752_:
{
if (v___y_753_ == 0)
{
v_x_741_ = v___x_751_;
goto _start;
}
else
{
lean_dec(v___x_751_);
lean_dec(v_x_740_);
return v___x_746_;
}
}
}
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
lean_dec(v_x_740_);
v___x_756_ = lean_nat_add(v_m_744_, v___x_743_);
lean_dec(v_m_744_);
v___x_757_ = lean_nat_dec_le(v___x_756_, v_x_741_);
if (v___x_757_ == 0)
{
lean_dec(v___x_756_);
lean_dec(v_x_741_);
return v___x_757_;
}
else
{
v_x_740_ = v___x_756_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object* v___y_759_, lean_object* v_as_760_, lean_object* v_k_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_759_, v_as_760_, v_k_761_, v_x_762_, v_x_763_);
lean_dec(v_k_761_);
lean_dec_ref(v_as_760_);
lean_dec(v___y_759_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_769_, lean_object* v_env_770_, lean_object* v_declName_771_, lean_object* v_asyncMode_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_box(1);
v___x_774_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_770_, v_declName_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
lean_inc(v_declName_771_);
v___x_775_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_773_, v_ext_769_, v_env_770_, v_asyncMode_772_, v_declName_771_);
v___x_776_ = l_Lean_NameSet_contains(v___x_775_, v_declName_771_);
lean_dec(v_declName_771_);
lean_dec(v___x_775_);
return v___x_776_;
}
else
{
lean_object* v_val_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_val_777_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v___x_774_, 1);
v___x_778_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_779_ = 0;
v___x_780_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_778_, v_ext_769_, v_env_770_, v_val_777_, v___x_779_);
lean_dec(v_val_777_);
lean_dec_ref(v_env_770_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v___x_780_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_dec_ref(v___x_780_);
lean_dec(v_declName_771_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_sub(v___x_782_, v___x_784_);
v___x_786_ = lean_nat_dec_le(v___x_781_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec(v___x_785_);
lean_dec_ref(v___x_780_);
lean_dec(v_declName_771_);
return v___x_786_;
}
else
{
uint8_t v___x_787_; 
lean_inc(v___x_785_);
v___x_787_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_785_, v___x_780_, v_declName_771_, v___x_781_, v___x_785_);
lean_dec(v_declName_771_);
lean_dec_ref(v___x_780_);
lean_dec(v___x_785_);
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_788_, lean_object* v_env_789_, lean_object* v_declName_790_, lean_object* v_asyncMode_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_788_, v_env_789_, v_declName_790_, v_asyncMode_791_);
lean_dec(v_asyncMode_791_);
lean_dec_ref(v_ext_788_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object* v___y_794_, lean_object* v_as_795_, lean_object* v_k_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_794_, v_as_795_, v_k_796_, v_x_797_, v_x_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object* v___y_801_, lean_object* v_as_802_, lean_object* v_k_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v___y_801_, v_as_802_, v_k_803_, v_x_804_, v_x_805_, v_x_806_);
lean_dec(v_k_803_);
lean_dec_ref(v_as_802_);
lean_dec(v___y_801_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(lean_object* v_x_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed(lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(v_x_814_, v___y_815_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_x_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(lean_object* v_s_818_, lean_object* v_x_819_){
_start:
{
lean_inc(v_s_818_);
return v_s_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed(lean_object* v_s_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(v_s_820_, v_x_821_);
lean_dec_ref(v_x_821_);
lean_dec(v_s_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1));
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed(lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(v_x_830_, v_x_831_);
lean_dec(v_x_831_);
lean_dec_ref(v_x_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_box(0);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed(lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(v_x_835_);
lean_dec(v_x_835_);
return v_res_836_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___f_841_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_842_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2));
v___f_843_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1));
v___f_844_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0));
v___x_845_ = lean_box(0);
v___x_846_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_847_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_845_);
lean_ctor_set(v___x_847_, 2, v___f_844_);
lean_ctor_set(v___x_847_, 3, v___f_843_);
lean_ctor_set(v___x_847_, 4, v___f_842_);
lean_ctor_set(v___x_847_, 5, v___f_841_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg(){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___boxed(lean_object* v___dummy_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v_res_851_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0(void){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_00_u03b1_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg(){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg___boxed(lean_object* v___dummy_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_instInhabitedMapDeclarationExtension___redArg();
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_866_; 
v_fst_864_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_fst_864_);
v_snd_865_ = lean_ctor_get(v_x_863_, 1);
lean_inc(v_snd_865_);
lean_dec_ref(v_x_863_);
v___x_866_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_864_, v_snd_865_, v_s_862_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_867_, lean_object* v_env_868_, lean_object* v_s_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_apply_2(v_exportEntriesFn_867_, v_env_868_, v_s_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
return v_x_872_;
}
else
{
lean_object* v_head_874_; lean_object* v_tail_875_; lean_object* v___x_876_; 
v_head_874_ = lean_ctor_get(v_x_873_, 0);
lean_inc(v_head_874_);
v_tail_875_ = lean_ctor_get(v_x_873_, 1);
lean_inc(v_tail_875_);
lean_dec_ref_known(v_x_873_, 2);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_871_, v_head_874_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_878_; 
v_val_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_874_, v_val_877_, v_x_872_);
v_x_872_ = v___x_878_;
v_x_873_ = v_tail_875_;
goto _start;
}
else
{
lean_dec(v___x_876_);
lean_dec(v_head_874_);
v_x_873_ = v_tail_875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_881_, v_x_882_, v_x_883_);
lean_dec(v_newState_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_885_, lean_object* v_newState_886_, lean_object* v_newConsts_887_, lean_object* v_s_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_886_, v_s_888_, v_newConsts_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_890_, lean_object* v_newState_891_, lean_object* v_newConsts_892_, lean_object* v_s_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_890_, v_newState_891_, v_newConsts_892_, v_s_893_);
lean_dec(v_newState_891_);
lean_dec(v_x_890_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0));
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_897_);
lean_dec(v_x_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_905_, lean_object* v_x_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_910_, v_x_911_, v___y_912_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_x_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_924_, lean_object* v_asyncMode_925_, lean_object* v_exportEntriesFn_926_){
_start:
{
lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___f_928_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_929_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1), 3, 1);
lean_closure_set(v___f_929_, 0, v_exportEntriesFn_926_);
v___f_930_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_931_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_932_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_933_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_934_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_935_ = 0;
v___x_936_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_936_, 0, v_name_924_);
lean_ctor_set(v___x_936_, 1, v___f_932_);
lean_ctor_set(v___x_936_, 2, v___f_933_);
lean_ctor_set(v___x_936_, 3, v___f_928_);
lean_ctor_set(v___x_936_, 4, v___f_929_);
lean_ctor_set(v___x_936_, 5, v___f_930_);
lean_ctor_set(v___x_936_, 6, v_asyncMode_925_);
lean_ctor_set(v___x_936_, 7, v___x_934_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*8, v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___f_931_);
v___x_938_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_938_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_938_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_955_, lean_object* v_asyncMode_956_, lean_object* v_exportEntriesFn_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_955_, v_asyncMode_956_, v_exportEntriesFn_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_960_, lean_object* v_name_961_, lean_object* v_asyncMode_962_, lean_object* v_exportEntriesFn_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_961_, v_asyncMode_962_, v_exportEntriesFn_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_966_, lean_object* v_name_967_, lean_object* v_asyncMode_968_, lean_object* v_exportEntriesFn_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_966_, v_name_967_, v_asyncMode_968_, v_exportEntriesFn_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_972_, lean_object* v_newState_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_973_, v_x_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_977_, lean_object* v_newState_978_, lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_977_, v_newState_978_, v_x_979_, v_x_980_);
lean_dec(v_newState_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_987_, lean_object* v_env_988_, lean_object* v_declName_989_, lean_object* v_val_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_988_, v_declName_989_);
if (lean_obj_tag(v___x_991_) == 1)
{
lean_object* v_val_992_; lean_object* v_name_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_val_990_);
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_991_, 1);
v_name_993_ = lean_ctor_get(v_ext_987_, 1);
lean_inc(v_name_993_);
lean_dec_ref(v_ext_987_);
v___x_994_ = lean_box(0);
v___x_995_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_996_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_997_ = lean_unsigned_to_nat(159u);
v___x_998_ = lean_unsigned_to_nat(4u);
v___x_999_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1000_ = 1;
v___x_1001_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_989_, v___x_1000_);
v___x_1002_ = lean_string_append(v___x_999_, v___x_1001_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
v___x_1005_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_993_, v___x_1000_);
v___x_1006_ = lean_string_append(v___x_1004_, v___x_1005_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_1008_ = lean_string_append(v___x_1006_, v___x_1007_);
v___x_1009_ = l_Lean_Environment_allImportedModuleNames(v_env_988_);
v___x_1010_ = lean_array_get(v___x_994_, v___x_1009_, v_val_992_);
lean_dec(v_val_992_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1010_, v___x_1000_);
v___x_1012_ = lean_string_append(v___x_1008_, v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
v___x_1015_ = l_mkPanicMessageWithDecl(v___x_995_, v___x_996_, v___x_997_, v___x_998_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = lean_panic_fn_borrowed(v_env_988_, v___x_1015_);
lean_dec_ref(v_env_988_);
return v___x_1016_;
}
else
{
lean_object* v_toEnvExtension_1017_; lean_object* v_asyncMode_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v___x_991_);
v_toEnvExtension_1017_ = lean_ctor_get(v_ext_987_, 0);
v_asyncMode_1018_ = lean_ctor_get(v_toEnvExtension_1017_, 2);
lean_inc(v_asyncMode_1018_);
lean_inc(v_declName_989_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_declName_989_);
lean_ctor_set(v___x_1019_, 1, v_val_990_);
v___x_1020_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_987_, v_env_988_, v___x_1019_, v_asyncMode_1018_, v_declName_989_);
lean_dec(v_asyncMode_1018_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_1021_, lean_object* v_ext_1022_, lean_object* v_env_1023_, lean_object* v_declName_1024_, lean_object* v_val_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1022_, v_env_1023_, v_declName_1024_, v_val_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object* v_a_1027_, lean_object* v_b_1028_){
_start:
{
lean_object* v_fst_1029_; lean_object* v_fst_1030_; uint8_t v___x_1031_; 
v_fst_1029_ = lean_ctor_get(v_a_1027_, 0);
v_fst_1030_ = lean_ctor_get(v_b_1028_, 0);
v___x_1031_ = l_Lean_Name_quickLt(v_fst_1029_, v_fst_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object* v_a_1032_, lean_object* v_b_1033_){
_start:
{
uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_res_1034_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_1032_, v_b_1033_);
lean_dec_ref(v_b_1033_);
lean_dec_ref(v_a_1032_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_inst_1038_, lean_object* v_ext_1039_, lean_object* v_env_1040_, lean_object* v_declName_1041_, lean_object* v_asyncMode_1042_, uint8_t v_level_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(1);
v___x_1045_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1040_, v_declName_1041_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v_inst_1038_);
lean_inc(v_declName_1041_);
v___x_1046_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1044_, v_ext_1039_, v_env_1040_, v_asyncMode_1042_, v_declName_1041_);
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1046_, v_declName_1041_);
lean_dec(v_declName_1041_);
lean_dec(v___x_1046_);
return v___x_1047_;
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_val_1048_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1049_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1044_, v_ext_1039_, v_env_1040_, v_val_1048_, v_level_1043_);
lean_dec(v_val_1048_);
lean_dec_ref(v_env_1040_);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_array_get_size(v___x_1049_);
v___x_1052_ = lean_nat_dec_lt(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v___x_1049_);
lean_dec(v_declName_1041_);
lean_dec(v_inst_1038_);
v___x_1053_ = lean_box(0);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_sub(v___x_1051_, v___x_1054_);
v___x_1056_ = lean_nat_dec_le(v___x_1050_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1049_);
lean_dec(v_declName_1041_);
lean_dec(v_inst_1038_);
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
else
{
lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___f_1058_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_declName_1041_);
lean_ctor_set(v___x_1059_, 1, v_inst_1038_);
v___x_1060_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1));
v___x_1061_ = l_Array_binSearchAux___redArg(v___f_1058_, v___x_1060_, v___x_1049_, v___x_1059_, v___x_1050_, v___x_1055_);
lean_dec_ref(v___x_1049_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_box(0);
return v___x_1062_;
}
else
{
lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_val_1063_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v___x_1061_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_dec(v___x_1061_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_snd_1067_; lean_object* v___x_1069_; 
v_snd_1067_ = lean_ctor_get(v_val_1063_, 1);
lean_inc(v_snd_1067_);
lean_dec(v_val_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_snd_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_snd_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_inst_1072_, lean_object* v_ext_1073_, lean_object* v_env_1074_, lean_object* v_declName_1075_, lean_object* v_asyncMode_1076_, lean_object* v_level_1077_){
_start:
{
uint8_t v_level_boxed_1078_; lean_object* v_res_1079_; 
v_level_boxed_1078_ = lean_unbox(v_level_1077_);
v_res_1079_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1072_, v_ext_1073_, v_env_1074_, v_declName_1075_, v_asyncMode_1076_, v_level_boxed_1078_);
lean_dec(v_asyncMode_1076_);
lean_dec_ref(v_ext_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1080_, lean_object* v_inst_1081_, lean_object* v_ext_1082_, lean_object* v_env_1083_, lean_object* v_declName_1084_, lean_object* v_asyncMode_1085_, uint8_t v_level_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1081_, v_ext_1082_, v_env_1083_, v_declName_1084_, v_asyncMode_1085_, v_level_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1088_, lean_object* v_inst_1089_, lean_object* v_ext_1090_, lean_object* v_env_1091_, lean_object* v_declName_1092_, lean_object* v_asyncMode_1093_, lean_object* v_level_1094_){
_start:
{
uint8_t v_level_boxed_1095_; lean_object* v_res_1096_; 
v_level_boxed_1095_ = lean_unbox(v_level_1094_);
v_res_1096_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1088_, v_inst_1089_, v_ext_1090_, v_env_1091_, v_declName_1092_, v_asyncMode_1093_, v_level_boxed_1095_);
lean_dec(v_asyncMode_1093_);
lean_dec_ref(v_ext_1090_);
return v_res_1096_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_inst_1098_, lean_object* v_ext_1099_, lean_object* v_env_1100_, lean_object* v_declName_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_box(1);
v___x_1103_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1100_, v_declName_1101_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_toEnvExtension_1104_; lean_object* v_asyncMode_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
lean_dec(v_inst_1098_);
v_toEnvExtension_1104_ = lean_ctor_get(v_ext_1099_, 0);
v_asyncMode_1105_ = lean_ctor_get(v_toEnvExtension_1104_, 2);
lean_inc(v_declName_1101_);
v___x_1106_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1102_, v_ext_1099_, v_env_1100_, v_asyncMode_1105_, v_declName_1101_);
v___x_1107_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1101_, v___x_1106_);
lean_dec(v___x_1106_);
lean_dec(v_declName_1101_);
return v___x_1107_;
}
else
{
lean_object* v_val_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_val_1108_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1109_ = 0;
v___x_1110_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1102_, v_ext_1099_, v_env_1100_, v_val_1108_, v___x_1109_);
lean_dec(v_val_1108_);
lean_dec_ref(v_env_1100_);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_array_get_size(v___x_1110_);
v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v___x_1110_);
lean_dec(v_declName_1101_);
lean_dec(v_inst_1098_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_sub(v___x_1112_, v___x_1114_);
v___x_1116_ = lean_nat_dec_le(v___x_1111_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec(v___x_1115_);
lean_dec_ref(v___x_1110_);
lean_dec(v_declName_1101_);
lean_dec(v_inst_1098_);
return v___x_1116_;
}
else
{
lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___f_1117_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_declName_1101_);
lean_ctor_set(v___x_1118_, 1, v_inst_1098_);
v___x_1119_ = ((lean_object*)(l_Lean_MapDeclarationExtension_contains___redArg___closed__0));
v___x_1120_ = l_Array_binSearchAux___redArg(v___f_1117_, v___x_1119_, v___x_1110_, v___x_1118_, v___x_1111_, v___x_1115_);
lean_dec_ref(v___x_1110_);
v___x_1121_ = lean_unbox(v___x_1120_);
lean_dec(v___x_1120_);
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_inst_1122_, lean_object* v_ext_1123_, lean_object* v_env_1124_, lean_object* v_declName_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1122_, v_ext_1123_, v_env_1124_, v_declName_1125_);
lean_dec_ref(v_ext_1123_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1128_, lean_object* v_inst_1129_, lean_object* v_ext_1130_, lean_object* v_env_1131_, lean_object* v_declName_1132_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1129_, v_ext_1130_, v_env_1131_, v_declName_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_inst_1135_, lean_object* v_ext_1136_, lean_object* v_env_1137_, lean_object* v_declName_1138_){
_start:
{
uint8_t v_res_1139_; lean_object* v_r_1140_; 
v_res_1139_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1134_, v_inst_1135_, v_ext_1136_, v_env_1137_, v_declName_1138_);
lean_dec_ref(v_ext_1136_);
v_r_1140_ = lean_box(v_res_1139_);
return v_r_1140_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
