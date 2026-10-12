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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_logDeclChange(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_TagDeclarationExtension_tag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.EnvExtension"};
static const lean_object* l_Lean_TagDeclarationExtension_tag___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_tag___closed__0_value;
static const lean_string_object l_Lean_TagDeclarationExtension_tag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.TagDeclarationExtension.tag"};
static const lean_object* l_Lean_TagDeclarationExtension_tag___closed__1 = (const lean_object*)&l_Lean_TagDeclarationExtension_tag___closed__1_value;
static const lean_string_object l_Lean_TagDeclarationExtension_tag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 310, .m_capacity = 310, .m_length = 309, .m_data = "assertion violation: env.getModuleIdxFor\? declName |>.isNone -- See comment at `TagDeclarationExtension`\n    -- Only the state visible on this branch, as in `MapDeclarationExtension.insert`: a tag added on\n    -- the still-running branch of `declName` is missed, which only costs a superfluous log entry.\n    "};
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
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_MapDeclarationExtension_insert___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "`, it is already present; declaration-keyed extension entries are write-once (pass `allowOverwrite := true` if this update is intended)"};
static const lean_object* l_Lean_MapDeclarationExtension_insert___redArg___closed__5 = (const lean_object*)&l_Lean_MapDeclarationExtension_insert___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(lean_object* v_addImportedFn_247_, lean_object* v___x_248_, lean_object* v_as_249_, lean_object* v___y_250_){
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
LEAN_EXPORT void l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_addImportedFn_247_ = stack[0].m_obj;
lean_object* v___x_248_ = stack[1].m_obj;
lean_object* v_as_249_ = stack[2].m_obj;
lean_object* v___y_250_ = stack[3].m_obj;
lean_object* v_res_255_;
v_res_255_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(v_addImportedFn_247_, v___x_248_, v_as_249_, v___y_250_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed(lean_object* v_addImportedFn_256_, lean_object* v___x_257_, lean_object* v_as_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(v_addImportedFn_256_, v___x_257_, v_as_258_, v___y_259_);
lean_dec_ref(v___y_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object* v_val_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_fst_267_; lean_object* v_snd_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v_fst_271_; lean_object* v_newEntries_272_; lean_object* v___x_273_; lean_object* v_fst_274_; lean_object* v_snd_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
v_fst_267_ = lean_ctor_get(v___y_266_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v___y_266_, 1);
lean_inc(v_snd_268_);
lean_dec_ref(v___y_266_);
v_fst_269_ = lean_ctor_get(v___y_264_, 0);
lean_inc(v_fst_269_);
v_snd_270_ = lean_ctor_get(v___y_264_, 1);
lean_inc(v_snd_270_);
lean_dec_ref(v___y_264_);
v_fst_271_ = lean_ctor_get(v___y_263_, 0);
v_newEntries_272_ = l_Lean_takeNewEntries___redArg(v_fst_269_, v_fst_271_);
v___x_273_ = lean_apply_3(v_val_262_, v_newEntries_272_, v_snd_270_, v_snd_268_);
v_fst_274_ = lean_ctor_get(v___x_273_, 0);
v_snd_275_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_283_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_275_);
lean_inc(v_fst_274_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = l_List_appendTR___redArg(v_fst_274_, v_fst_267_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_snd_275_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object* v_val_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(v_val_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_285_);
return v_res_289_;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object* v_descr_294_){
_start:
{
lean_object* v_name_296_; lean_object* v_addEntryFn_297_; lean_object* v_addImportedFn_298_; lean_object* v_toArrayFn_299_; lean_object* v_exportEntriesFnEx_x3f_300_; lean_object* v_asyncMode_301_; lean_object* v_replay_x3f_302_; uint8_t v_logWrites_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___y_315_; 
v_name_296_ = lean_ctor_get(v_descr_294_, 0);
lean_inc(v_name_296_);
v_addEntryFn_297_ = lean_ctor_get(v_descr_294_, 1);
lean_inc(v_addEntryFn_297_);
v_addImportedFn_298_ = lean_ctor_get(v_descr_294_, 2);
lean_inc_n(v_addImportedFn_298_, 2);
v_toArrayFn_299_ = lean_ctor_get(v_descr_294_, 3);
lean_inc_ref(v_toArrayFn_299_);
v_exportEntriesFnEx_x3f_300_ = lean_ctor_get(v_descr_294_, 4);
lean_inc(v_exportEntriesFnEx_x3f_300_);
v_asyncMode_301_ = lean_ctor_get(v_descr_294_, 5);
lean_inc(v_asyncMode_301_);
v_replay_x3f_302_ = lean_ctor_get(v_descr_294_, 6);
lean_inc(v_replay_x3f_302_);
v_logWrites_303_ = lean_ctor_get_uint8(v_descr_294_, sizeof(void*)*7);
lean_dec_ref(v_descr_294_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0), 3, 1);
lean_closure_set(v___f_304_, 0, v_addEntryFn_297_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1), 4, 2);
lean_closure_set(v___f_305_, 0, v_exportEntriesFnEx_x3f_300_);
lean_closure_set(v___f_305_, 1, v_toArrayFn_299_);
v___f_306_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0));
v___f_307_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1));
v___x_308_ = lean_box(0);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_309_, 0, v_addImportedFn_298_);
lean_closure_set(v___f_309_, 1, v___x_308_);
v___x_310_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2));
v___x_311_ = lean_apply_1(v_addImportedFn_298_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_308_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_313_, 0, lean_box(0));
lean_closure_set(v___x_313_, 1, lean_box(0));
lean_closure_set(v___x_313_, 2, v___x_312_);
if (lean_obj_tag(v_replay_x3f_302_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
v___y_315_ = v___x_320_;
goto v___jp_314_;
}
else
{
lean_object* v_val_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_val_321_ = lean_ctor_get(v_replay_x3f_302_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_replay_x3f_302_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v_replay_x3f_302_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_val_321_);
lean_dec(v_replay_x3f_302_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___f_325_; lean_object* v___x_327_; 
v___f_325_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed), 5, 1);
lean_closure_set(v___f_325_, 0, v_val_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___f_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___f_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v___y_315_ = v___x_327_;
goto v___jp_314_;
}
}
}
v___jp_314_:
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_317_, 0, v_name_296_);
lean_ctor_set(v___x_317_, 1, v___x_313_);
lean_ctor_set(v___x_317_, 2, v___f_309_);
lean_ctor_set(v___x_317_, 3, v___f_304_);
lean_ctor_set(v___x_317_, 4, v___f_305_);
lean_ctor_set(v___x_317_, 5, v___f_306_);
lean_ctor_set(v___x_317_, 6, v_asyncMode_301_);
lean_ctor_set(v___x_317_, 7, v___y_315_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*8, v___x_316_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*8 + 1, v_logWrites_303_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___f_307_);
v___x_319_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT void l_Lean_registerSimplePersistentEnvExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_294_ = stack[0].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_294_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object* v_descr_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_331_);
return v_res_333_;
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* v_00_u03b1_334_, lean_object* v_00_u03c3_335_, lean_object* v_inst_336_, lean_object* v_descr_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_337_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Lean_registerSimplePersistentEnvExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_336_ = stack[2].m_obj;
lean_object* v_descr_337_ = stack[3].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_registerSimplePersistentEnvExtension(lean_box(0), lean_box(0), v_inst_336_, v_descr_337_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* v_00_u03b1_341_, lean_object* v_00_u03c3_342_, lean_object* v_inst_343_, lean_object* v_descr_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_registerSimplePersistentEnvExtension(v_00_u03b1_341_, v_00_u03c3_342_, v_inst_343_, v_descr_344_);
lean_dec(v_inst_343_);
return v_res_346_;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object* v_x_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT void l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_350_ = stack[0].m_obj;
lean_object* v___y_351_ = stack[1].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_350_, v___y_351_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_356_, v___y_357_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_x_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(lean_object* v_s_360_, lean_object* v_x_361_){
_start:
{
lean_inc_ref(v_s_360_);
return v_s_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1___boxed(lean_object* v_s_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(v_s_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec_ref(v_s_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0));
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(v_x_370_, v_x_371_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(lean_object* v_x_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_box(0);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3___boxed(lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(v_x_375_);
lean_dec_ref(v_x_375_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_381_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5(void){
_start:
{
lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___f_382_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3));
v___f_383_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2));
v___f_384_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1));
v___f_385_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0));
v___x_386_ = lean_box(0);
v___x_387_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_388_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___f_385_);
lean_ctor_set(v___x_388_, 3, v___f_384_);
lean_ctor_set(v___x_388_, 4, v___f_383_);
lean_ctor_set(v___x_388_, 5, v___f_382_);
return v___x_388_;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_390_;
}
}
LEAN_EXPORT void l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_391_;
v_res_391_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg();
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg();
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object* v_00_u03b1_394_, lean_object* v_00_u03c3_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_396_;
}
}
lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg(){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_398_;
}
}
LEAN_EXPORT void l_Lean_SimplePersistentEnvExtension_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_399_;
v_res_399_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg___boxed(lean_object* v___dummy_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v_res_401_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object* v_00_u03b1_403_, lean_object* v_00_u03c3_404_, lean_object* v_inst_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0, &l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object* v_00_u03b1_407_, lean_object* v_00_u03c3_408_, lean_object* v_inst_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_SimplePersistentEnvExtension_instInhabited(v_00_u03b1_407_, v_00_u03c3_408_, v_inst_409_);
lean_dec(v_inst_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object* v_inst_411_, lean_object* v_ext_412_, lean_object* v_env_413_, lean_object* v_asyncMode_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v_fst_420_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_inst_411_);
v___x_417_ = lean_box(0);
v___x_418_ = 0;
v___x_419_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_416_, v_ext_412_, v_env_413_, v_asyncMode_414_, v___x_417_, v___x_418_);
v_fst_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_fst_420_);
lean_dec(v___x_419_);
return v_fst_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object* v_inst_421_, lean_object* v_ext_422_, lean_object* v_env_423_, lean_object* v_asyncMode_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_421_, v_ext_422_, v_env_423_, v_asyncMode_424_);
lean_dec(v_asyncMode_424_);
lean_dec_ref(v_ext_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* v_00_u03b1_426_, lean_object* v_00_u03c3_427_, lean_object* v_inst_428_, lean_object* v_ext_429_, lean_object* v_env_430_, lean_object* v_asyncMode_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_428_, v_ext_429_, v_env_430_, v_asyncMode_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object* v_00_u03b1_433_, lean_object* v_00_u03c3_434_, lean_object* v_inst_435_, lean_object* v_ext_436_, lean_object* v_env_437_, lean_object* v_asyncMode_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_SimplePersistentEnvExtension_getEntries(v_00_u03b1_433_, v_00_u03c3_434_, v_inst_435_, v_ext_436_, v_env_437_, v_asyncMode_438_);
lean_dec(v_asyncMode_438_);
lean_dec_ref(v_ext_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object* v_inst_440_, lean_object* v_ext_441_, lean_object* v_env_442_, lean_object* v_asyncMode_443_, lean_object* v_asyncDecl_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v_snd_449_; 
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_inst_440_);
v___x_447_ = 0;
v___x_448_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_446_, v_ext_441_, v_env_442_, v_asyncMode_443_, v_asyncDecl_444_, v___x_447_);
v_snd_449_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_snd_449_);
lean_dec(v___x_448_);
return v_snd_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object* v_inst_450_, lean_object* v_ext_451_, lean_object* v_env_452_, lean_object* v_asyncMode_453_, lean_object* v_asyncDecl_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_450_, v_ext_451_, v_env_452_, v_asyncMode_453_, v_asyncDecl_454_);
lean_dec(v_asyncMode_453_);
lean_dec_ref(v_ext_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* v_00_u03b1_456_, lean_object* v_00_u03c3_457_, lean_object* v_inst_458_, lean_object* v_ext_459_, lean_object* v_env_460_, lean_object* v_asyncMode_461_, lean_object* v_asyncDecl_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_458_, v_ext_459_, v_env_460_, v_asyncMode_461_, v_asyncDecl_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object* v_00_u03b1_464_, lean_object* v_00_u03c3_465_, lean_object* v_inst_466_, lean_object* v_ext_467_, lean_object* v_env_468_, lean_object* v_asyncMode_469_, lean_object* v_asyncDecl_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_SimplePersistentEnvExtension_getState(v_00_u03b1_464_, v_00_u03c3_465_, v_inst_466_, v_ext_467_, v_env_468_, v_asyncMode_469_, v_asyncDecl_470_);
lean_dec(v_asyncMode_469_);
lean_dec_ref(v_ext_467_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object* v_s_472_, lean_object* v_ps_473_){
_start:
{
lean_object* v_state_474_; lean_object* v_importedEntries_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_491_; 
v_state_474_ = lean_ctor_get(v_ps_473_, 1);
v_importedEntries_475_ = lean_ctor_get(v_ps_473_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_ps_473_);
if (v_isSharedCheck_491_ == 0)
{
v___x_477_ = v_ps_473_;
v_isShared_478_ = v_isSharedCheck_491_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_state_474_);
lean_inc(v_importedEntries_475_);
lean_dec(v_ps_473_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_491_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_fst_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_489_; 
v_fst_479_ = lean_ctor_get(v_state_474_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_state_474_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_state_474_, 1);
lean_dec(v_unused_490_);
v___x_481_ = v_state_474_;
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_fst_479_);
lean_dec(v_state_474_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v_s_472_);
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fst_479_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_s_472_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_484_);
v___x_486_ = v___x_477_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_importedEntries_475_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object* v_ext_492_, lean_object* v_env_493_, lean_object* v_s_494_){
_start:
{
lean_object* v_toEnvExtension_495_; lean_object* v_asyncMode_496_; uint8_t v_logWrites_497_; lean_object* v___f_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_toEnvExtension_495_ = lean_ctor_get(v_ext_492_, 0);
lean_inc_ref(v_toEnvExtension_495_);
lean_dec_ref(v_ext_492_);
v_asyncMode_496_ = lean_ctor_get(v_toEnvExtension_495_, 2);
lean_inc(v_asyncMode_496_);
v_logWrites_497_ = lean_ctor_get_uint8(v_toEnvExtension_495_, sizeof(void*)*6);
v___f_498_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_498_, 0, v_s_494_);
v___x_499_ = lean_box(0);
v___x_500_ = 1;
if (v_logWrites_497_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_495_, v_env_493_, v___f_498_, v_asyncMode_496_, v___x_499_, v___x_500_);
lean_dec(v_asyncMode_496_);
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_inc_ref(v_toEnvExtension_495_);
v___x_502_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_495_, v_env_493_);
lean_dec_ref(v_env_493_);
v___x_503_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_495_, v___x_502_, v___f_498_, v_asyncMode_496_, v___x_499_, v___x_500_);
lean_dec(v_asyncMode_496_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* v_00_u03b1_504_, lean_object* v_00_u03c3_505_, lean_object* v_ext_506_, lean_object* v_env_507_, lean_object* v_s_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_506_, v_env_507_, v_s_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_510_, lean_object* v_ps_511_){
_start:
{
lean_object* v_state_512_; lean_object* v_importedEntries_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_530_; 
v_state_512_ = lean_ctor_get(v_ps_511_, 1);
v_importedEntries_513_ = lean_ctor_get(v_ps_511_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_ps_511_);
if (v_isSharedCheck_530_ == 0)
{
v___x_515_ = v_ps_511_;
v_isShared_516_ = v_isSharedCheck_530_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_state_512_);
lean_inc(v_importedEntries_513_);
lean_dec(v_ps_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_530_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_529_; 
v_fst_517_ = lean_ctor_get(v_state_512_, 0);
v_snd_518_ = lean_ctor_get(v_state_512_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_state_512_);
if (v_isSharedCheck_529_ == 0)
{
v___x_520_ = v_state_512_;
v_isShared_521_ = v_isSharedCheck_529_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_inc(v_fst_517_);
lean_dec(v_state_512_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_529_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_apply_1(v_f_510_, v_snd_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_524_);
v___x_526_ = v___x_515_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_importedEntries_513_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object* v_ext_531_, lean_object* v_env_532_, lean_object* v_f_533_){
_start:
{
lean_object* v_toEnvExtension_534_; lean_object* v_asyncMode_535_; uint8_t v_logWrites_536_; lean_object* v___f_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_toEnvExtension_534_ = lean_ctor_get(v_ext_531_, 0);
lean_inc_ref(v_toEnvExtension_534_);
lean_dec_ref(v_ext_531_);
v_asyncMode_535_ = lean_ctor_get(v_toEnvExtension_534_, 2);
lean_inc(v_asyncMode_535_);
v_logWrites_536_ = lean_ctor_get_uint8(v_toEnvExtension_534_, sizeof(void*)*6);
v___f_537_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_537_, 0, v_f_533_);
v___x_538_ = lean_box(0);
v___x_539_ = 1;
if (v_logWrites_536_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_534_, v_env_532_, v___f_537_, v_asyncMode_535_, v___x_538_, v___x_539_);
lean_dec(v_asyncMode_535_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_inc_ref(v_toEnvExtension_534_);
v___x_541_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_534_, v_env_532_);
lean_dec_ref(v_env_532_);
v___x_542_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_534_, v___x_541_, v___f_537_, v_asyncMode_535_, v___x_538_, v___x_539_);
lean_dec(v_asyncMode_535_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* v_00_u03b1_543_, lean_object* v_00_u03c3_544_, lean_object* v_ext_545_, lean_object* v_env_546_, lean_object* v_f_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(v_ext_545_, v_env_546_, v_f_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_NameSet_empty;
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_552_);
lean_dec_ref(v_x_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object* v_hi_554_, lean_object* v_pivot_555_, lean_object* v_as_556_, lean_object* v_i_557_, lean_object* v_k_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_lt(v_k_558_, v_hi_554_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_k_558_);
v___x_560_ = lean_array_fswap(v_as_556_, v_i_557_, v_hi_554_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_i_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_fget_borrowed(v_as_556_, v_k_558_);
v___x_563_ = l_Lean_Name_quickLt(v___x_562_, v_pivot_555_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_add(v_k_558_, v___x_564_);
lean_dec(v_k_558_);
v_k_558_ = v___x_565_;
goto _start;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_array_fswap(v_as_556_, v_i_557_, v_k_558_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_i_557_, v___x_568_);
lean_dec(v_i_557_);
v___x_570_ = lean_nat_add(v_k_558_, v___x_568_);
lean_dec(v_k_558_);
v_as_556_ = v___x_567_;
v_i_557_ = v___x_569_;
v_k_558_ = v___x_570_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object* v_hi_572_, lean_object* v_pivot_573_, lean_object* v_as_574_, lean_object* v_i_575_, lean_object* v_k_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_572_, v_pivot_573_, v_as_574_, v_i_575_, v_k_576_);
lean_dec(v_pivot_573_);
lean_dec(v_hi_572_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_n_578_, lean_object* v_as_579_, lean_object* v_lo_580_, lean_object* v_hi_581_){
_start:
{
lean_object* v___y_583_; uint8_t v___x_593_; 
v___x_593_ = lean_nat_dec_lt(v_lo_580_, v_hi_581_);
if (v___x_593_ == 0)
{
lean_dec(v_lo_580_);
return v_as_579_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_mid_596_; lean_object* v___y_598_; lean_object* v___y_604_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_594_ = lean_nat_add(v_lo_580_, v_hi_581_);
v___x_595_ = lean_unsigned_to_nat(1u);
v_mid_596_ = lean_nat_shiftr(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
v___x_609_ = lean_array_fget_borrowed(v_as_579_, v_mid_596_);
v___x_610_ = lean_array_fget_borrowed(v_as_579_, v_lo_580_);
v___x_611_ = l_Lean_Name_quickLt(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_604_ = v_as_579_;
goto v___jp_603_;
}
else
{
lean_object* v___x_612_; 
v___x_612_ = lean_array_fswap(v_as_579_, v_lo_580_, v_mid_596_);
v___y_604_ = v___x_612_;
goto v___jp_603_;
}
v___jp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = lean_array_fget_borrowed(v___y_598_, v_mid_596_);
v___x_600_ = lean_array_fget_borrowed(v___y_598_, v_hi_581_);
v___x_601_ = l_Lean_Name_quickLt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_mid_596_);
v___y_583_ = v___y_598_;
goto v___jp_582_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_array_fswap(v___y_598_, v_mid_596_, v_hi_581_);
lean_dec(v_mid_596_);
v___y_583_ = v___x_602_;
goto v___jp_582_;
}
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_array_fget_borrowed(v___y_604_, v_hi_581_);
v___x_606_ = lean_array_fget_borrowed(v___y_604_, v_lo_580_);
v___x_607_ = l_Lean_Name_quickLt(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
v___y_598_ = v___y_604_;
goto v___jp_597_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_fswap(v___y_604_, v_lo_580_, v_hi_581_);
v___y_598_ = v___x_608_;
goto v___jp_597_;
}
}
}
v___jp_582_:
{
lean_object* v_pivot_584_; lean_object* v___x_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; uint8_t v___x_588_; 
v_pivot_584_ = lean_array_fget(v___y_583_, v_hi_581_);
lean_inc_n(v_lo_580_, 2);
v___x_585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_581_, v_pivot_584_, v___y_583_, v_lo_580_, v_lo_580_);
lean_dec(v_pivot_584_);
v_fst_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_fst_586_);
v_snd_587_ = lean_ctor_get(v___x_585_, 1);
lean_inc(v_snd_587_);
lean_dec_ref(v___x_585_);
v___x_588_ = lean_nat_dec_le(v_hi_581_, v_fst_586_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_578_, v_snd_587_, v_lo_580_, v_fst_586_);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_fst_586_, v___x_590_);
lean_dec(v_fst_586_);
v_as_579_ = v___x_589_;
v_lo_580_ = v___x_591_;
goto _start;
}
else
{
lean_dec(v_fst_586_);
lean_dec(v_lo_580_);
return v_snd_587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_n_613_, lean_object* v_as_614_, lean_object* v_lo_615_, lean_object* v_hi_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_613_, v_as_614_, v_lo_615_, v_hi_616_);
lean_dec(v_hi_616_);
lean_dec(v_n_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_array_mk(v_es_618_);
v___x_620_ = lean_array_get_size(v___x_619_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___y_626_; uint8_t v___x_630_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_sub(v___x_620_, v___x_623_);
v___x_630_ = lean_nat_dec_le(v___x_621_, v___x_624_);
if (v___x_630_ == 0)
{
lean_inc(v___x_624_);
v___y_626_ = v___x_624_;
goto v___jp_625_;
}
else
{
v___y_626_ = v___x_621_;
goto v___jp_625_;
}
v___jp_625_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v___y_626_, v___x_624_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec(v___x_624_);
lean_inc(v___y_626_);
v___x_628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_620_, v___x_619_, v___y_626_, v___y_626_);
lean_dec(v___y_626_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_620_, v___x_619_, v___y_626_, v___x_624_);
lean_dec(v___x_624_);
return v___x_629_;
}
}
}
else
{
return v___x_619_;
}
}
}
uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_631_, lean_object* v_x2_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_NameSet_contains(v_x1_631_, v_x2_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = 1;
return v___x_634_;
}
else
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
}
LEAN_EXPORT void l_Lean_mkTagDeclarationExtension___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_631_ = stack[0].m_obj;
lean_object* v_x2_632_ = stack[1].m_obj;
uint8_t v_res_636_;
v_res_636_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_631_, v_x2_632_);
stack->m_num = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_637_, lean_object* v_x2_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_637_, v_x2_638_);
lean_dec(v_x2_638_);
lean_dec(v_x1_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_650_, lean_object* v_asyncMode_651_, uint8_t v_logWrites_652_){
_start:
{
lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___f_654_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_655_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_656_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_659_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_659_, 0, v_name_650_);
lean_ctor_set(v___x_659_, 1, v___f_654_);
lean_ctor_set(v___x_659_, 2, v___f_655_);
lean_ctor_set(v___x_659_, 3, v___f_656_);
lean_ctor_set(v___x_659_, 4, v___x_657_);
lean_ctor_set(v___x_659_, 5, v_asyncMode_651_);
lean_ctor_set(v___x_659_, 6, v___x_658_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*7, v_logWrites_652_);
v___x_660_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT void l_Lean_mkTagDeclarationExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_650_ = stack[0].m_obj;
lean_object* v_asyncMode_651_ = stack[1].m_obj;
uint8_t v_logWrites_652_ = stack[2].m_num;
lean_object* v_res_661_;
v_res_661_ = l_Lean_mkTagDeclarationExtension(v_name_650_, v_asyncMode_651_, v_logWrites_652_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_662_, lean_object* v_asyncMode_663_, lean_object* v_logWrites_664_, lean_object* v_a_665_){
_start:
{
uint8_t v_logWrites_boxed_666_; lean_object* v_res_667_; 
v_logWrites_boxed_666_ = lean_unbox(v_logWrites_664_);
v_res_667_ = l_Lean_mkTagDeclarationExtension(v_name_662_, v_asyncMode_663_, v_logWrites_boxed_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_668_, lean_object* v_as_669_, lean_object* v_lo_670_, lean_object* v_hi_671_, lean_object* v_w_672_, lean_object* v_hlo_673_, lean_object* v_hhi_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_668_, v_as_669_, v_lo_670_, v_hi_671_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_676_, lean_object* v_as_677_, lean_object* v_lo_678_, lean_object* v_hi_679_, lean_object* v_w_680_, lean_object* v_hlo_681_, lean_object* v_hhi_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_676_, v_as_677_, v_lo_678_, v_hi_679_, v_w_680_, v_hlo_681_, v_hhi_682_);
lean_dec(v_hi_679_);
lean_dec(v_n_676_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object* v_n_684_, lean_object* v_lo_685_, lean_object* v_hi_686_, lean_object* v_hhi_687_, lean_object* v_pivot_688_, lean_object* v_as_689_, lean_object* v_i_690_, lean_object* v_k_691_, lean_object* v_ilo_692_, lean_object* v_ik_693_, lean_object* v_w_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_686_, v_pivot_688_, v_as_689_, v_i_690_, v_k_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object* v_n_696_, lean_object* v_lo_697_, lean_object* v_hi_698_, lean_object* v_hhi_699_, lean_object* v_pivot_700_, lean_object* v_as_701_, lean_object* v_i_702_, lean_object* v_k_703_, lean_object* v_ilo_704_, lean_object* v_ik_705_, lean_object* v_w_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_696_, v_lo_697_, v_hi_698_, v_hhi_699_, v_pivot_700_, v_as_701_, v_i_702_, v_k_703_, v_ilo_704_, v_ik_705_, v_w_706_);
lean_dec(v_pivot_700_);
lean_dec(v_hi_698_);
lean_dec(v_lo_697_);
lean_dec(v_n_696_);
return v_res_707_;
}
}
lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT void l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_708_ = stack[0].m_obj;
lean_object* v___y_709_ = stack[1].m_obj;
lean_object* v_res_713_;
v_res_713_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_708_, v___y_709_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_714_, v___y_715_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v_x_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_718_, lean_object* v_x_719_){
_start:
{
lean_inc_ref(v_s_718_);
return v_s_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_720_, lean_object* v_x_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_720_, v_x_721_);
lean_dec(v_x_721_);
lean_dec_ref(v_s_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1));
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_730_, v_x_731_);
lean_dec_ref(v_x_731_);
lean_dec_ref(v_x_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_box(0);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_735_);
lean_dec_ref(v_x_735_);
return v_res_736_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___f_741_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_742_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_743_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_744_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_745_ = lean_box(0);
v___x_746_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_747_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
lean_ctor_set(v___x_747_, 2, v___f_744_);
lean_ctor_set(v___x_747_, 3, v___f_743_);
lean_ctor_set(v___x_747_, 4, v___f_742_);
lean_ctor_set(v___x_747_, 5, v___f_741_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_750_, lean_object* v_msg_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_panic_fn_borrowed(v_env_750_, v_msg_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object* v_env_753_, lean_object* v_msg_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_753_, v_msg_754_);
lean_dec_ref(v_env_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag___lam__0(lean_object* v_ext_756_, lean_object* v_declName_757_, lean_object* v_s_758_){
_start:
{
lean_object* v_addEntryFn_759_; lean_object* v_importedEntries_760_; lean_object* v_state_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_addEntryFn_759_ = lean_ctor_get(v_ext_756_, 3);
lean_inc(v_addEntryFn_759_);
lean_dec_ref(v_ext_756_);
v_importedEntries_760_ = lean_ctor_get(v_s_758_, 0);
v_state_761_ = lean_ctor_get(v_s_758_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_s_758_);
if (v_isSharedCheck_769_ == 0)
{
v___x_763_ = v_s_758_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_state_761_);
lean_inc(v_importedEntries_760_);
lean_dec(v_s_758_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_state_765_; lean_object* v___x_767_; 
v_state_765_ = lean_apply_2(v_addEntryFn_759_, v_state_761_, v_declName_757_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v_state_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_importedEntries_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_state_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_773_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_774_ = lean_unsigned_to_nat(4u);
v___x_775_ = lean_unsigned_to_nat(120u);
v___x_776_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_777_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_778_ = l_mkPanicMessageWithDecl(v___x_777_, v___x_776_, v___x_775_, v___x_774_, v___x_773_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_779_, lean_object* v_env_780_, lean_object* v_declName_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = l_Lean_Name_isAnonymous(v_declName_781_);
if (v___x_782_ == 0)
{
lean_object* v___f_783_; lean_object* v___x_784_; uint8_t v___y_786_; lean_object* v___x_798_; 
lean_inc(v_declName_781_);
lean_inc_ref(v_ext_779_);
v___f_783_ = lean_alloc_closure((void*)(l_Lean_TagDeclarationExtension_tag___lam__0), 3, 2);
lean_closure_set(v___f_783_, 0, v_ext_779_);
lean_closure_set(v___f_783_, 1, v_declName_781_);
v___x_784_ = lean_box(1);
v___x_798_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_780_, v_declName_781_);
if (lean_obj_tag(v___x_798_) == 0)
{
uint8_t v___x_799_; 
v___x_799_ = 1;
v___y_786_ = v___x_799_;
goto v___jp_785_;
}
else
{
lean_dec_ref_known(v___x_798_, 1);
if (v___x_782_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v___f_783_);
lean_dec(v_declName_781_);
lean_dec_ref(v_ext_779_);
v___x_800_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_801_ = lean_panic_fn_borrowed(v_env_780_, v___x_800_);
lean_dec_ref(v_env_780_);
return v___x_801_;
}
else
{
v___y_786_ = v___x_782_;
goto v___jp_785_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_787_ = lean_box(1);
v___x_788_ = lean_box(0);
lean_inc_ref(v_env_780_);
v___x_789_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_784_, v_ext_779_, v_env_780_, v___x_787_, v___x_788_);
v___x_790_ = l_Lean_NameSet_contains(v___x_789_, v_declName_781_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v_toEnvExtension_791_; uint8_t v_logWrites_792_; 
v_toEnvExtension_791_ = lean_ctor_get(v_ext_779_, 0);
lean_inc_ref(v_toEnvExtension_791_);
lean_dec_ref(v_ext_779_);
v_logWrites_792_ = lean_ctor_get_uint8(v_toEnvExtension_791_, sizeof(void*)*6);
if (v_logWrites_792_ == 0)
{
lean_object* v_asyncMode_793_; lean_object* v___x_794_; 
v_asyncMode_793_ = lean_ctor_get(v_toEnvExtension_791_, 2);
lean_inc(v_asyncMode_793_);
v___x_794_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_791_, v_env_780_, v___f_783_, v_asyncMode_793_, v_declName_781_, v___y_786_);
lean_dec(v_asyncMode_793_);
return v___x_794_;
}
else
{
lean_object* v_asyncMode_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_asyncMode_795_ = lean_ctor_get(v_toEnvExtension_791_, 2);
lean_inc(v_asyncMode_795_);
lean_inc(v_declName_781_);
v___x_796_ = l_Lean_Environment_logDeclChange(v_env_780_, v_declName_781_);
v___x_797_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_791_, v___x_796_, v___f_783_, v_asyncMode_795_, v_declName_781_, v___y_786_);
lean_dec(v_asyncMode_795_);
return v___x_797_;
}
}
else
{
lean_dec_ref(v___f_783_);
lean_dec(v_declName_781_);
lean_dec_ref(v_ext_779_);
return v_env_780_;
}
}
}
else
{
lean_dec(v_declName_781_);
lean_dec_ref(v_ext_779_);
return v_env_780_;
}
}
}
uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object* v___y_802_, lean_object* v_as_803_, lean_object* v_k_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_m_809_; lean_object* v_a_810_; uint8_t v___x_811_; 
v___x_807_ = lean_nat_add(v_x_805_, v_x_806_);
v___x_808_ = lean_unsigned_to_nat(1u);
v_m_809_ = lean_nat_shiftr(v___x_807_, v___x_808_);
lean_dec(v___x_807_);
v_a_810_ = lean_array_fget_borrowed(v_as_803_, v_m_809_);
v___x_811_ = l_Lean_Name_quickLt(v_a_810_, v_k_804_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
lean_dec(v_x_806_);
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = l_Lean_Name_quickLt(v_k_804_, v_a_810_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; 
lean_dec(v_m_809_);
lean_dec(v_x_805_);
v___x_814_ = lean_nat_dec_le(v___x_812_, v___y_802_);
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = lean_nat_dec_eq(v_m_809_, v___x_812_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_nat_sub(v_m_809_, v___x_808_);
lean_dec(v_m_809_);
v___x_817_ = lean_nat_dec_lt(v___x_816_, v_x_805_);
if (v___x_817_ == 0)
{
v_x_806_ = v___x_816_;
goto _start;
}
else
{
lean_dec(v___x_816_);
lean_dec(v_x_805_);
return v___x_815_;
}
}
else
{
lean_dec(v_m_809_);
lean_dec(v_x_805_);
return v___x_811_;
}
}
}
else
{
lean_object* v___x_819_; uint8_t v___x_820_; 
lean_dec(v_x_805_);
v___x_819_ = lean_nat_add(v_m_809_, v___x_808_);
lean_dec(v_m_809_);
v___x_820_ = lean_nat_dec_le(v___x_819_, v_x_806_);
if (v___x_820_ == 0)
{
lean_dec(v___x_819_);
lean_dec(v_x_806_);
return v___x_820_;
}
else
{
v_x_805_ = v___x_819_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_802_ = stack[0].m_obj;
lean_object* v_as_803_ = stack[1].m_obj;
lean_object* v_k_804_ = stack[2].m_obj;
lean_object* v_x_805_ = stack[3].m_obj;
lean_object* v_x_806_ = stack[4].m_obj;
uint8_t v_res_822_;
v_res_822_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_802_, v_as_803_, v_k_804_, v_x_805_, v_x_806_);
stack->m_num = v_res_822_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object* v___y_823_, lean_object* v_as_824_, lean_object* v_k_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_823_, v_as_824_, v_k_825_, v_x_826_, v_x_827_);
lean_dec(v_k_825_);
lean_dec_ref(v_as_824_);
lean_dec(v___y_823_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_833_, lean_object* v_env_834_, lean_object* v_declName_835_, lean_object* v_asyncMode_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_box(1);
v___x_838_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_834_, v_declName_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; uint8_t v___x_840_; 
lean_inc(v_declName_835_);
v___x_839_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_837_, v_ext_833_, v_env_834_, v_asyncMode_836_, v_declName_835_);
v___x_840_ = l_Lean_NameSet_contains(v___x_839_, v_declName_835_);
lean_dec(v_declName_835_);
lean_dec(v___x_839_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_val_841_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_838_, 1);
v___x_842_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_843_ = 0;
v___x_844_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_842_, v_ext_833_, v_env_834_, v_val_841_, v___x_843_);
lean_dec(v_val_841_);
lean_dec_ref(v_env_834_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_array_get_size(v___x_844_);
v___x_847_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec_ref(v___x_844_);
lean_dec(v_declName_835_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_sub(v___x_846_, v___x_848_);
v___x_850_ = lean_nat_dec_le(v___x_845_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec(v___x_849_);
lean_dec_ref(v___x_844_);
lean_dec(v_declName_835_);
return v___x_850_;
}
else
{
uint8_t v___x_851_; 
lean_inc(v___x_849_);
v___x_851_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_849_, v___x_844_, v_declName_835_, v___x_845_, v___x_849_);
lean_dec(v_declName_835_);
lean_dec_ref(v___x_844_);
lean_dec(v___x_849_);
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_TagDeclarationExtension_isTagged_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_833_ = stack[0].m_obj;
lean_object* v_env_834_ = stack[1].m_obj;
lean_object* v_declName_835_ = stack[2].m_obj;
lean_object* v_asyncMode_836_ = stack[3].m_obj;
uint8_t v_res_852_;
v_res_852_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_833_, v_env_834_, v_declName_835_, v_asyncMode_836_);
stack->m_num = v_res_852_;
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_853_, lean_object* v_env_854_, lean_object* v_declName_855_, lean_object* v_asyncMode_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_853_, v_env_854_, v_declName_855_, v_asyncMode_856_);
lean_dec(v_asyncMode_856_);
lean_dec_ref(v_ext_853_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object* v___y_859_, lean_object* v_as_860_, lean_object* v_k_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_859_, v_as_860_, v_k_861_, v_x_862_, v_x_863_);
return v___x_865_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_859_ = stack[0].m_obj;
lean_object* v_as_860_ = stack[1].m_obj;
lean_object* v_k_861_ = stack[2].m_obj;
lean_object* v_x_862_ = stack[3].m_obj;
lean_object* v_x_863_ = stack[4].m_obj;
uint8_t v_res_866_;
v_res_866_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v___y_859_, v_as_860_, v_k_861_, v_x_862_, v_x_863_, lean_box(0));
stack->m_num = v_res_866_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object* v___y_867_, lean_object* v_as_868_, lean_object* v_k_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v___y_867_, v_as_868_, v_k_869_, v_x_870_, v_x_871_, v_x_872_);
lean_dec(v_k_869_);
lean_dec_ref(v_as_868_);
lean_dec(v___y_867_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(lean_object* v_x_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_875_ = stack[0].m_obj;
lean_object* v___y_876_ = stack[1].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(v_x_875_, v___y_876_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed(lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(v_x_881_, v___y_882_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v_x_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(lean_object* v_s_885_, lean_object* v_x_886_){
_start:
{
lean_inc(v_s_885_);
return v_s_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed(lean_object* v_s_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(v_s_887_, v_x_888_);
lean_dec_ref(v_x_888_);
lean_dec(v_s_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1));
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(v_x_897_, v_x_898_);
lean_dec(v_x_898_);
lean_dec_ref(v_x_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(lean_object* v_x_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_box(0);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed(lean_object* v_x_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(v_x_902_);
lean_dec(v_x_902_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___f_908_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_909_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2));
v___f_910_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1));
v___f_911_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0));
v___x_912_ = lean_box(0);
v___x_913_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_914_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_912_);
lean_ctor_set(v___x_914_, 2, v___f_911_);
lean_ctor_set(v___x_914_, 3, v___f_910_);
lean_ctor_set(v___x_914_, 4, v___f_909_);
lean_ctor_set(v___x_914_, 5, v___f_908_);
return v___x_914_;
}
}
lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg(){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4);
return v___x_916_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedMapDeclarationExtension_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_917_;
v_res_917_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
stack->m_obj
 = v_res_917_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___boxed(lean_object* v___dummy_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v_res_919_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0(void){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_00_u03b1_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_922_;
}
}
lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg(){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_924_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedMapDeclarationExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_925_;
v_res_925_ = l_Lean_instInhabitedMapDeclarationExtension___redArg();
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg___boxed(lean_object* v___dummy_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_instInhabitedMapDeclarationExtension___redArg();
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_931_, lean_object* v_x_932_){
_start:
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_935_; 
v_fst_933_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_fst_933_);
v_snd_934_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_snd_934_);
lean_dec_ref(v_x_932_);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_933_, v_snd_934_, v_s_931_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_936_, lean_object* v_env_937_, lean_object* v_s_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_apply_2(v_exportEntriesFn_936_, v_env_937_, v_s_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
return v_x_941_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v___x_945_; 
v_head_943_ = lean_ctor_get(v_x_942_, 0);
lean_inc(v_head_943_);
v_tail_944_ = lean_ctor_get(v_x_942_, 1);
lean_inc(v_tail_944_);
lean_dec_ref_known(v_x_942_, 2);
v___x_945_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_940_, v_head_943_);
if (lean_obj_tag(v___x_945_) == 1)
{
lean_object* v_val_946_; lean_object* v___x_947_; 
v_val_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_943_, v_val_946_, v_x_941_);
v_x_941_ = v___x_947_;
v_x_942_ = v_tail_944_;
goto _start;
}
else
{
lean_dec(v___x_945_);
lean_dec(v_head_943_);
v_x_942_ = v_tail_944_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_950_, v_x_951_, v_x_952_);
lean_dec(v_newState_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_954_, lean_object* v_newState_955_, lean_object* v_newConsts_956_, lean_object* v_s_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_955_, v_s_957_, v_newConsts_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_959_, lean_object* v_newState_960_, lean_object* v_newConsts_961_, lean_object* v_s_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_959_, v_newState_960_, v_newConsts_961_, v_s_962_);
lean_dec(v_newState_960_);
lean_dec(v_x_959_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0));
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_966_);
lean_dec(v_x_966_);
return v_res_967_;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
return v___x_970_;
}
}
LEAN_EXPORT void l_Lean_mkMapDeclarationExtension___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_968_ = stack[0].m_obj;
lean_object* v_res_971_;
v_res_971_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_968_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_972_);
return v_res_974_;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_975_, lean_object* v_x_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_975_);
return v___x_979_;
}
}
LEAN_EXPORT void l_Lean_mkMapDeclarationExtension___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_975_ = stack[0].m_obj;
lean_object* v_x_976_ = stack[1].m_obj;
lean_object* v___y_977_ = stack[2].m_obj;
lean_object* v_res_980_;
v_res_980_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_975_, v_x_976_, v___y_977_);
stack->m_obj
 = v_res_980_;
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_981_, v_x_982_, v___y_983_);
lean_dec_ref(v___y_983_);
lean_dec_ref(v_x_982_);
return v_res_985_;
}
}
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_995_, lean_object* v_asyncMode_996_, uint8_t v_logWrites_997_, lean_object* v_exportEntriesFn_998_){
_start:
{
lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___f_1000_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1001_, 0, v_exportEntriesFn_998_);
v___f_1002_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_1003_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_1004_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_1005_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_1006_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_1007_ = 0;
v___x_1008_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1008_, 0, v_name_995_);
lean_ctor_set(v___x_1008_, 1, v___f_1004_);
lean_ctor_set(v___x_1008_, 2, v___f_1005_);
lean_ctor_set(v___x_1008_, 3, v___f_1000_);
lean_ctor_set(v___x_1008_, 4, v___f_1001_);
lean_ctor_set(v___x_1008_, 5, v___f_1002_);
lean_ctor_set(v___x_1008_, 6, v_asyncMode_996_);
lean_ctor_set(v___x_1008_, 7, v___x_1006_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*8, v___x_1007_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*8 + 1, v_logWrites_997_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___f_1003_);
v___x_1010_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1009_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1010_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1010_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkMapDeclarationExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_995_ = stack[0].m_obj;
lean_object* v_asyncMode_996_ = stack[1].m_obj;
uint8_t v_logWrites_997_ = stack[2].m_num;
lean_object* v_exportEntriesFn_998_ = stack[3].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_995_, v_asyncMode_996_, v_logWrites_997_, v_exportEntriesFn_998_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_1028_, lean_object* v_asyncMode_1029_, lean_object* v_logWrites_1030_, lean_object* v_exportEntriesFn_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v_logWrites_boxed_1033_; lean_object* v_res_1034_; 
v_logWrites_boxed_1033_ = lean_unbox(v_logWrites_1030_);
v_res_1034_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1028_, v_asyncMode_1029_, v_logWrites_boxed_1033_, v_exportEntriesFn_1031_);
return v_res_1034_;
}
}
lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_1035_, lean_object* v_name_1036_, lean_object* v_asyncMode_1037_, uint8_t v_logWrites_1038_, lean_object* v_exportEntriesFn_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1036_, v_asyncMode_1037_, v_logWrites_1038_, v_exportEntriesFn_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT void l_Lean_mkMapDeclarationExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1036_ = stack[1].m_obj;
lean_object* v_asyncMode_1037_ = stack[2].m_obj;
uint8_t v_logWrites_1038_ = stack[3].m_num;
lean_object* v_exportEntriesFn_1039_ = stack[4].m_obj;
lean_object* v_res_1042_;
v_res_1042_ = l_Lean_mkMapDeclarationExtension(lean_box(0), v_name_1036_, v_asyncMode_1037_, v_logWrites_1038_, v_exportEntriesFn_1039_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_name_1044_, lean_object* v_asyncMode_1045_, lean_object* v_logWrites_1046_, lean_object* v_exportEntriesFn_1047_, lean_object* v_a_1048_){
_start:
{
uint8_t v_logWrites_boxed_1049_; lean_object* v_res_1050_; 
v_logWrites_boxed_1049_ = lean_unbox(v_logWrites_1046_);
v_res_1050_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_1043_, v_name_1044_, v_asyncMode_1045_, v_logWrites_boxed_1049_, v_exportEntriesFn_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_1051_, lean_object* v_newState_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_1052_, v_x_1053_, v_x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_1056_, lean_object* v_newState_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_1056_, v_newState_1057_, v_x_1058_, v_x_1059_);
lean_dec(v_newState_1057_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___lam__0(lean_object* v_addEntryFn_1061_, lean_object* v___x_1062_, lean_object* v_s_1063_){
_start:
{
lean_object* v_importedEntries_1064_; lean_object* v_state_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
v_importedEntries_1064_ = lean_ctor_get(v_s_1063_, 0);
v_state_1065_ = lean_ctor_get(v_s_1063_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_s_1063_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1067_ = v_s_1063_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_state_1065_);
lean_inc(v_importedEntries_1064_);
lean_dec(v_s_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_state_1069_; lean_object* v___x_1071_; 
v_state_1069_ = lean_apply_2(v_addEntryFn_1061_, v_state_1065_, v___x_1062_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v_state_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_importedEntries_1064_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_state_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_1080_, lean_object* v_env_1081_, lean_object* v_declName_1082_, lean_object* v_val_1083_, uint8_t v_allowOverwrite_1084_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1081_, v_declName_1082_);
if (lean_obj_tag(v___x_1096_) == 1)
{
lean_object* v_val_1097_; lean_object* v_name_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_val_1083_);
v_val_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v_name_1098_ = lean_ctor_get(v_ext_1080_, 1);
lean_inc(v_name_1098_);
lean_dec_ref(v_ext_1080_);
v___x_1099_ = lean_box(0);
v___x_1100_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1101_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1102_ = lean_unsigned_to_nat(179u);
v___x_1103_ = lean_unsigned_to_nat(4u);
v___x_1104_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1105_ = 1;
v___x_1106_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1082_, v___x_1105_);
v___x_1107_ = lean_string_append(v___x_1104_, v___x_1106_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1109_ = lean_string_append(v___x_1107_, v___x_1108_);
v___x_1110_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1098_, v___x_1105_);
v___x_1111_ = lean_string_append(v___x_1109_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
v___x_1114_ = l_Lean_Environment_allImportedModuleNames(v_env_1081_);
v___x_1115_ = lean_array_get(v___x_1099_, v___x_1114_, v_val_1097_);
lean_dec(v_val_1097_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1115_, v___x_1105_);
v___x_1117_ = lean_string_append(v___x_1113_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
v___x_1120_ = l_mkPanicMessageWithDecl(v___x_1100_, v___x_1101_, v___x_1102_, v___x_1103_, v___x_1119_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = lean_panic_fn_borrowed(v_env_1081_, v___x_1120_);
lean_dec_ref(v_env_1081_);
return v___x_1121_;
}
else
{
lean_dec(v___x_1096_);
if (v_allowOverwrite_1084_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1122_ = lean_box(1);
v___x_1123_ = lean_box(1);
v___x_1124_ = lean_box(0);
lean_inc_ref(v_env_1081_);
v___x_1125_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1122_, v_ext_1080_, v_env_1081_, v___x_1123_, v___x_1124_, v_allowOverwrite_1084_);
v___x_1126_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1082_, v___x_1125_);
lean_dec(v___x_1125_);
if (v___x_1126_ == 0)
{
goto v___jp_1085_;
}
else
{
lean_object* v_name_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v_val_1083_);
v_name_1127_ = lean_ctor_get(v_ext_1080_, 1);
lean_inc(v_name_1127_);
lean_dec_ref(v_ext_1080_);
v___x_1128_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1129_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1130_ = lean_unsigned_to_nat(186u);
v___x_1131_ = lean_unsigned_to_nat(4u);
v___x_1132_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1133_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1082_, v___x_1126_);
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1136_ = lean_string_append(v___x_1134_, v___x_1135_);
v___x_1137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1127_, v___x_1126_);
v___x_1138_ = lean_string_append(v___x_1136_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__5));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___x_1141_ = l_mkPanicMessageWithDecl(v___x_1128_, v___x_1129_, v___x_1130_, v___x_1131_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = lean_panic_fn_borrowed(v_env_1081_, v___x_1141_);
lean_dec_ref(v_env_1081_);
return v___x_1142_;
}
}
else
{
goto v___jp_1085_;
}
}
v___jp_1085_:
{
lean_object* v_toEnvExtension_1086_; lean_object* v_addEntryFn_1087_; lean_object* v_asyncMode_1088_; uint8_t v_logWrites_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; uint8_t v___x_1092_; 
v_toEnvExtension_1086_ = lean_ctor_get(v_ext_1080_, 0);
lean_inc_ref(v_toEnvExtension_1086_);
v_addEntryFn_1087_ = lean_ctor_get(v_ext_1080_, 3);
lean_inc(v_addEntryFn_1087_);
lean_dec_ref(v_ext_1080_);
v_asyncMode_1088_ = lean_ctor_get(v_toEnvExtension_1086_, 2);
lean_inc(v_asyncMode_1088_);
v_logWrites_1089_ = lean_ctor_get_uint8(v_toEnvExtension_1086_, sizeof(void*)*6);
lean_inc(v_declName_1082_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_declName_1082_);
lean_ctor_set(v___x_1090_, 1, v_val_1083_);
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_insert___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1091_, 0, v_addEntryFn_1087_);
lean_closure_set(v___f_1091_, 1, v___x_1090_);
v___x_1092_ = 1;
if (v_logWrites_1089_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1086_, v_env_1081_, v___f_1091_, v_asyncMode_1088_, v_declName_1082_, v___x_1092_);
lean_dec(v_asyncMode_1088_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_inc(v_declName_1082_);
v___x_1094_ = l_Lean_Environment_logDeclChange(v_env_1081_, v_declName_1082_);
v___x_1095_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1086_, v___x_1094_, v___f_1091_, v_asyncMode_1088_, v_declName_1082_, v___x_1092_);
lean_dec(v_asyncMode_1088_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_insert___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1080_ = stack[0].m_obj;
lean_object* v_env_1081_ = stack[1].m_obj;
lean_object* v_declName_1082_ = stack[2].m_obj;
lean_object* v_val_1083_ = stack[3].m_obj;
uint8_t v_allowOverwrite_1084_ = stack[4].m_num;
lean_object* v_res_1143_;
v_res_1143_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1080_, v_env_1081_, v_declName_1082_, v_val_1083_, v_allowOverwrite_1084_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___boxed(lean_object* v_ext_1144_, lean_object* v_env_1145_, lean_object* v_declName_1146_, lean_object* v_val_1147_, lean_object* v_allowOverwrite_1148_){
_start:
{
uint8_t v_allowOverwrite_boxed_1149_; lean_object* v_res_1150_; 
v_allowOverwrite_boxed_1149_ = lean_unbox(v_allowOverwrite_1148_);
v_res_1150_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1144_, v_env_1145_, v_declName_1146_, v_val_1147_, v_allowOverwrite_boxed_1149_);
return v_res_1150_;
}
}
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_1151_, lean_object* v_ext_1152_, lean_object* v_env_1153_, lean_object* v_declName_1154_, lean_object* v_val_1155_, uint8_t v_allowOverwrite_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1152_, v_env_1153_, v_declName_1154_, v_val_1155_, v_allowOverwrite_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_insert_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1152_ = stack[1].m_obj;
lean_object* v_env_1153_ = stack[2].m_obj;
lean_object* v_declName_1154_ = stack[3].m_obj;
lean_object* v_val_1155_ = stack[4].m_obj;
uint8_t v_allowOverwrite_1156_ = stack[5].m_num;
lean_object* v_res_1158_;
v_res_1158_ = l_Lean_MapDeclarationExtension_insert(lean_box(0), v_ext_1152_, v_env_1153_, v_declName_1154_, v_val_1155_, v_allowOverwrite_1156_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_ext_1160_, lean_object* v_env_1161_, lean_object* v_declName_1162_, lean_object* v_val_1163_, lean_object* v_allowOverwrite_1164_){
_start:
{
uint8_t v_allowOverwrite_boxed_1165_; lean_object* v_res_1166_; 
v_allowOverwrite_boxed_1165_ = lean_unbox(v_allowOverwrite_1164_);
v_res_1166_ = l_Lean_MapDeclarationExtension_insert(v_00_u03b1_1159_, v_ext_1160_, v_env_1161_, v_declName_1162_, v_val_1163_, v_allowOverwrite_boxed_1165_);
return v_res_1166_;
}
}
uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_fst_1169_; lean_object* v_fst_1170_; uint8_t v___x_1171_; 
v_fst_1169_ = lean_ctor_get(v_a_1167_, 0);
v_fst_1170_ = lean_ctor_get(v_b_1168_, 0);
v___x_1171_ = l_Lean_Name_quickLt(v_fst_1169_, v_fst_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1167_ = stack[0].m_obj;
lean_object* v_b_1168_ = stack[1].m_obj;
uint8_t v_res_1172_;
v_res_1172_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_1167_, v_b_1168_);
stack->m_num = v_res_1172_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object* v_a_1173_, lean_object* v_b_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_1173_, v_b_1174_);
lean_dec_ref(v_b_1174_);
lean_dec_ref(v_a_1173_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_inst_1179_, lean_object* v_ext_1180_, lean_object* v_env_1181_, lean_object* v_declName_1182_, lean_object* v_asyncMode_1183_, uint8_t v_level_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_box(1);
v___x_1186_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1181_, v_declName_1182_);
if (lean_obj_tag(v___x_1186_) == 0)
{
uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v_inst_1179_);
v___x_1187_ = 0;
lean_inc(v_declName_1182_);
v___x_1188_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1185_, v_ext_1180_, v_env_1181_, v_asyncMode_1183_, v_declName_1182_, v___x_1187_);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1188_, v_declName_1182_);
lean_dec(v_declName_1182_);
lean_dec(v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v_val_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_val_1190_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1191_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1185_, v_ext_1180_, v_env_1181_, v_val_1190_, v_level_1184_);
lean_dec(v_val_1190_);
lean_dec_ref(v_env_1181_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_array_get_size(v___x_1191_);
v___x_1194_ = lean_nat_dec_lt(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v___x_1191_);
lean_dec(v_declName_1182_);
lean_dec(v_inst_1179_);
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_sub(v___x_1193_, v___x_1196_);
v___x_1198_ = lean_nat_dec_le(v___x_1192_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v___x_1197_);
lean_dec_ref(v___x_1191_);
lean_dec(v_declName_1182_);
lean_dec(v_inst_1179_);
v___x_1199_ = lean_box(0);
return v___x_1199_;
}
else
{
lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___f_1200_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_declName_1182_);
lean_ctor_set(v___x_1201_, 1, v_inst_1179_);
v___x_1202_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1));
v___x_1203_ = l_Array_binSearchAux___redArg(v___f_1200_, v___x_1202_, v___x_1191_, v___x_1201_, v___x_1192_, v___x_1197_);
lean_dec_ref(v___x_1191_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_val_1205_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1207_ = v___x_1203_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_val_1205_);
lean_dec(v___x_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_snd_1209_; lean_object* v___x_1211_; 
v_snd_1209_ = lean_ctor_get(v_val_1205_, 1);
lean_inc(v_snd_1209_);
lean_dec(v_val_1205_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v_snd_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_snd_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_find_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1179_ = stack[0].m_obj;
lean_object* v_ext_1180_ = stack[1].m_obj;
lean_object* v_env_1181_ = stack[2].m_obj;
lean_object* v_declName_1182_ = stack[3].m_obj;
lean_object* v_asyncMode_1183_ = stack[4].m_obj;
uint8_t v_level_1184_ = stack[5].m_num;
lean_object* v_res_1214_;
v_res_1214_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1179_, v_ext_1180_, v_env_1181_, v_declName_1182_, v_asyncMode_1183_, v_level_1184_);
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_inst_1215_, lean_object* v_ext_1216_, lean_object* v_env_1217_, lean_object* v_declName_1218_, lean_object* v_asyncMode_1219_, lean_object* v_level_1220_){
_start:
{
uint8_t v_level_boxed_1221_; lean_object* v_res_1222_; 
v_level_boxed_1221_ = lean_unbox(v_level_1220_);
v_res_1222_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1215_, v_ext_1216_, v_env_1217_, v_declName_1218_, v_asyncMode_1219_, v_level_boxed_1221_);
lean_dec(v_asyncMode_1219_);
lean_dec_ref(v_ext_1216_);
return v_res_1222_;
}
}
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1223_, lean_object* v_inst_1224_, lean_object* v_ext_1225_, lean_object* v_env_1226_, lean_object* v_declName_1227_, lean_object* v_asyncMode_1228_, uint8_t v_level_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1224_, v_ext_1225_, v_env_1226_, v_declName_1227_, v_asyncMode_1228_, v_level_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_find_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1224_ = stack[1].m_obj;
lean_object* v_ext_1225_ = stack[2].m_obj;
lean_object* v_env_1226_ = stack[3].m_obj;
lean_object* v_declName_1227_ = stack[4].m_obj;
lean_object* v_asyncMode_1228_ = stack[5].m_obj;
uint8_t v_level_1229_ = stack[6].m_num;
lean_object* v_res_1231_;
v_res_1231_ = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), v_inst_1224_, v_ext_1225_, v_env_1226_, v_declName_1227_, v_asyncMode_1228_, v_level_1229_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_inst_1233_, lean_object* v_ext_1234_, lean_object* v_env_1235_, lean_object* v_declName_1236_, lean_object* v_asyncMode_1237_, lean_object* v_level_1238_){
_start:
{
uint8_t v_level_boxed_1239_; lean_object* v_res_1240_; 
v_level_boxed_1239_ = lean_unbox(v_level_1238_);
v_res_1240_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1232_, v_inst_1233_, v_ext_1234_, v_env_1235_, v_declName_1236_, v_asyncMode_1237_, v_level_boxed_1239_);
lean_dec(v_asyncMode_1237_);
lean_dec_ref(v_ext_1234_);
return v_res_1240_;
}
}
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_inst_1242_, lean_object* v_ext_1243_, lean_object* v_env_1244_, lean_object* v_declName_1245_, lean_object* v_asyncMode_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_box(1);
v___x_1248_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1244_, v_declName_1245_);
if (lean_obj_tag(v___x_1248_) == 0)
{
uint8_t v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_dec(v_inst_1242_);
v___x_1249_ = 0;
lean_inc(v_declName_1245_);
v___x_1250_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1247_, v_ext_1243_, v_env_1244_, v_asyncMode_1246_, v_declName_1245_, v___x_1249_);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1245_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v_declName_1245_);
return v___x_1251_;
}
else
{
lean_object* v_val_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_val_1252_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1252_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1253_ = 0;
v___x_1254_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1247_, v_ext_1243_, v_env_1244_, v_val_1252_, v___x_1253_);
lean_dec(v_val_1252_);
lean_dec_ref(v_env_1244_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_array_get_size(v___x_1254_);
v___x_1257_ = lean_nat_dec_lt(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_dec_ref(v___x_1254_);
lean_dec(v_declName_1245_);
lean_dec(v_inst_1242_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_sub(v___x_1256_, v___x_1258_);
v___x_1260_ = lean_nat_dec_le(v___x_1255_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_dec(v___x_1259_);
lean_dec_ref(v___x_1254_);
lean_dec(v_declName_1245_);
lean_dec(v_inst_1242_);
return v___x_1260_;
}
else
{
lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___f_1261_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_declName_1245_);
lean_ctor_set(v___x_1262_, 1, v_inst_1242_);
v___x_1263_ = ((lean_object*)(l_Lean_MapDeclarationExtension_contains___redArg___closed__0));
v___x_1264_ = l_Array_binSearchAux___redArg(v___f_1261_, v___x_1263_, v___x_1254_, v___x_1262_, v___x_1255_, v___x_1259_);
lean_dec_ref(v___x_1254_);
v___x_1265_ = lean_unbox(v___x_1264_);
lean_dec(v___x_1264_);
return v___x_1265_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1242_ = stack[0].m_obj;
lean_object* v_ext_1243_ = stack[1].m_obj;
lean_object* v_env_1244_ = stack[2].m_obj;
lean_object* v_declName_1245_ = stack[3].m_obj;
lean_object* v_asyncMode_1246_ = stack[4].m_obj;
uint8_t v_res_1266_;
v_res_1266_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1242_, v_ext_1243_, v_env_1244_, v_declName_1245_, v_asyncMode_1246_);
stack->m_num = v_res_1266_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_inst_1267_, lean_object* v_ext_1268_, lean_object* v_env_1269_, lean_object* v_declName_1270_, lean_object* v_asyncMode_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1267_, v_ext_1268_, v_env_1269_, v_declName_1270_, v_asyncMode_1271_);
lean_dec(v_asyncMode_1271_);
lean_dec_ref(v_ext_1268_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1274_, lean_object* v_inst_1275_, lean_object* v_ext_1276_, lean_object* v_env_1277_, lean_object* v_declName_1278_, lean_object* v_asyncMode_1279_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1275_, v_ext_1276_, v_env_1277_, v_declName_1278_, v_asyncMode_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT void l_Lean_MapDeclarationExtension_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1275_ = stack[1].m_obj;
lean_object* v_ext_1276_ = stack[2].m_obj;
lean_object* v_env_1277_ = stack[3].m_obj;
lean_object* v_declName_1278_ = stack[4].m_obj;
lean_object* v_asyncMode_1279_ = stack[5].m_obj;
uint8_t v_res_1281_;
v_res_1281_ = l_Lean_MapDeclarationExtension_contains(lean_box(0), v_inst_1275_, v_ext_1276_, v_env_1277_, v_declName_1278_, v_asyncMode_1279_);
stack->m_num = v_res_1281_;
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_inst_1283_, lean_object* v_ext_1284_, lean_object* v_env_1285_, lean_object* v_declName_1286_, lean_object* v_asyncMode_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1282_, v_inst_1283_, v_ext_1284_, v_env_1285_, v_declName_1286_, v_asyncMode_1287_);
lean_dec(v_asyncMode_1287_);
lean_dec_ref(v_ext_1284_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
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
