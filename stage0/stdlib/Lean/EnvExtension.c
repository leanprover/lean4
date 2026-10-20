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
size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; 
v___x_31_ = ((size_t)0ULL);
v___x_32_ = lean_usize_of_nat(v___x_28_);
v___x_33_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_29_, v___f_24_, v_x2_26_, v___x_31_, v___x_32_, v_x1_25_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___redArg(lean_object* v_addEntryFn_34_, lean_object* v_initState_35_, lean_object* v_as_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_array_get_size(v_as_36_);
v___x_39_ = ((lean_object*)(l_Lean_mkStateFromImportedEntries___redArg___lam__1___closed__9));
v___x_40_ = lean_nat_dec_lt(v___x_37_, v___x_38_);
if (v___x_40_ == 0)
{
lean_dec_ref(v_as_36_);
lean_dec(v_addEntryFn_34_);
return v_initState_35_;
}
else
{
lean_object* v___f_41_; lean_object* v___f_42_; size_t v___x_43_; size_t v___x_44_; lean_object* v___x_45_; 
v___f_41_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___redArg___lam__0), 3, 1);
lean_closure_set(v___f_41_, 0, v_addEntryFn_34_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___redArg___lam__1), 3, 1);
lean_closure_set(v___f_42_, 0, v___f_41_);
v___x_43_ = ((size_t)0ULL);
v___x_44_ = lean_usize_of_nat(v___x_38_);
v___x_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_39_, v___f_42_, v_as_36_, v___x_43_, v___x_44_, v_initState_35_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries(lean_object* v_00_u03b1_46_, lean_object* v_00_u03c3_47_, lean_object* v_addEntryFn_48_, lean_object* v_initState_49_, lean_object* v_as_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_mkStateFromImportedEntries___redArg(v_addEntryFn_48_, v_initState_49_, v_as_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__10));
v___x_79_ = l_Lean_mkAtom(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__12);
v___x_81_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__17));
v___x_92_ = l_Lean_mkAtom(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__18);
v___x_94_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_95_ = lean_array_push(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__19);
v___x_97_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__16));
v___x_98_ = lean_box(2);
v___x_99_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
lean_ctor_set(v___x_99_, 2, v___x_96_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__20);
v___x_101_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__13);
v___x_102_ = lean_array_push(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__21);
v___x_104_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__11));
v___x_105_ = lean_box(2);
v___x_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__22);
v___x_108_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_109_ = lean_array_push(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__23);
v___x_111_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__9));
v___x_112_ = lean_box(2);
v___x_113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
lean_ctor_set(v___x_113_, 2, v___x_110_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__24);
v___x_115_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_116_ = lean_array_push(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__25);
v___x_118_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__7));
v___x_119_ = lean_box(2);
v___x_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__26);
v___x_122_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__5));
v___x_123_ = lean_array_push(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_124_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__27);
v___x_125_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__4));
v___x_126_ = lean_box(2);
v___x_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_124_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(lean_object* v_addEntryFn_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_dec(v_addEntryFn_129_);
return v_x_130_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_134_; 
v_head_132_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_head_132_);
v_tail_133_ = lean_ctor_get(v_x_131_, 1);
lean_inc(v_tail_133_);
lean_dec_ref_known(v_x_131_, 2);
lean_inc(v_addEntryFn_129_);
v___x_134_ = lean_apply_2(v_addEntryFn_129_, v_x_130_, v_head_132_);
v_x_130_ = v___x_134_;
v_x_131_ = v_tail_133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(lean_object* v___x_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
if (lean_obj_tag(v_a_137_) == 0)
{
lean_object* v___x_139_; 
lean_dec_ref(v___x_136_);
v___x_139_ = l_List_reverse___redArg(v_a_138_);
return v___x_139_;
}
else
{
lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_152_; 
v_head_140_ = lean_ctor_get(v_a_137_, 0);
v_tail_141_ = lean_ctor_get(v_a_137_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_a_137_);
if (v_isSharedCheck_152_ == 0)
{
v___x_143_ = v_a_137_;
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_tail_141_);
lean_inc(v_head_140_);
lean_dec(v_a_137_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
lean_inc_ref(v___x_136_);
lean_inc(v_head_140_);
v___x_145_ = lean_apply_1(v___x_136_, v_head_140_);
v___x_146_ = lean_unbox(v___x_145_);
if (v___x_146_ == 0)
{
lean_del_object(v___x_143_);
lean_dec(v_head_140_);
v_a_137_ = v_tail_141_;
goto _start;
}
else
{
lean_object* v___x_149_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v_a_138_);
v___x_149_ = v___x_143_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_head_140_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_a_138_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v_a_137_ = v_tail_141_;
v_a_138_ = v___x_149_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(lean_object* v_p_153_, lean_object* v_addEntryFn_154_, lean_object* v_newEntries_155_, lean_object* v_s_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_newEntries_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc(v_s_156_);
v___x_157_ = lean_apply_1(v_p_153_, v_s_156_);
v___x_158_ = lean_box(0);
v_newEntries_159_ = l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(v___x_157_, v_newEntries_155_, v___x_158_);
lean_inc(v_newEntries_159_);
v___x_160_ = l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(v_addEntryFn_154_, v_s_156_, v_newEntries_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_newEntries_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter(lean_object* v_00_u03c3_162_, lean_object* v_00_u03b1_163_, lean_object* v_p_164_, lean_object* v_addEntryFn_165_, lean_object* v_newEntries_166_, lean_object* v_x_167_, lean_object* v_s_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_SimplePersistentEnvExtension_replayOfFilter___redArg(v_p_164_, v_addEntryFn_165_, v_newEntries_166_, v_s_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object* v_00_u03c3_170_, lean_object* v_00_u03b1_171_, lean_object* v_p_172_, lean_object* v_addEntryFn_173_, lean_object* v_newEntries_174_, lean_object* v_x_175_, lean_object* v_s_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_SimplePersistentEnvExtension_replayOfFilter(v_00_u03c3_170_, v_00_u03b1_171_, v_p_172_, v_addEntryFn_173_, v_newEntries_174_, v_x_175_, v_s_176_);
lean_dec(v_x_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0(lean_object* v_00_u03b1_178_, lean_object* v___x_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_List_filterTR_loop___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__0___redArg(v___x_179_, v_a_180_, v_a_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1(lean_object* v_00_u03c3_183_, lean_object* v_00_u03b1_184_, lean_object* v_addEntryFn_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_List_foldl___at___00Lean_SimplePersistentEnvExtension_replayOfFilter_spec__1___redArg(v_addEntryFn_185_, v_x_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0(lean_object* v_addEntryFn_189_, lean_object* v_s_190_, lean_object* v_e_191_){
_start:
{
lean_object* v_fst_192_; lean_object* v_snd_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_202_; 
v_fst_192_ = lean_ctor_get(v_s_190_, 0);
v_snd_193_ = lean_ctor_get(v_s_190_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_s_190_);
if (v_isSharedCheck_202_ == 0)
{
v___x_195_ = v_s_190_;
v_isShared_196_ = v_isSharedCheck_202_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_snd_193_);
lean_inc(v_fst_192_);
lean_dec(v_s_190_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_202_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
lean_inc(v_e_191_);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v_e_191_);
lean_ctor_set(v___x_197_, 1, v_fst_192_);
v___x_198_ = lean_apply_2(v_addEntryFn_189_, v_snd_193_, v_e_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___x_198_);
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_200_ = v___x_195_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1(lean_object* v_exportEntriesFnEx_x3f_203_, lean_object* v_toArrayFn_204_, lean_object* v_env_205_, lean_object* v_s_206_){
_start:
{
if (lean_obj_tag(v_exportEntriesFnEx_x3f_203_) == 0)
{
lean_object* v_fst_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v_env_205_);
v_fst_207_ = lean_ctor_get(v_s_206_, 0);
lean_inc(v_fst_207_);
lean_dec_ref(v_s_206_);
v___x_208_ = l_List_reverse___redArg(v_fst_207_);
v___x_209_ = lean_apply_1(v_toArrayFn_204_, v___x_208_);
lean_inc_ref_n(v___x_209_, 2);
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_ctor_set(v___x_210_, 2, v___x_209_);
return v___x_210_;
}
else
{
lean_object* v_val_211_; lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v_toArrayFn_204_);
v_val_211_ = lean_ctor_get(v_exportEntriesFnEx_x3f_203_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v_exportEntriesFnEx_x3f_203_, 1);
v_fst_212_ = lean_ctor_get(v_s_206_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v_s_206_, 1);
lean_inc(v_snd_213_);
lean_dec_ref(v_s_206_);
v___x_214_ = l_List_reverse___redArg(v_fst_212_);
v___x_215_ = lean_apply_3(v_val_211_, v_env_205_, v_snd_213_, v___x_214_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2(lean_object* v_s_219_){
_start:
{
lean_object* v_fst_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_231_; 
v_fst_220_ = lean_ctor_get(v_s_219_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_s_219_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_s_219_, 1);
lean_dec(v_unused_232_);
v___x_222_ = v_s_219_;
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_fst_220_);
lean_dec(v_s_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__2___closed__1));
v___x_225_ = l_List_lengthTR___redArg(v_fst_220_);
lean_dec(v_fst_220_);
v___x_226_ = l_Nat_reprFast(v___x_225_);
v___x_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 5);
lean_ctor_set(v___x_222_, 1, v___x_227_);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___closed__0));
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3___boxed(lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__3(v_x_237_);
lean_dec_ref(v_x_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(lean_object* v_addImportedFn_239_, lean_object* v___x_240_, lean_object* v_as_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_apply_1(v_addImportedFn_239_, v_as_241_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_240_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed(lean_object* v_addImportedFn_247_, lean_object* v___x_248_, lean_object* v_as_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4(v_addImportedFn_247_, v___x_248_, v_as_249_, v___y_250_);
lean_dec_ref(v___y_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(lean_object* v_val_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v_fst_262_; lean_object* v_newEntries_263_; lean_object* v___x_264_; lean_object* v_fst_265_; lean_object* v_snd_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_fst_258_ = lean_ctor_get(v___y_257_, 0);
lean_inc(v_fst_258_);
v_snd_259_ = lean_ctor_get(v___y_257_, 1);
lean_inc(v_snd_259_);
lean_dec_ref(v___y_257_);
v_fst_260_ = lean_ctor_get(v___y_255_, 0);
lean_inc(v_fst_260_);
v_snd_261_ = lean_ctor_get(v___y_255_, 1);
lean_inc(v_snd_261_);
lean_dec_ref(v___y_255_);
v_fst_262_ = lean_ctor_get(v___y_254_, 0);
v_newEntries_263_ = l_Lean_takeNewEntries___redArg(v_fst_260_, v_fst_262_);
v___x_264_ = lean_apply_3(v_val_253_, v_newEntries_263_, v_snd_261_, v_snd_259_);
v_fst_265_ = lean_ctor_get(v___x_264_, 0);
v_snd_266_ = lean_ctor_get(v___x_264_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v___x_264_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_snd_266_);
lean_inc(v_fst_265_);
lean_dec(v___x_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = l_List_appendTR___redArg(v_fst_265_, v_fst_258_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_snd_266_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed(lean_object* v_val_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5(v_val_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_276_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object* v_descr_285_){
_start:
{
lean_object* v_name_287_; lean_object* v_addEntryFn_288_; lean_object* v_addImportedFn_289_; lean_object* v_toArrayFn_290_; lean_object* v_exportEntriesFnEx_x3f_291_; lean_object* v_asyncMode_292_; lean_object* v_replay_x3f_293_; uint8_t v_logWrites_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___y_306_; 
v_name_287_ = lean_ctor_get(v_descr_285_, 0);
lean_inc(v_name_287_);
v_addEntryFn_288_ = lean_ctor_get(v_descr_285_, 1);
lean_inc(v_addEntryFn_288_);
v_addImportedFn_289_ = lean_ctor_get(v_descr_285_, 2);
lean_inc_n(v_addImportedFn_289_, 2);
v_toArrayFn_290_ = lean_ctor_get(v_descr_285_, 3);
lean_inc_ref(v_toArrayFn_290_);
v_exportEntriesFnEx_x3f_291_ = lean_ctor_get(v_descr_285_, 4);
lean_inc(v_exportEntriesFnEx_x3f_291_);
v_asyncMode_292_ = lean_ctor_get(v_descr_285_, 5);
lean_inc(v_asyncMode_292_);
v_replay_x3f_293_ = lean_ctor_get(v_descr_285_, 6);
lean_inc(v_replay_x3f_293_);
v_logWrites_294_ = lean_ctor_get_uint8(v_descr_285_, sizeof(void*)*7);
lean_dec_ref(v_descr_285_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0), 3, 1);
lean_closure_set(v___f_295_, 0, v_addEntryFn_288_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1), 4, 2);
lean_closure_set(v___f_296_, 0, v_exportEntriesFnEx_x3f_291_);
lean_closure_set(v___f_296_, 1, v_toArrayFn_290_);
v___f_297_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0));
v___f_298_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1));
v___x_299_ = lean_box(0);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_300_, 0, v_addImportedFn_289_);
lean_closure_set(v___f_300_, 1, v___x_299_);
v___x_301_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2));
v___x_302_ = lean_apply_1(v_addImportedFn_289_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_299_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_304_, 0, lean_box(0));
lean_closure_set(v___x_304_, 1, lean_box(0));
lean_closure_set(v___x_304_, 2, v___x_303_);
if (lean_obj_tag(v_replay_x3f_293_) == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_box(0);
v___y_306_ = v___x_311_;
goto v___jp_305_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_val_312_ = lean_ctor_get(v_replay_x3f_293_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_replay_x3f_293_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v_replay_x3f_293_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_val_312_);
lean_dec(v_replay_x3f_293_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___f_316_; lean_object* v___x_318_; 
v___f_316_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed), 5, 1);
lean_closure_set(v___f_316_, 0, v_val_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___f_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___f_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v___y_306_ = v___x_318_;
goto v___jp_305_;
}
}
}
v___jp_305_:
{
uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = 0;
v___x_308_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_308_, 0, v_name_287_);
lean_ctor_set(v___x_308_, 1, v___x_304_);
lean_ctor_set(v___x_308_, 2, v___f_300_);
lean_ctor_set(v___x_308_, 3, v___f_295_);
lean_ctor_set(v___x_308_, 4, v___f_296_);
lean_ctor_set(v___x_308_, 5, v___f_297_);
lean_ctor_set(v___x_308_, 6, v_asyncMode_292_);
lean_ctor_set(v___x_308_, 7, v___y_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*8, v___x_307_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*8 + 1, v_logWrites_294_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___f_298_);
v___x_310_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object* v_descr_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* v_00_u03b1_324_, lean_object* v_00_u03c3_325_, lean_object* v_inst_326_, lean_object* v_descr_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* v_00_u03b1_330_, lean_object* v_00_u03c3_331_, lean_object* v_inst_332_, lean_object* v_descr_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_registerSimplePersistentEnvExtension(v_00_u03b1_330_, v_00_u03c3_331_, v_inst_332_, v_descr_333_);
lean_dec(v_inst_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object* v_x_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_344_, v___y_345_);
lean_dec_ref(v___y_345_);
lean_dec_ref(v_x_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(lean_object* v_s_348_, lean_object* v_x_349_){
_start:
{
lean_inc_ref(v_s_348_);
return v_s_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1___boxed(lean_object* v_s_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(v_s_350_, v_x_351_);
lean_dec(v_x_351_);
lean_dec_ref(v_s_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0));
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(v_x_358_, v_x_359_);
lean_dec_ref(v_x_359_);
lean_dec_ref(v_x_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(lean_object* v_x_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3___boxed(lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(v_x_363_);
lean_dec_ref(v_x_363_);
return v_res_364_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_369_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5(void){
_start:
{
lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___f_370_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3));
v___f_371_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2));
v___f_372_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1));
v___f_373_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0));
v___x_374_ = lean_box(0);
v___x_375_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_376_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___f_373_);
lean_ctor_set(v___x_376_, 3, v___f_372_);
lean_ctor_set(v___x_376_, 4, v___f_371_);
lean_ctor_set(v___x_376_, 5, v___f_370_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object* v_00_u03b1_381_, lean_object* v_00_u03c3_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg(){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg___boxed(lean_object* v___dummy_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v_res_387_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object* v_00_u03b1_389_, lean_object* v_00_u03c3_390_, lean_object* v_inst_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0, &l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object* v_00_u03b1_393_, lean_object* v_00_u03c3_394_, lean_object* v_inst_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_SimplePersistentEnvExtension_instInhabited(v_00_u03b1_393_, v_00_u03c3_394_, v_inst_395_);
lean_dec(v_inst_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object* v_inst_397_, lean_object* v_ext_398_, lean_object* v_env_399_, lean_object* v_asyncMode_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v_fst_406_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v_inst_397_);
v___x_403_ = lean_box(0);
v___x_404_ = 0;
v___x_405_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_402_, v_ext_398_, v_env_399_, v_asyncMode_400_, v___x_403_, v___x_404_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_406_);
lean_dec(v___x_405_);
return v_fst_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object* v_inst_407_, lean_object* v_ext_408_, lean_object* v_env_409_, lean_object* v_asyncMode_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_407_, v_ext_408_, v_env_409_, v_asyncMode_410_);
lean_dec(v_asyncMode_410_);
lean_dec_ref(v_ext_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* v_00_u03b1_412_, lean_object* v_00_u03c3_413_, lean_object* v_inst_414_, lean_object* v_ext_415_, lean_object* v_env_416_, lean_object* v_asyncMode_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_414_, v_ext_415_, v_env_416_, v_asyncMode_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object* v_00_u03b1_419_, lean_object* v_00_u03c3_420_, lean_object* v_inst_421_, lean_object* v_ext_422_, lean_object* v_env_423_, lean_object* v_asyncMode_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_SimplePersistentEnvExtension_getEntries(v_00_u03b1_419_, v_00_u03c3_420_, v_inst_421_, v_ext_422_, v_env_423_, v_asyncMode_424_);
lean_dec(v_asyncMode_424_);
lean_dec_ref(v_ext_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object* v_inst_426_, lean_object* v_ext_427_, lean_object* v_env_428_, lean_object* v_asyncMode_429_, lean_object* v_asyncDecl_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v_snd_435_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_inst_426_);
v___x_433_ = 0;
v___x_434_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_432_, v_ext_427_, v_env_428_, v_asyncMode_429_, v_asyncDecl_430_, v___x_433_);
v_snd_435_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_snd_435_);
lean_dec(v___x_434_);
return v_snd_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object* v_inst_436_, lean_object* v_ext_437_, lean_object* v_env_438_, lean_object* v_asyncMode_439_, lean_object* v_asyncDecl_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_436_, v_ext_437_, v_env_438_, v_asyncMode_439_, v_asyncDecl_440_);
lean_dec(v_asyncMode_439_);
lean_dec_ref(v_ext_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* v_00_u03b1_442_, lean_object* v_00_u03c3_443_, lean_object* v_inst_444_, lean_object* v_ext_445_, lean_object* v_env_446_, lean_object* v_asyncMode_447_, lean_object* v_asyncDecl_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_444_, v_ext_445_, v_env_446_, v_asyncMode_447_, v_asyncDecl_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object* v_00_u03b1_450_, lean_object* v_00_u03c3_451_, lean_object* v_inst_452_, lean_object* v_ext_453_, lean_object* v_env_454_, lean_object* v_asyncMode_455_, lean_object* v_asyncDecl_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_SimplePersistentEnvExtension_getState(v_00_u03b1_450_, v_00_u03c3_451_, v_inst_452_, v_ext_453_, v_env_454_, v_asyncMode_455_, v_asyncDecl_456_);
lean_dec(v_asyncMode_455_);
lean_dec_ref(v_ext_453_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object* v_s_458_, lean_object* v_ps_459_){
_start:
{
lean_object* v_state_460_; lean_object* v_importedEntries_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_477_; 
v_state_460_ = lean_ctor_get(v_ps_459_, 1);
v_importedEntries_461_ = lean_ctor_get(v_ps_459_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_ps_459_);
if (v_isSharedCheck_477_ == 0)
{
v___x_463_ = v_ps_459_;
v_isShared_464_ = v_isSharedCheck_477_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_state_460_);
lean_inc(v_importedEntries_461_);
lean_dec(v_ps_459_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_477_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_fst_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_475_; 
v_fst_465_ = lean_ctor_get(v_state_460_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_state_460_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_state_460_, 1);
lean_dec(v_unused_476_);
v___x_467_ = v_state_460_;
v_isShared_468_ = v_isSharedCheck_475_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_fst_465_);
lean_dec(v_state_460_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_475_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v_s_458_);
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_s_458_);
v___x_470_ = v_reuseFailAlloc_474_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_470_);
v___x_472_ = v___x_463_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_importedEntries_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object* v_ext_478_, lean_object* v_env_479_, lean_object* v_s_480_){
_start:
{
lean_object* v_toEnvExtension_481_; lean_object* v_asyncMode_482_; uint8_t v_logWrites_483_; lean_object* v___f_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_toEnvExtension_481_ = lean_ctor_get(v_ext_478_, 0);
lean_inc_ref(v_toEnvExtension_481_);
lean_dec_ref(v_ext_478_);
v_asyncMode_482_ = lean_ctor_get(v_toEnvExtension_481_, 2);
lean_inc(v_asyncMode_482_);
v_logWrites_483_ = lean_ctor_get_uint8(v_toEnvExtension_481_, sizeof(void*)*6);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_484_, 0, v_s_480_);
v___x_485_ = lean_box(0);
v___x_486_ = 1;
if (v_logWrites_483_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_481_, v_env_479_, v___f_484_, v_asyncMode_482_, v___x_485_, v___x_486_);
lean_dec(v_asyncMode_482_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_inc_ref(v_toEnvExtension_481_);
v___x_488_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_481_, v_env_479_);
lean_dec_ref(v_env_479_);
v___x_489_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_481_, v___x_488_, v___f_484_, v_asyncMode_482_, v___x_485_, v___x_486_);
lean_dec(v_asyncMode_482_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* v_00_u03b1_490_, lean_object* v_00_u03c3_491_, lean_object* v_ext_492_, lean_object* v_env_493_, lean_object* v_s_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_492_, v_env_493_, v_s_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_496_, lean_object* v_ps_497_){
_start:
{
lean_object* v_state_498_; lean_object* v_importedEntries_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_516_; 
v_state_498_ = lean_ctor_get(v_ps_497_, 1);
v_importedEntries_499_ = lean_ctor_get(v_ps_497_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_ps_497_);
if (v_isSharedCheck_516_ == 0)
{
v___x_501_ = v_ps_497_;
v_isShared_502_ = v_isSharedCheck_516_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_state_498_);
lean_inc(v_importedEntries_499_);
lean_dec(v_ps_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_516_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_fst_503_; lean_object* v_snd_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_515_; 
v_fst_503_ = lean_ctor_get(v_state_498_, 0);
v_snd_504_ = lean_ctor_get(v_state_498_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_state_498_);
if (v_isSharedCheck_515_ == 0)
{
v___x_506_ = v_state_498_;
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_snd_504_);
lean_inc(v_fst_503_);
lean_dec(v_state_498_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_apply_1(v_f_496_, v_snd_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_fst_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_510_);
v___x_512_ = v___x_501_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_importedEntries_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object* v_ext_517_, lean_object* v_env_518_, lean_object* v_f_519_){
_start:
{
lean_object* v_toEnvExtension_520_; lean_object* v_asyncMode_521_; uint8_t v_logWrites_522_; lean_object* v___f_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_toEnvExtension_520_ = lean_ctor_get(v_ext_517_, 0);
lean_inc_ref(v_toEnvExtension_520_);
lean_dec_ref(v_ext_517_);
v_asyncMode_521_ = lean_ctor_get(v_toEnvExtension_520_, 2);
lean_inc(v_asyncMode_521_);
v_logWrites_522_ = lean_ctor_get_uint8(v_toEnvExtension_520_, sizeof(void*)*6);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_523_, 0, v_f_519_);
v___x_524_ = lean_box(0);
v___x_525_ = 1;
if (v_logWrites_522_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_520_, v_env_518_, v___f_523_, v_asyncMode_521_, v___x_524_, v___x_525_);
lean_dec(v_asyncMode_521_);
return v___x_526_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_inc_ref(v_toEnvExtension_520_);
v___x_527_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_520_, v_env_518_);
lean_dec_ref(v_env_518_);
v___x_528_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_520_, v___x_527_, v___f_523_, v_asyncMode_521_, v___x_524_, v___x_525_);
lean_dec(v_asyncMode_521_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* v_00_u03b1_529_, lean_object* v_00_u03c3_530_, lean_object* v_ext_531_, lean_object* v_env_532_, lean_object* v_f_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(v_ext_531_, v_env_532_, v_f_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_NameSet_empty;
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_538_);
lean_dec_ref(v_x_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object* v_hi_540_, lean_object* v_pivot_541_, lean_object* v_as_542_, lean_object* v_i_543_, lean_object* v_k_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_nat_dec_lt(v_k_544_, v_hi_540_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v_k_544_);
v___x_546_ = lean_array_fswap(v_as_542_, v_i_543_, v_hi_540_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_i_543_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_array_fget_borrowed(v_as_542_, v_k_544_);
v___x_549_ = l_Lean_Name_quickLt(v___x_548_, v_pivot_541_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_add(v_k_544_, v___x_550_);
lean_dec(v_k_544_);
v_k_544_ = v___x_551_;
goto _start;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = lean_array_fswap(v_as_542_, v_i_543_, v_k_544_);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_i_543_, v___x_554_);
lean_dec(v_i_543_);
v___x_556_ = lean_nat_add(v_k_544_, v___x_554_);
lean_dec(v_k_544_);
v_as_542_ = v___x_553_;
v_i_543_ = v___x_555_;
v_k_544_ = v___x_556_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object* v_hi_558_, lean_object* v_pivot_559_, lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_558_, v_pivot_559_, v_as_560_, v_i_561_, v_k_562_);
lean_dec(v_pivot_559_);
lean_dec(v_hi_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_n_564_, lean_object* v_as_565_, lean_object* v_lo_566_, lean_object* v_hi_567_){
_start:
{
lean_object* v___y_569_; uint8_t v___x_579_; 
v___x_579_ = lean_nat_dec_lt(v_lo_566_, v_hi_567_);
if (v___x_579_ == 0)
{
lean_dec(v_lo_566_);
return v_as_565_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_mid_582_; lean_object* v___y_584_; lean_object* v___y_590_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_580_ = lean_nat_add(v_lo_566_, v_hi_567_);
v___x_581_ = lean_unsigned_to_nat(1u);
v_mid_582_ = lean_nat_shiftr(v___x_580_, v___x_581_);
lean_dec(v___x_580_);
v___x_595_ = lean_array_fget_borrowed(v_as_565_, v_mid_582_);
v___x_596_ = lean_array_fget_borrowed(v_as_565_, v_lo_566_);
v___x_597_ = l_Lean_Name_quickLt(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
v___y_590_ = v_as_565_;
goto v___jp_589_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_array_fswap(v_as_565_, v_lo_566_, v_mid_582_);
v___y_590_ = v___x_598_;
goto v___jp_589_;
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_array_fget_borrowed(v___y_584_, v_mid_582_);
v___x_586_ = lean_array_fget_borrowed(v___y_584_, v_hi_567_);
v___x_587_ = l_Lean_Name_quickLt(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v_mid_582_);
v___y_569_ = v___y_584_;
goto v___jp_568_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_array_fswap(v___y_584_, v_mid_582_, v_hi_567_);
lean_dec(v_mid_582_);
v___y_569_ = v___x_588_;
goto v___jp_568_;
}
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_array_fget_borrowed(v___y_590_, v_hi_567_);
v___x_592_ = lean_array_fget_borrowed(v___y_590_, v_lo_566_);
v___x_593_ = l_Lean_Name_quickLt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
v___y_584_ = v___y_590_;
goto v___jp_583_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_fswap(v___y_590_, v_lo_566_, v_hi_567_);
v___y_584_ = v___x_594_;
goto v___jp_583_;
}
}
}
v___jp_568_:
{
lean_object* v_pivot_570_; lean_object* v___x_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; uint8_t v___x_574_; 
v_pivot_570_ = lean_array_fget(v___y_569_, v_hi_567_);
lean_inc_n(v_lo_566_, 2);
v___x_571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_567_, v_pivot_570_, v___y_569_, v_lo_566_, v_lo_566_);
lean_dec(v_pivot_570_);
v_fst_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_573_);
lean_dec_ref(v___x_571_);
v___x_574_ = lean_nat_dec_le(v_hi_567_, v_fst_572_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_564_, v_snd_573_, v_lo_566_, v_fst_572_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_fst_572_, v___x_576_);
lean_dec(v_fst_572_);
v_as_565_ = v___x_575_;
v_lo_566_ = v___x_577_;
goto _start;
}
else
{
lean_dec(v_fst_572_);
lean_dec(v_lo_566_);
return v_snd_573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_n_599_, lean_object* v_as_600_, lean_object* v_lo_601_, lean_object* v_hi_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_599_, v_as_600_, v_lo_601_, v_hi_602_);
lean_dec(v_hi_602_);
lean_dec(v_n_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_605_ = lean_array_mk(v_es_604_);
v___x_606_ = lean_array_get_size(v___x_605_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_eq(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___y_612_; uint8_t v___x_616_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_sub(v___x_606_, v___x_609_);
v___x_616_ = lean_nat_dec_le(v___x_607_, v___x_610_);
if (v___x_616_ == 0)
{
lean_inc(v___x_610_);
v___y_612_ = v___x_610_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___x_607_;
goto v___jp_611_;
}
v___jp_611_:
{
uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_le(v___y_612_, v___x_610_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v___x_610_);
lean_inc(v___y_612_);
v___x_614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_606_, v___x_605_, v___y_612_, v___y_612_);
lean_dec(v___y_612_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_606_, v___x_605_, v___y_612_, v___x_610_);
lean_dec(v___x_610_);
return v___x_615_;
}
}
}
else
{
return v___x_605_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_617_, lean_object* v_x2_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = l_Lean_NameSet_contains(v_x1_617_, v_x2_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = 1;
return v___x_620_;
}
else
{
uint8_t v___x_621_; 
v___x_621_ = 0;
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_622_, lean_object* v_x2_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_622_, v_x2_623_);
lean_dec(v_x2_623_);
lean_dec(v_x1_622_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_635_, lean_object* v_asyncMode_636_, uint8_t v_logWrites_637_){
_start:
{
lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___f_639_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_640_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_641_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_642_ = lean_box(0);
v___x_643_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_644_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_644_, 0, v_name_635_);
lean_ctor_set(v___x_644_, 1, v___f_639_);
lean_ctor_set(v___x_644_, 2, v___f_640_);
lean_ctor_set(v___x_644_, 3, v___f_641_);
lean_ctor_set(v___x_644_, 4, v___x_642_);
lean_ctor_set(v___x_644_, 5, v_asyncMode_636_);
lean_ctor_set(v___x_644_, 6, v___x_643_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*7, v_logWrites_637_);
v___x_645_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_646_, lean_object* v_asyncMode_647_, lean_object* v_logWrites_648_, lean_object* v_a_649_){
_start:
{
uint8_t v_logWrites_boxed_650_; lean_object* v_res_651_; 
v_logWrites_boxed_650_ = lean_unbox(v_logWrites_648_);
v_res_651_ = l_Lean_mkTagDeclarationExtension(v_name_646_, v_asyncMode_647_, v_logWrites_boxed_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_652_, lean_object* v_as_653_, lean_object* v_lo_654_, lean_object* v_hi_655_, lean_object* v_w_656_, lean_object* v_hlo_657_, lean_object* v_hhi_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_652_, v_as_653_, v_lo_654_, v_hi_655_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_660_, lean_object* v_as_661_, lean_object* v_lo_662_, lean_object* v_hi_663_, lean_object* v_w_664_, lean_object* v_hlo_665_, lean_object* v_hhi_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_660_, v_as_661_, v_lo_662_, v_hi_663_, v_w_664_, v_hlo_665_, v_hhi_666_);
lean_dec(v_hi_663_);
lean_dec(v_n_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object* v_n_668_, lean_object* v_lo_669_, lean_object* v_hi_670_, lean_object* v_hhi_671_, lean_object* v_pivot_672_, lean_object* v_as_673_, lean_object* v_i_674_, lean_object* v_k_675_, lean_object* v_ilo_676_, lean_object* v_ik_677_, lean_object* v_w_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_670_, v_pivot_672_, v_as_673_, v_i_674_, v_k_675_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object* v_n_680_, lean_object* v_lo_681_, lean_object* v_hi_682_, lean_object* v_hhi_683_, lean_object* v_pivot_684_, lean_object* v_as_685_, lean_object* v_i_686_, lean_object* v_k_687_, lean_object* v_ilo_688_, lean_object* v_ik_689_, lean_object* v_w_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_680_, v_lo_681_, v_hi_682_, v_hhi_683_, v_pivot_684_, v_as_685_, v_i_686_, v_k_687_, v_ilo_688_, v_ik_689_, v_w_690_);
lean_dec(v_pivot_684_);
lean_dec(v_hi_682_);
lean_dec(v_lo_681_);
lean_dec(v_n_680_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_697_, v___y_698_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_x_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_701_, lean_object* v_x_702_){
_start:
{
lean_inc_ref(v_s_701_);
return v_s_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_703_, lean_object* v_x_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_703_, v_x_704_);
lean_dec(v_x_704_);
lean_dec_ref(v_s_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1));
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_713_, v_x_714_);
lean_dec_ref(v_x_714_);
lean_dec_ref(v_x_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_box(0);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_718_);
lean_dec_ref(v_x_718_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___f_724_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_725_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_726_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_727_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_728_ = lean_box(0);
v___x_729_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_730_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___f_727_);
lean_ctor_set(v___x_730_, 3, v___f_726_);
lean_ctor_set(v___x_730_, 4, v___f_725_);
lean_ctor_set(v___x_730_, 5, v___f_724_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_733_, lean_object* v_msg_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_panic_fn_borrowed(v_env_733_, v_msg_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object* v_env_736_, lean_object* v_msg_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_736_, v_msg_737_);
lean_dec_ref(v_env_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag___lam__0(lean_object* v_addEntryFn_739_, lean_object* v_declName_740_, lean_object* v_s_741_){
_start:
{
lean_object* v_importedEntries_742_; lean_object* v_state_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_importedEntries_742_ = lean_ctor_get(v_s_741_, 0);
v_state_743_ = lean_ctor_get(v_s_741_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_s_741_);
if (v_isSharedCheck_751_ == 0)
{
v___x_745_ = v_s_741_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_state_743_);
lean_inc(v_importedEntries_742_);
lean_dec(v_s_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_state_747_; lean_object* v___x_749_; 
v_state_747_ = lean_apply_2(v_addEntryFn_739_, v_state_743_, v_declName_740_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_state_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_importedEntries_742_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_state_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_755_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_756_ = lean_unsigned_to_nat(4u);
v___x_757_ = lean_unsigned_to_nat(120u);
v___x_758_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_759_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_760_ = l_mkPanicMessageWithDecl(v___x_759_, v___x_758_, v___x_757_, v___x_756_, v___x_755_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_761_, lean_object* v_env_762_, lean_object* v_declName_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_Lean_Name_isAnonymous(v_declName_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_762_, v_declName_763_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_766_ = lean_box(1);
v___x_767_ = lean_box(1);
v___x_768_ = lean_box(0);
lean_inc_ref(v_env_762_);
v___x_769_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_766_, v_ext_761_, v_env_762_, v___x_767_, v___x_768_);
v___x_770_ = l_Lean_NameSet_contains(v___x_769_, v_declName_763_);
lean_dec(v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v_toEnvExtension_771_; lean_object* v_addEntryFn_772_; lean_object* v_asyncMode_773_; uint8_t v_logWrites_774_; lean_object* v___f_775_; uint8_t v___x_776_; 
v_toEnvExtension_771_ = lean_ctor_get(v_ext_761_, 0);
lean_inc_ref(v_toEnvExtension_771_);
v_addEntryFn_772_ = lean_ctor_get(v_ext_761_, 3);
lean_inc(v_addEntryFn_772_);
lean_dec_ref(v_ext_761_);
v_asyncMode_773_ = lean_ctor_get(v_toEnvExtension_771_, 2);
lean_inc(v_asyncMode_773_);
v_logWrites_774_ = lean_ctor_get_uint8(v_toEnvExtension_771_, sizeof(void*)*6);
lean_inc(v_declName_763_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_TagDeclarationExtension_tag___lam__0), 3, 2);
lean_closure_set(v___f_775_, 0, v_addEntryFn_772_);
lean_closure_set(v___f_775_, 1, v_declName_763_);
v___x_776_ = 1;
if (v_logWrites_774_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_771_, v_env_762_, v___f_775_, v_asyncMode_773_, v_declName_763_, v___x_776_);
lean_dec(v_asyncMode_773_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_inc(v_declName_763_);
v___x_778_ = l_Lean_Environment_logDeclChange(v_env_762_, v_declName_763_);
v___x_779_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_771_, v___x_778_, v___f_775_, v_asyncMode_773_, v_declName_763_, v___x_776_);
lean_dec(v_asyncMode_773_);
return v___x_779_;
}
}
else
{
lean_dec(v_declName_763_);
lean_dec_ref(v_ext_761_);
return v_env_762_;
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_765_, 1);
lean_dec(v_declName_763_);
lean_dec_ref(v_ext_761_);
v___x_780_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_781_ = lean_panic_fn_borrowed(v_env_762_, v___x_780_);
lean_dec_ref(v_env_762_);
return v___x_781_;
}
}
else
{
lean_dec(v_declName_763_);
lean_dec_ref(v_ext_761_);
return v_env_762_;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object* v___y_782_, lean_object* v_as_783_, lean_object* v_k_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_m_789_; lean_object* v_a_790_; uint8_t v___x_791_; 
v___x_787_ = lean_nat_add(v_x_785_, v_x_786_);
v___x_788_ = lean_unsigned_to_nat(1u);
v_m_789_ = lean_nat_shiftr(v___x_787_, v___x_788_);
lean_dec(v___x_787_);
v_a_790_ = lean_array_fget_borrowed(v_as_783_, v_m_789_);
v___x_791_ = l_Lean_Name_quickLt(v_a_790_, v_k_784_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
lean_dec(v_x_786_);
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = l_Lean_Name_quickLt(v_k_784_, v_a_790_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; 
lean_dec(v_m_789_);
lean_dec(v_x_785_);
v___x_794_ = lean_nat_dec_le(v___x_792_, v___y_782_);
return v___x_794_;
}
else
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_eq(v_m_789_, v___x_792_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_nat_sub(v_m_789_, v___x_788_);
lean_dec(v_m_789_);
v___x_797_ = lean_nat_dec_lt(v___x_796_, v_x_785_);
if (v___x_797_ == 0)
{
v_x_786_ = v___x_796_;
goto _start;
}
else
{
lean_dec(v___x_796_);
lean_dec(v_x_785_);
return v___x_795_;
}
}
else
{
lean_dec(v_m_789_);
lean_dec(v_x_785_);
return v___x_791_;
}
}
}
else
{
lean_object* v___x_799_; uint8_t v___x_800_; 
lean_dec(v_x_785_);
v___x_799_ = lean_nat_add(v_m_789_, v___x_788_);
lean_dec(v_m_789_);
v___x_800_ = lean_nat_dec_le(v___x_799_, v_x_786_);
if (v___x_800_ == 0)
{
lean_dec(v___x_799_);
lean_dec(v_x_786_);
return v___x_800_;
}
else
{
v_x_785_ = v___x_799_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object* v___y_802_, lean_object* v_as_803_, lean_object* v_k_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_802_, v_as_803_, v_k_804_, v_x_805_, v_x_806_);
lean_dec(v_k_804_);
lean_dec_ref(v_as_803_);
lean_dec(v___y_802_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_812_, lean_object* v_env_813_, lean_object* v_declName_814_, lean_object* v_asyncMode_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_box(1);
v___x_817_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_813_, v_declName_814_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; 
lean_inc(v_declName_814_);
v___x_818_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_816_, v_ext_812_, v_env_813_, v_asyncMode_815_, v_declName_814_);
v___x_819_ = l_Lean_NameSet_contains(v___x_818_, v_declName_814_);
lean_dec(v_declName_814_);
lean_dec(v___x_818_);
return v___x_819_;
}
else
{
lean_object* v_val_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_val_820_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_820_);
lean_dec_ref_known(v___x_817_, 1);
v___x_821_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_822_ = 0;
v___x_823_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_821_, v_ext_812_, v_env_813_, v_val_820_, v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref(v_env_813_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_array_get_size(v___x_823_);
v___x_826_ = lean_nat_dec_lt(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_dec_ref(v___x_823_);
lean_dec(v_declName_814_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_sub(v___x_825_, v___x_827_);
v___x_829_ = lean_nat_dec_le(v___x_824_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v___x_828_);
lean_dec_ref(v___x_823_);
lean_dec(v_declName_814_);
return v___x_829_;
}
else
{
uint8_t v___x_830_; 
lean_inc(v___x_828_);
v___x_830_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_828_, v___x_823_, v_declName_814_, v___x_824_, v___x_828_);
lean_dec(v_declName_814_);
lean_dec_ref(v___x_823_);
lean_dec(v___x_828_);
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_831_, lean_object* v_env_832_, lean_object* v_declName_833_, lean_object* v_asyncMode_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_831_, v_env_832_, v_declName_833_, v_asyncMode_834_);
lean_dec(v_asyncMode_834_);
lean_dec_ref(v_ext_831_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object* v___y_837_, lean_object* v_as_838_, lean_object* v_k_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_837_, v_as_838_, v_k_839_, v_x_840_, v_x_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object* v___y_844_, lean_object* v_as_845_, lean_object* v_k_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v___y_844_, v_as_845_, v_k_846_, v_x_847_, v_x_848_, v_x_849_);
lean_dec(v_k_846_);
lean_dec_ref(v_as_845_);
lean_dec(v___y_844_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(lean_object* v_x_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed(lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(v_x_857_, v___y_858_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_x_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(lean_object* v_s_861_, lean_object* v_x_862_){
_start:
{
lean_inc(v_s_861_);
return v_s_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed(lean_object* v_s_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(v_s_863_, v_x_864_);
lean_dec_ref(v_x_864_);
lean_dec(v_s_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1));
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed(lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(v_x_873_, v_x_874_);
lean_dec(v_x_874_);
lean_dec_ref(v_x_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_box(0);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed(lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(v_x_878_);
lean_dec(v_x_878_);
return v_res_879_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___f_884_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_885_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2));
v___f_886_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1));
v___f_887_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0));
v___x_888_ = lean_box(0);
v___x_889_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_890_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_888_);
lean_ctor_set(v___x_890_, 2, v___f_887_);
lean_ctor_set(v___x_890_, 3, v___f_886_);
lean_ctor_set(v___x_890_, 4, v___f_885_);
lean_ctor_set(v___x_890_, 5, v___f_884_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg(){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___boxed(lean_object* v___dummy_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v_res_894_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0(void){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_00_u03b1_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg(){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg___boxed(lean_object* v___dummy_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_instInhabitedMapDeclarationExtension___redArg();
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_909_; 
v_fst_907_ = lean_ctor_get(v_x_906_, 0);
lean_inc(v_fst_907_);
v_snd_908_ = lean_ctor_get(v_x_906_, 1);
lean_inc(v_snd_908_);
lean_dec_ref(v_x_906_);
v___x_909_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_907_, v_snd_908_, v_s_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_910_, lean_object* v_env_911_, lean_object* v_s_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_apply_2(v_exportEntriesFn_910_, v_env_911_, v_s_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
return v_x_915_;
}
else
{
lean_object* v_head_917_; lean_object* v_tail_918_; lean_object* v___x_919_; 
v_head_917_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_head_917_);
v_tail_918_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_tail_918_);
lean_dec_ref_known(v_x_916_, 2);
v___x_919_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_914_, v_head_917_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v_val_920_; lean_object* v___x_921_; 
v_val_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_917_, v_val_920_, v_x_915_);
v_x_915_ = v___x_921_;
v_x_916_ = v_tail_918_;
goto _start;
}
else
{
lean_dec(v___x_919_);
lean_dec(v_head_917_);
v_x_916_ = v_tail_918_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_924_, v_x_925_, v_x_926_);
lean_dec(v_newState_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_928_, lean_object* v_newState_929_, lean_object* v_newConsts_930_, lean_object* v_s_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_929_, v_s_931_, v_newConsts_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_933_, lean_object* v_newState_934_, lean_object* v_newConsts_935_, lean_object* v_s_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_933_, v_newState_934_, v_newConsts_935_, v_s_936_);
lean_dec(v_newState_934_);
lean_dec(v_x_933_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0));
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_940_);
lean_dec(v_x_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_948_, lean_object* v_x_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_948_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_953_, lean_object* v_x_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_953_, v_x_954_, v___y_955_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_x_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_967_, lean_object* v_asyncMode_968_, uint8_t v_logWrites_969_, lean_object* v_exportEntriesFn_970_){
_start:
{
lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___f_972_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_973_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1), 3, 1);
lean_closure_set(v___f_973_, 0, v_exportEntriesFn_970_);
v___f_974_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_975_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_976_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_977_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_978_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_979_ = 0;
v___x_980_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_980_, 0, v_name_967_);
lean_ctor_set(v___x_980_, 1, v___f_976_);
lean_ctor_set(v___x_980_, 2, v___f_977_);
lean_ctor_set(v___x_980_, 3, v___f_972_);
lean_ctor_set(v___x_980_, 4, v___f_973_);
lean_ctor_set(v___x_980_, 5, v___f_974_);
lean_ctor_set(v___x_980_, 6, v_asyncMode_968_);
lean_ctor_set(v___x_980_, 7, v___x_978_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*8, v___x_979_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*8 + 1, v_logWrites_969_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___f_975_);
v___x_982_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_982_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_982_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_999_, lean_object* v_asyncMode_1000_, lean_object* v_logWrites_1001_, lean_object* v_exportEntriesFn_1002_, lean_object* v_a_1003_){
_start:
{
uint8_t v_logWrites_boxed_1004_; lean_object* v_res_1005_; 
v_logWrites_boxed_1004_ = lean_unbox(v_logWrites_1001_);
v_res_1005_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_999_, v_asyncMode_1000_, v_logWrites_boxed_1004_, v_exportEntriesFn_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_1006_, lean_object* v_name_1007_, lean_object* v_asyncMode_1008_, uint8_t v_logWrites_1009_, lean_object* v_exportEntriesFn_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1007_, v_asyncMode_1008_, v_logWrites_1009_, v_exportEntriesFn_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_name_1014_, lean_object* v_asyncMode_1015_, lean_object* v_logWrites_1016_, lean_object* v_exportEntriesFn_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_logWrites_boxed_1019_; lean_object* v_res_1020_; 
v_logWrites_boxed_1019_ = lean_unbox(v_logWrites_1016_);
v_res_1020_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_1013_, v_name_1014_, v_asyncMode_1015_, v_logWrites_boxed_1019_, v_exportEntriesFn_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_1021_, lean_object* v_newState_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_1022_, v_x_1023_, v_x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_newState_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_1026_, v_newState_1027_, v_x_1028_, v_x_1029_);
lean_dec(v_newState_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___lam__0(lean_object* v_addEntryFn_1031_, lean_object* v___x_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v_importedEntries_1034_; lean_object* v_state_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_importedEntries_1034_ = lean_ctor_get(v_s_1033_, 0);
v_state_1035_ = lean_ctor_get(v_s_1033_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_s_1033_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1037_ = v_s_1033_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_state_1035_);
lean_inc(v_importedEntries_1034_);
lean_dec(v_s_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_state_1039_; lean_object* v___x_1041_; 
v_state_1039_ = lean_apply_2(v_addEntryFn_1031_, v_state_1035_, v___x_1032_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_state_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_importedEntries_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_state_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_1050_, lean_object* v_env_1051_, lean_object* v_declName_1052_, lean_object* v_val_1053_, uint8_t v_allowOverwrite_1054_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1051_, v_declName_1052_);
if (lean_obj_tag(v___x_1066_) == 1)
{
lean_object* v_val_1067_; lean_object* v_name_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_val_1053_);
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_name_1068_ = lean_ctor_get(v_ext_1050_, 1);
lean_inc(v_name_1068_);
lean_dec_ref(v_ext_1050_);
v___x_1069_ = lean_box(0);
v___x_1070_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1071_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1072_ = lean_unsigned_to_nat(179u);
v___x_1073_ = lean_unsigned_to_nat(4u);
v___x_1074_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1075_ = 1;
v___x_1076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1052_, v___x_1075_);
v___x_1077_ = lean_string_append(v___x_1074_, v___x_1076_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1079_ = lean_string_append(v___x_1077_, v___x_1078_);
v___x_1080_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1068_, v___x_1075_);
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_1083_ = lean_string_append(v___x_1081_, v___x_1082_);
v___x_1084_ = l_Lean_Environment_allImportedModuleNames(v_env_1051_);
v___x_1085_ = lean_array_get(v___x_1069_, v___x_1084_, v_val_1067_);
lean_dec(v_val_1067_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1085_, v___x_1075_);
v___x_1087_ = lean_string_append(v___x_1083_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_1089_ = lean_string_append(v___x_1087_, v___x_1088_);
v___x_1090_ = l_mkPanicMessageWithDecl(v___x_1070_, v___x_1071_, v___x_1072_, v___x_1073_, v___x_1089_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = lean_panic_fn_borrowed(v_env_1051_, v___x_1090_);
lean_dec_ref(v_env_1051_);
return v___x_1091_;
}
else
{
lean_dec(v___x_1066_);
if (v_allowOverwrite_1054_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1092_ = lean_box(1);
v___x_1093_ = lean_box(1);
v___x_1094_ = lean_box(0);
lean_inc_ref(v_env_1051_);
v___x_1095_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1092_, v_ext_1050_, v_env_1051_, v___x_1093_, v___x_1094_, v_allowOverwrite_1054_);
v___x_1096_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1052_, v___x_1095_);
lean_dec(v___x_1095_);
if (v___x_1096_ == 0)
{
goto v___jp_1055_;
}
else
{
lean_object* v_name_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_val_1053_);
v_name_1097_ = lean_ctor_get(v_ext_1050_, 1);
lean_inc(v_name_1097_);
lean_dec_ref(v_ext_1050_);
v___x_1098_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1099_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1100_ = lean_unsigned_to_nat(186u);
v___x_1101_ = lean_unsigned_to_nat(4u);
v___x_1102_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1052_, v___x_1096_);
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1106_ = lean_string_append(v___x_1104_, v___x_1105_);
v___x_1107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1097_, v___x_1096_);
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__5));
v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
v___x_1111_ = l_mkPanicMessageWithDecl(v___x_1098_, v___x_1099_, v___x_1100_, v___x_1101_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = lean_panic_fn_borrowed(v_env_1051_, v___x_1111_);
lean_dec_ref(v_env_1051_);
return v___x_1112_;
}
}
else
{
goto v___jp_1055_;
}
}
v___jp_1055_:
{
lean_object* v_toEnvExtension_1056_; lean_object* v_addEntryFn_1057_; lean_object* v_asyncMode_1058_; uint8_t v_logWrites_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; uint8_t v___x_1062_; 
v_toEnvExtension_1056_ = lean_ctor_get(v_ext_1050_, 0);
lean_inc_ref(v_toEnvExtension_1056_);
v_addEntryFn_1057_ = lean_ctor_get(v_ext_1050_, 3);
lean_inc(v_addEntryFn_1057_);
lean_dec_ref(v_ext_1050_);
v_asyncMode_1058_ = lean_ctor_get(v_toEnvExtension_1056_, 2);
lean_inc(v_asyncMode_1058_);
v_logWrites_1059_ = lean_ctor_get_uint8(v_toEnvExtension_1056_, sizeof(void*)*6);
lean_inc(v_declName_1052_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_declName_1052_);
lean_ctor_set(v___x_1060_, 1, v_val_1053_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_insert___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1061_, 0, v_addEntryFn_1057_);
lean_closure_set(v___f_1061_, 1, v___x_1060_);
v___x_1062_ = 1;
if (v_logWrites_1059_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1056_, v_env_1051_, v___f_1061_, v_asyncMode_1058_, v_declName_1052_, v___x_1062_);
lean_dec(v_asyncMode_1058_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_inc(v_declName_1052_);
v___x_1064_ = l_Lean_Environment_logDeclChange(v_env_1051_, v_declName_1052_);
v___x_1065_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1056_, v___x_1064_, v___f_1061_, v_asyncMode_1058_, v_declName_1052_, v___x_1062_);
lean_dec(v_asyncMode_1058_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___boxed(lean_object* v_ext_1113_, lean_object* v_env_1114_, lean_object* v_declName_1115_, lean_object* v_val_1116_, lean_object* v_allowOverwrite_1117_){
_start:
{
uint8_t v_allowOverwrite_boxed_1118_; lean_object* v_res_1119_; 
v_allowOverwrite_boxed_1118_ = lean_unbox(v_allowOverwrite_1117_);
v_res_1119_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1113_, v_env_1114_, v_declName_1115_, v_val_1116_, v_allowOverwrite_boxed_1118_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_1120_, lean_object* v_ext_1121_, lean_object* v_env_1122_, lean_object* v_declName_1123_, lean_object* v_val_1124_, uint8_t v_allowOverwrite_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1121_, v_env_1122_, v_declName_1123_, v_val_1124_, v_allowOverwrite_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_ext_1128_, lean_object* v_env_1129_, lean_object* v_declName_1130_, lean_object* v_val_1131_, lean_object* v_allowOverwrite_1132_){
_start:
{
uint8_t v_allowOverwrite_boxed_1133_; lean_object* v_res_1134_; 
v_allowOverwrite_boxed_1133_ = lean_unbox(v_allowOverwrite_1132_);
v_res_1134_ = l_Lean_MapDeclarationExtension_insert(v_00_u03b1_1127_, v_ext_1128_, v_env_1129_, v_declName_1130_, v_val_1131_, v_allowOverwrite_boxed_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object* v_a_1135_, lean_object* v_b_1136_){
_start:
{
lean_object* v_fst_1137_; lean_object* v_fst_1138_; uint8_t v___x_1139_; 
v_fst_1137_ = lean_ctor_get(v_a_1135_, 0);
v_fst_1138_ = lean_ctor_get(v_b_1136_, 0);
v___x_1139_ = l_Lean_Name_quickLt(v_fst_1137_, v_fst_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object* v_a_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_1140_, v_b_1141_);
lean_dec_ref(v_b_1141_);
lean_dec_ref(v_a_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_inst_1146_, lean_object* v_ext_1147_, lean_object* v_env_1148_, lean_object* v_declName_1149_, lean_object* v_asyncMode_1150_, uint8_t v_level_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_box(1);
v___x_1153_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1148_, v_declName_1149_);
if (lean_obj_tag(v___x_1153_) == 0)
{
uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_inst_1146_);
v___x_1154_ = 0;
lean_inc(v_declName_1149_);
v___x_1155_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1152_, v_ext_1147_, v_env_1148_, v_asyncMode_1150_, v_declName_1149_, v___x_1154_);
v___x_1156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1155_, v_declName_1149_);
lean_dec(v_declName_1149_);
lean_dec(v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_val_1157_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v___x_1153_, 1);
v___x_1158_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1152_, v_ext_1147_, v_env_1148_, v_val_1157_, v_level_1151_);
lean_dec(v_val_1157_);
lean_dec_ref(v_env_1148_);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_array_get_size(v___x_1158_);
v___x_1161_ = lean_nat_dec_lt(v___x_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_dec_ref(v___x_1158_);
lean_dec(v_declName_1149_);
lean_dec(v_inst_1146_);
v___x_1162_ = lean_box(0);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_sub(v___x_1160_, v___x_1163_);
v___x_1165_ = lean_nat_dec_le(v___x_1159_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec(v___x_1164_);
lean_dec_ref(v___x_1158_);
lean_dec(v_declName_1149_);
lean_dec(v_inst_1146_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___f_1167_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_declName_1149_);
lean_ctor_set(v___x_1168_, 1, v_inst_1146_);
v___x_1169_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1));
v___x_1170_ = l_Array_binSearchAux___redArg(v___f_1167_, v___x_1169_, v___x_1158_, v___x_1168_, v___x_1159_, v___x_1164_);
lean_dec_ref(v___x_1158_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_val_1172_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v___x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_val_1172_);
lean_dec(v___x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_snd_1176_; lean_object* v___x_1178_; 
v_snd_1176_ = lean_ctor_get(v_val_1172_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_val_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v_snd_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_snd_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_inst_1181_, lean_object* v_ext_1182_, lean_object* v_env_1183_, lean_object* v_declName_1184_, lean_object* v_asyncMode_1185_, lean_object* v_level_1186_){
_start:
{
uint8_t v_level_boxed_1187_; lean_object* v_res_1188_; 
v_level_boxed_1187_ = lean_unbox(v_level_1186_);
v_res_1188_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1181_, v_ext_1182_, v_env_1183_, v_declName_1184_, v_asyncMode_1185_, v_level_boxed_1187_);
lean_dec(v_asyncMode_1185_);
lean_dec_ref(v_ext_1182_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1189_, lean_object* v_inst_1190_, lean_object* v_ext_1191_, lean_object* v_env_1192_, lean_object* v_declName_1193_, lean_object* v_asyncMode_1194_, uint8_t v_level_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1190_, v_ext_1191_, v_env_1192_, v_declName_1193_, v_asyncMode_1194_, v_level_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_inst_1198_, lean_object* v_ext_1199_, lean_object* v_env_1200_, lean_object* v_declName_1201_, lean_object* v_asyncMode_1202_, lean_object* v_level_1203_){
_start:
{
uint8_t v_level_boxed_1204_; lean_object* v_res_1205_; 
v_level_boxed_1204_ = lean_unbox(v_level_1203_);
v_res_1205_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1197_, v_inst_1198_, v_ext_1199_, v_env_1200_, v_declName_1201_, v_asyncMode_1202_, v_level_boxed_1204_);
lean_dec(v_asyncMode_1202_);
lean_dec_ref(v_ext_1199_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_inst_1207_, lean_object* v_ext_1208_, lean_object* v_env_1209_, lean_object* v_declName_1210_, lean_object* v_asyncMode_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(1);
v___x_1213_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1209_, v_declName_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
uint8_t v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
lean_dec(v_inst_1207_);
v___x_1214_ = 0;
lean_inc(v_declName_1210_);
v___x_1215_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1212_, v_ext_1208_, v_env_1209_, v_asyncMode_1211_, v_declName_1210_, v___x_1214_);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1210_, v___x_1215_);
lean_dec(v___x_1215_);
lean_dec(v_declName_1210_);
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_val_1217_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1218_ = 0;
v___x_1219_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1212_, v_ext_1208_, v_env_1209_, v_val_1217_, v___x_1218_);
lean_dec(v_val_1217_);
lean_dec_ref(v_env_1209_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_array_get_size(v___x_1219_);
v___x_1222_ = lean_nat_dec_lt(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_dec_ref(v___x_1219_);
lean_dec(v_declName_1210_);
lean_dec(v_inst_1207_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_sub(v___x_1221_, v___x_1223_);
v___x_1225_ = lean_nat_dec_le(v___x_1220_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_dec(v___x_1224_);
lean_dec_ref(v___x_1219_);
lean_dec(v_declName_1210_);
lean_dec(v_inst_1207_);
return v___x_1225_;
}
else
{
lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___f_1226_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_declName_1210_);
lean_ctor_set(v___x_1227_, 1, v_inst_1207_);
v___x_1228_ = ((lean_object*)(l_Lean_MapDeclarationExtension_contains___redArg___closed__0));
v___x_1229_ = l_Array_binSearchAux___redArg(v___f_1226_, v___x_1228_, v___x_1219_, v___x_1227_, v___x_1220_, v___x_1224_);
lean_dec_ref(v___x_1219_);
v___x_1230_ = lean_unbox(v___x_1229_);
lean_dec(v___x_1229_);
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_inst_1231_, lean_object* v_ext_1232_, lean_object* v_env_1233_, lean_object* v_declName_1234_, lean_object* v_asyncMode_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1231_, v_ext_1232_, v_env_1233_, v_declName_1234_, v_asyncMode_1235_);
lean_dec(v_asyncMode_1235_);
lean_dec_ref(v_ext_1232_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1238_, lean_object* v_inst_1239_, lean_object* v_ext_1240_, lean_object* v_env_1241_, lean_object* v_declName_1242_, lean_object* v_asyncMode_1243_){
_start:
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1239_, v_ext_1240_, v_env_1241_, v_declName_1242_, v_asyncMode_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1245_, lean_object* v_inst_1246_, lean_object* v_ext_1247_, lean_object* v_env_1248_, lean_object* v_declName_1249_, lean_object* v_asyncMode_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1245_, v_inst_1246_, v_ext_1247_, v_env_1248_, v_declName_1249_, v_asyncMode_1250_);
lean_dec(v_asyncMode_1250_);
lean_dec_ref(v_ext_1247_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
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
