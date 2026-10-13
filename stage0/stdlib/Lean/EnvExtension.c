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
lean_object* v_name_295_; lean_object* v_addEntryFn_296_; lean_object* v_addImportedFn_297_; lean_object* v_toArrayFn_298_; lean_object* v_exportEntriesFnEx_x3f_299_; lean_object* v_asyncMode_300_; lean_object* v_replay_x3f_301_; uint8_t v_logWrites_302_; lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___y_314_; 
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
v_logWrites_302_ = lean_ctor_get_uint8(v_descr_293_, sizeof(void*)*7);
lean_dec_ref(v_descr_293_);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__0), 3, 1);
lean_closure_set(v___f_303_, 0, v_addEntryFn_296_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__1), 4, 2);
lean_closure_set(v___f_304_, 0, v_exportEntriesFnEx_x3f_299_);
lean_closure_set(v___f_304_, 1, v_toArrayFn_298_);
v___f_305_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__0));
v___f_306_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__1));
v___x_307_ = lean_box(0);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_308_, 0, v_addImportedFn_297_);
lean_closure_set(v___f_308_, 1, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_registerSimplePersistentEnvExtension___redArg___closed__2));
v___x_310_ = lean_apply_1(v_addImportedFn_297_, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_307_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_312_, 0, lean_box(0));
lean_closure_set(v___x_312_, 1, lean_box(0));
lean_closure_set(v___x_312_, 2, v___x_311_);
if (lean_obj_tag(v_replay_x3f_301_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
v___y_314_ = v___x_319_;
goto v___jp_313_;
}
else
{
lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_val_320_ = lean_ctor_get(v_replay_x3f_301_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_replay_x3f_301_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v_replay_x3f_301_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_dec(v_replay_x3f_301_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___f_324_; lean_object* v___x_326_; 
v___f_324_ = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___redArg___lam__5___boxed), 5, 1);
lean_closure_set(v___f_324_, 0, v_val_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___f_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___f_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
}
}
v___jp_313_:
{
uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = 0;
v___x_316_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_316_, 0, v_name_295_);
lean_ctor_set(v___x_316_, 1, v___x_312_);
lean_ctor_set(v___x_316_, 2, v___f_308_);
lean_ctor_set(v___x_316_, 3, v___f_303_);
lean_ctor_set(v___x_316_, 4, v___f_304_);
lean_ctor_set(v___x_316_, 5, v___f_305_);
lean_ctor_set(v___x_316_, 6, v_asyncMode_300_);
lean_ctor_set(v___x_316_, 7, v___y_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*8, v___x_315_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*8 + 1, v_logWrites_302_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___f_306_);
v___x_318_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg___boxed(lean_object* v_descr_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object* v_00_u03b1_332_, lean_object* v_00_u03c3_333_, lean_object* v_inst_334_, lean_object* v_descr_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v_descr_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___boxed(lean_object* v_00_u03b1_338_, lean_object* v_00_u03c3_339_, lean_object* v_inst_340_, lean_object* v_descr_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_registerSimplePersistentEnvExtension(v_00_u03b1_338_, v_00_u03c3_339_, v_inst_340_, v_descr_341_);
lean_dec(v_inst_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object* v_x_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_352_, v___y_353_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v_x_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(lean_object* v_s_356_, lean_object* v_x_357_){
_start:
{
lean_inc_ref(v_s_356_);
return v_s_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1___boxed(lean_object* v_s_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__1(v_s_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec_ref(v_s_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0));
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__2(v_x_366_, v_x_367_);
lean_dec_ref(v_x_367_);
lean_dec_ref(v_x_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3___boxed(lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__3(v_x_371_);
lean_dec_ref(v_x_371_);
return v_res_372_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_377_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5(void){
_start:
{
lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___f_378_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__3));
v___f_379_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__2));
v___f_380_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__1));
v___f_381_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__0));
v___x_382_ = lean_box(0);
v___x_383_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_384_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___f_381_);
lean_ctor_set(v___x_384_, 3, v___f_380_);
lean_ctor_set(v___x_384_, 4, v___f_379_);
lean_ctor_set(v___x_384_, 5, v___f_378_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg();
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1(lean_object* v_00_u03b1_389_, lean_object* v_00_u03c3_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg(){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__5);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___redArg___boxed(lean_object* v___dummy_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v_res_395_;
}
}
static lean_object* _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_SimplePersistentEnvExtension_instInhabited___redArg();
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited(lean_object* v_00_u03b1_397_, lean_object* v_00_u03c3_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0, &l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___closed__0);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_instInhabited___boxed(lean_object* v_00_u03b1_401_, lean_object* v_00_u03c3_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_SimplePersistentEnvExtension_instInhabited(v_00_u03b1_401_, v_00_u03c3_402_, v_inst_403_);
lean_dec(v_inst_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object* v_inst_405_, lean_object* v_ext_406_, lean_object* v_env_407_, lean_object* v_asyncMode_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v_fst_414_; 
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_inst_405_);
v___x_411_ = lean_box(0);
v___x_412_ = 0;
v___x_413_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_410_, v_ext_406_, v_env_407_, v_asyncMode_408_, v___x_411_, v___x_412_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_fst_414_);
lean_dec(v___x_413_);
return v_fst_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg___boxed(lean_object* v_inst_415_, lean_object* v_ext_416_, lean_object* v_env_417_, lean_object* v_asyncMode_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_415_, v_ext_416_, v_env_417_, v_asyncMode_418_);
lean_dec(v_asyncMode_418_);
lean_dec_ref(v_ext_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries(lean_object* v_00_u03b1_420_, lean_object* v_00_u03c3_421_, lean_object* v_inst_422_, lean_object* v_ext_423_, lean_object* v_env_424_, lean_object* v_asyncMode_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v_inst_422_, v_ext_423_, v_env_424_, v_asyncMode_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___boxed(lean_object* v_00_u03b1_427_, lean_object* v_00_u03c3_428_, lean_object* v_inst_429_, lean_object* v_ext_430_, lean_object* v_env_431_, lean_object* v_asyncMode_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_SimplePersistentEnvExtension_getEntries(v_00_u03b1_427_, v_00_u03c3_428_, v_inst_429_, v_ext_430_, v_env_431_, v_asyncMode_432_);
lean_dec(v_asyncMode_432_);
lean_dec_ref(v_ext_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object* v_inst_434_, lean_object* v_ext_435_, lean_object* v_env_436_, lean_object* v_asyncMode_437_, lean_object* v_asyncDecl_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v_snd_443_; 
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_inst_434_);
v___x_441_ = 0;
v___x_442_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_440_, v_ext_435_, v_env_436_, v_asyncMode_437_, v_asyncDecl_438_, v___x_441_);
v_snd_443_ = lean_ctor_get(v___x_442_, 1);
lean_inc(v_snd_443_);
lean_dec(v___x_442_);
return v_snd_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg___boxed(lean_object* v_inst_444_, lean_object* v_ext_445_, lean_object* v_env_446_, lean_object* v_asyncMode_447_, lean_object* v_asyncDecl_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_444_, v_ext_445_, v_env_446_, v_asyncMode_447_, v_asyncDecl_448_);
lean_dec(v_asyncMode_447_);
lean_dec_ref(v_ext_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object* v_00_u03b1_450_, lean_object* v_00_u03c3_451_, lean_object* v_inst_452_, lean_object* v_ext_453_, lean_object* v_env_454_, lean_object* v_asyncMode_455_, lean_object* v_asyncDecl_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v_inst_452_, v_ext_453_, v_env_454_, v_asyncMode_455_, v_asyncDecl_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___boxed(lean_object* v_00_u03b1_458_, lean_object* v_00_u03c3_459_, lean_object* v_inst_460_, lean_object* v_ext_461_, lean_object* v_env_462_, lean_object* v_asyncMode_463_, lean_object* v_asyncDecl_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_SimplePersistentEnvExtension_getState(v_00_u03b1_458_, v_00_u03c3_459_, v_inst_460_, v_ext_461_, v_env_462_, v_asyncMode_463_, v_asyncDecl_464_);
lean_dec(v_asyncMode_463_);
lean_dec_ref(v_ext_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0(lean_object* v_s_466_, lean_object* v_ps_467_){
_start:
{
lean_object* v_state_468_; lean_object* v_importedEntries_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_485_; 
v_state_468_ = lean_ctor_get(v_ps_467_, 1);
v_importedEntries_469_ = lean_ctor_get(v_ps_467_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_ps_467_);
if (v_isSharedCheck_485_ == 0)
{
v___x_471_ = v_ps_467_;
v_isShared_472_ = v_isSharedCheck_485_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_state_468_);
lean_inc(v_importedEntries_469_);
lean_dec(v_ps_467_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_485_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_fst_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_483_; 
v_fst_473_ = lean_ctor_get(v_state_468_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_state_468_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_state_468_, 1);
lean_dec(v_unused_484_);
v___x_475_ = v_state_468_;
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_fst_473_);
lean_dec(v_state_468_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_s_466_);
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fst_473_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_s_466_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_478_);
v___x_480_ = v___x_471_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_importedEntries_469_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object* v_ext_486_, lean_object* v_env_487_, lean_object* v_s_488_){
_start:
{
lean_object* v_toEnvExtension_489_; lean_object* v_asyncMode_490_; uint8_t v_logWrites_491_; lean_object* v___f_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_toEnvExtension_489_ = lean_ctor_get(v_ext_486_, 0);
lean_inc_ref(v_toEnvExtension_489_);
lean_dec_ref(v_ext_486_);
v_asyncMode_490_ = lean_ctor_get(v_toEnvExtension_489_, 2);
lean_inc(v_asyncMode_490_);
v_logWrites_491_ = lean_ctor_get_uint8(v_toEnvExtension_489_, sizeof(void*)*6);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_setState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_492_, 0, v_s_488_);
v___x_493_ = lean_box(0);
v___x_494_ = 1;
if (v_logWrites_491_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_489_, v_env_487_, v___f_492_, v_asyncMode_490_, v___x_493_, v___x_494_);
lean_dec(v_asyncMode_490_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_inc_ref(v_toEnvExtension_489_);
v___x_496_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_489_, v_env_487_);
lean_dec_ref(v_env_487_);
v___x_497_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_489_, v___x_496_, v___f_492_, v_asyncMode_490_, v___x_493_, v___x_494_);
lean_dec(v_asyncMode_490_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_setState(lean_object* v_00_u03b1_498_, lean_object* v_00_u03c3_499_, lean_object* v_ext_500_, lean_object* v_env_501_, lean_object* v_s_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v_ext_500_, v_env_501_, v_s_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_504_, lean_object* v_ps_505_){
_start:
{
lean_object* v_state_506_; lean_object* v_importedEntries_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_524_; 
v_state_506_ = lean_ctor_get(v_ps_505_, 1);
v_importedEntries_507_ = lean_ctor_get(v_ps_505_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_ps_505_);
if (v_isSharedCheck_524_ == 0)
{
v___x_509_ = v_ps_505_;
v_isShared_510_ = v_isSharedCheck_524_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_state_506_);
lean_inc(v_importedEntries_507_);
lean_dec(v_ps_505_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_524_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_523_; 
v_fst_511_ = lean_ctor_get(v_state_506_, 0);
v_snd_512_ = lean_ctor_get(v_state_506_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_state_506_);
if (v_isSharedCheck_523_ == 0)
{
v___x_514_ = v_state_506_;
v_isShared_515_ = v_isSharedCheck_523_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_511_);
lean_dec(v_state_506_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_523_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_apply_1(v_f_504_, v_snd_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_fst_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_518_);
v___x_520_ = v___x_509_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_importedEntries_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___redArg(lean_object* v_ext_525_, lean_object* v_env_526_, lean_object* v_f_527_){
_start:
{
lean_object* v_toEnvExtension_528_; lean_object* v_asyncMode_529_; uint8_t v_logWrites_530_; lean_object* v___f_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_toEnvExtension_528_ = lean_ctor_get(v_ext_525_, 0);
lean_inc_ref(v_toEnvExtension_528_);
lean_dec_ref(v_ext_525_);
v_asyncMode_529_ = lean_ctor_get(v_toEnvExtension_528_, 2);
lean_inc(v_asyncMode_529_);
v_logWrites_530_ = lean_ctor_get_uint8(v_toEnvExtension_528_, sizeof(void*)*6);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_531_, 0, v_f_527_);
v___x_532_ = lean_box(0);
v___x_533_ = 1;
if (v_logWrites_530_ == 0)
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_528_, v_env_526_, v___f_531_, v_asyncMode_529_, v___x_532_, v___x_533_);
lean_dec(v_asyncMode_529_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_inc_ref(v_toEnvExtension_528_);
v___x_535_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_528_, v_env_526_);
lean_dec_ref(v_env_526_);
v___x_536_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_528_, v___x_535_, v___f_531_, v_asyncMode_529_, v___x_532_, v___x_533_);
lean_dec(v_asyncMode_529_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_modifyState(lean_object* v_00_u03b1_537_, lean_object* v_00_u03c3_538_, lean_object* v_ext_539_, lean_object* v_env_540_, lean_object* v_f_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_SimplePersistentEnvExtension_modifyState___redArg(v_ext_539_, v_env_540_, v_f_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_NameSet_empty;
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_546_);
lean_dec_ref(v_x_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object* v_hi_548_, lean_object* v_pivot_549_, lean_object* v_as_550_, lean_object* v_i_551_, lean_object* v_k_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = lean_nat_dec_lt(v_k_552_, v_hi_548_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v_k_552_);
v___x_554_ = lean_array_fswap(v_as_550_, v_i_551_, v_hi_548_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_i_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_fget_borrowed(v_as_550_, v_k_552_);
v___x_557_ = l_Lean_Name_quickLt(v___x_556_, v_pivot_549_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_k_552_, v___x_558_);
lean_dec(v_k_552_);
v_k_552_ = v___x_559_;
goto _start;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = lean_array_fswap(v_as_550_, v_i_551_, v_k_552_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_i_551_, v___x_562_);
lean_dec(v_i_551_);
v___x_564_ = lean_nat_add(v_k_552_, v___x_562_);
lean_dec(v_k_552_);
v_as_550_ = v___x_561_;
v_i_551_ = v___x_563_;
v_k_552_ = v___x_564_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object* v_hi_566_, lean_object* v_pivot_567_, lean_object* v_as_568_, lean_object* v_i_569_, lean_object* v_k_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_566_, v_pivot_567_, v_as_568_, v_i_569_, v_k_570_);
lean_dec(v_pivot_567_);
lean_dec(v_hi_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_n_572_, lean_object* v_as_573_, lean_object* v_lo_574_, lean_object* v_hi_575_){
_start:
{
lean_object* v___y_577_; uint8_t v___x_587_; 
v___x_587_ = lean_nat_dec_lt(v_lo_574_, v_hi_575_);
if (v___x_587_ == 0)
{
lean_dec(v_lo_574_);
return v_as_573_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_mid_590_; lean_object* v___y_592_; lean_object* v___y_598_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_588_ = lean_nat_add(v_lo_574_, v_hi_575_);
v___x_589_ = lean_unsigned_to_nat(1u);
v_mid_590_ = lean_nat_shiftr(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
v___x_603_ = lean_array_fget_borrowed(v_as_573_, v_mid_590_);
v___x_604_ = lean_array_fget_borrowed(v_as_573_, v_lo_574_);
v___x_605_ = l_Lean_Name_quickLt(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
v___y_598_ = v_as_573_;
goto v___jp_597_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_array_fswap(v_as_573_, v_lo_574_, v_mid_590_);
v___y_598_ = v___x_606_;
goto v___jp_597_;
}
v___jp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_array_fget_borrowed(v___y_592_, v_mid_590_);
v___x_594_ = lean_array_fget_borrowed(v___y_592_, v_hi_575_);
v___x_595_ = l_Lean_Name_quickLt(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec(v_mid_590_);
v___y_577_ = v___y_592_;
goto v___jp_576_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_array_fswap(v___y_592_, v_mid_590_, v_hi_575_);
lean_dec(v_mid_590_);
v___y_577_ = v___x_596_;
goto v___jp_576_;
}
}
v___jp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = lean_array_fget_borrowed(v___y_598_, v_hi_575_);
v___x_600_ = lean_array_fget_borrowed(v___y_598_, v_lo_574_);
v___x_601_ = l_Lean_Name_quickLt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
v___y_592_ = v___y_598_;
goto v___jp_591_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_array_fswap(v___y_598_, v_lo_574_, v_hi_575_);
v___y_592_ = v___x_602_;
goto v___jp_591_;
}
}
}
v___jp_576_:
{
lean_object* v_pivot_578_; lean_object* v___x_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; uint8_t v___x_582_; 
v_pivot_578_ = lean_array_fget(v___y_577_, v_hi_575_);
lean_inc_n(v_lo_574_, 2);
v___x_579_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_575_, v_pivot_578_, v___y_577_, v_lo_574_, v_lo_574_);
lean_dec(v_pivot_578_);
v_fst_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_fst_580_);
v_snd_581_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_snd_581_);
lean_dec_ref(v___x_579_);
v___x_582_ = lean_nat_dec_le(v_hi_575_, v_fst_580_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_572_, v_snd_581_, v_lo_574_, v_fst_580_);
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_fst_580_, v___x_584_);
lean_dec(v_fst_580_);
v_as_573_ = v___x_583_;
v_lo_574_ = v___x_585_;
goto _start;
}
else
{
lean_dec(v_fst_580_);
lean_dec(v_lo_574_);
return v_snd_581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_n_607_, lean_object* v_as_608_, lean_object* v_lo_609_, lean_object* v_hi_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_607_, v_as_608_, v_lo_609_, v_hi_610_);
lean_dec(v_hi_610_);
lean_dec(v_n_607_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_613_ = lean_array_mk(v_es_612_);
v___x_614_ = lean_array_get_size(v___x_613_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___y_620_; uint8_t v___x_624_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_sub(v___x_614_, v___x_617_);
v___x_624_ = lean_nat_dec_le(v___x_615_, v___x_618_);
if (v___x_624_ == 0)
{
lean_inc(v___x_618_);
v___y_620_ = v___x_618_;
goto v___jp_619_;
}
else
{
v___y_620_ = v___x_615_;
goto v___jp_619_;
}
v___jp_619_:
{
uint8_t v___x_621_; 
v___x_621_ = lean_nat_dec_le(v___y_620_, v___x_618_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v___x_618_);
lean_inc(v___y_620_);
v___x_622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_614_, v___x_613_, v___y_620_, v___y_620_);
lean_dec(v___y_620_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_614_, v___x_613_, v___y_620_, v___x_618_);
lean_dec(v___x_618_);
return v___x_623_;
}
}
}
else
{
return v___x_613_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_625_, lean_object* v_x2_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_NameSet_contains(v_x1_625_, v_x2_626_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
v___x_628_ = 1;
return v___x_628_;
}
else
{
uint8_t v___x_629_; 
v___x_629_ = 0;
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_630_, lean_object* v_x2_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_630_, v_x2_631_);
lean_dec(v_x2_631_);
lean_dec(v_x1_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_643_, lean_object* v_asyncMode_644_, uint8_t v_logWrites_645_){
_start:
{
lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___f_647_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_648_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_649_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_650_ = lean_box(0);
v___x_651_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_652_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_652_, 0, v_name_643_);
lean_ctor_set(v___x_652_, 1, v___f_647_);
lean_ctor_set(v___x_652_, 2, v___f_648_);
lean_ctor_set(v___x_652_, 3, v___f_649_);
lean_ctor_set(v___x_652_, 4, v___x_650_);
lean_ctor_set(v___x_652_, 5, v_asyncMode_644_);
lean_ctor_set(v___x_652_, 6, v___x_651_);
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*7, v_logWrites_645_);
v___x_653_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_654_, lean_object* v_asyncMode_655_, lean_object* v_logWrites_656_, lean_object* v_a_657_){
_start:
{
uint8_t v_logWrites_boxed_658_; lean_object* v_res_659_; 
v_logWrites_boxed_658_ = lean_unbox(v_logWrites_656_);
v_res_659_ = l_Lean_mkTagDeclarationExtension(v_name_654_, v_asyncMode_655_, v_logWrites_boxed_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_660_, lean_object* v_as_661_, lean_object* v_lo_662_, lean_object* v_hi_663_, lean_object* v_w_664_, lean_object* v_hlo_665_, lean_object* v_hhi_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_660_, v_as_661_, v_lo_662_, v_hi_663_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_668_, lean_object* v_as_669_, lean_object* v_lo_670_, lean_object* v_hi_671_, lean_object* v_w_672_, lean_object* v_hlo_673_, lean_object* v_hhi_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_668_, v_as_669_, v_lo_670_, v_hi_671_, v_w_672_, v_hlo_673_, v_hhi_674_);
lean_dec(v_hi_671_);
lean_dec(v_n_668_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object* v_n_676_, lean_object* v_lo_677_, lean_object* v_hi_678_, lean_object* v_hhi_679_, lean_object* v_pivot_680_, lean_object* v_as_681_, lean_object* v_i_682_, lean_object* v_k_683_, lean_object* v_ilo_684_, lean_object* v_ik_685_, lean_object* v_w_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_678_, v_pivot_680_, v_as_681_, v_i_682_, v_k_683_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object* v_n_688_, lean_object* v_lo_689_, lean_object* v_hi_690_, lean_object* v_hhi_691_, lean_object* v_pivot_692_, lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_k_695_, lean_object* v_ilo_696_, lean_object* v_ik_697_, lean_object* v_w_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_688_, v_lo_689_, v_hi_690_, v_hhi_691_, v_pivot_692_, v_as_693_, v_i_694_, v_k_695_, v_ilo_696_, v_ik_697_, v_w_698_);
lean_dec(v_pivot_692_);
lean_dec(v_hi_690_);
lean_dec(v_lo_689_);
lean_dec(v_n_688_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_705_, v___y_706_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_x_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_709_, lean_object* v_x_710_){
_start:
{
lean_inc_ref(v_s_709_);
return v_s_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_711_, lean_object* v_x_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_711_, v_x_712_);
lean_dec(v_x_712_);
lean_dec_ref(v_s_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1));
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_721_, v_x_722_);
lean_dec_ref(v_x_722_);
lean_dec_ref(v_x_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_726_);
lean_dec_ref(v_x_726_);
return v_res_727_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___f_732_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_733_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_734_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_735_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_736_ = lean_box(0);
v___x_737_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_738_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
lean_ctor_set(v___x_738_, 2, v___f_735_);
lean_ctor_set(v___x_738_, 3, v___f_734_);
lean_ctor_set(v___x_738_, 4, v___f_733_);
lean_ctor_set(v___x_738_, 5, v___f_732_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_741_, lean_object* v_msg_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_panic_fn_borrowed(v_env_741_, v_msg_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object* v_env_744_, lean_object* v_msg_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_744_, v_msg_745_);
lean_dec_ref(v_env_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag___lam__0(lean_object* v_ext_747_, lean_object* v_declName_748_, lean_object* v_s_749_){
_start:
{
lean_object* v_addEntryFn_750_; lean_object* v_importedEntries_751_; lean_object* v_state_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_addEntryFn_750_ = lean_ctor_get(v_ext_747_, 3);
lean_inc(v_addEntryFn_750_);
lean_dec_ref(v_ext_747_);
v_importedEntries_751_ = lean_ctor_get(v_s_749_, 0);
v_state_752_ = lean_ctor_get(v_s_749_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_s_749_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v_s_749_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_state_752_);
lean_inc(v_importedEntries_751_);
lean_dec(v_s_749_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_state_756_; lean_object* v___x_758_; 
v_state_756_ = lean_apply_2(v_addEntryFn_750_, v_state_752_, v_declName_748_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_state_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_importedEntries_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_state_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_764_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_765_ = lean_unsigned_to_nat(4u);
v___x_766_ = lean_unsigned_to_nat(120u);
v___x_767_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_768_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_769_ = l_mkPanicMessageWithDecl(v___x_768_, v___x_767_, v___x_766_, v___x_765_, v___x_764_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_770_, lean_object* v_env_771_, lean_object* v_declName_772_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = l_Lean_Name_isAnonymous(v_declName_772_);
if (v___x_773_ == 0)
{
lean_object* v___f_774_; lean_object* v___x_775_; uint8_t v___y_777_; lean_object* v___x_789_; 
lean_inc(v_declName_772_);
lean_inc_ref(v_ext_770_);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_TagDeclarationExtension_tag___lam__0), 3, 2);
lean_closure_set(v___f_774_, 0, v_ext_770_);
lean_closure_set(v___f_774_, 1, v_declName_772_);
v___x_775_ = lean_box(1);
v___x_789_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_771_, v_declName_772_);
if (lean_obj_tag(v___x_789_) == 0)
{
uint8_t v___x_790_; 
v___x_790_ = 1;
v___y_777_ = v___x_790_;
goto v___jp_776_;
}
else
{
lean_dec_ref_known(v___x_789_, 1);
if (v___x_773_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v___f_774_);
lean_dec(v_declName_772_);
lean_dec_ref(v_ext_770_);
v___x_791_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_792_ = lean_panic_fn_borrowed(v_env_771_, v___x_791_);
lean_dec_ref(v_env_771_);
return v___x_792_;
}
else
{
v___y_777_ = v___x_773_;
goto v___jp_776_;
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_778_ = lean_box(1);
v___x_779_ = lean_box(0);
lean_inc_ref(v_env_771_);
v___x_780_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_775_, v_ext_770_, v_env_771_, v___x_778_, v___x_779_);
v___x_781_ = l_Lean_NameSet_contains(v___x_780_, v_declName_772_);
lean_dec(v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v_toEnvExtension_782_; uint8_t v_logWrites_783_; 
v_toEnvExtension_782_ = lean_ctor_get(v_ext_770_, 0);
lean_inc_ref(v_toEnvExtension_782_);
lean_dec_ref(v_ext_770_);
v_logWrites_783_ = lean_ctor_get_uint8(v_toEnvExtension_782_, sizeof(void*)*6);
if (v_logWrites_783_ == 0)
{
lean_object* v_asyncMode_784_; lean_object* v___x_785_; 
v_asyncMode_784_ = lean_ctor_get(v_toEnvExtension_782_, 2);
lean_inc(v_asyncMode_784_);
v___x_785_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_782_, v_env_771_, v___f_774_, v_asyncMode_784_, v_declName_772_, v___y_777_);
lean_dec(v_asyncMode_784_);
return v___x_785_;
}
else
{
lean_object* v_asyncMode_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_asyncMode_786_ = lean_ctor_get(v_toEnvExtension_782_, 2);
lean_inc(v_asyncMode_786_);
lean_inc(v_declName_772_);
v___x_787_ = l_Lean_Environment_logDeclChange(v_env_771_, v_declName_772_);
v___x_788_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_782_, v___x_787_, v___f_774_, v_asyncMode_786_, v_declName_772_, v___y_777_);
lean_dec(v_asyncMode_786_);
return v___x_788_;
}
}
else
{
lean_dec_ref(v___f_774_);
lean_dec(v_declName_772_);
lean_dec_ref(v_ext_770_);
return v_env_771_;
}
}
}
else
{
lean_dec(v_declName_772_);
lean_dec_ref(v_ext_770_);
return v_env_771_;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object* v___y_793_, lean_object* v_as_794_, lean_object* v_k_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_m_800_; lean_object* v_a_801_; uint8_t v___x_802_; 
v___x_798_ = lean_nat_add(v_x_796_, v_x_797_);
v___x_799_ = lean_unsigned_to_nat(1u);
v_m_800_ = lean_nat_shiftr(v___x_798_, v___x_799_);
lean_dec(v___x_798_);
v_a_801_ = lean_array_fget_borrowed(v_as_794_, v_m_800_);
v___x_802_ = l_Lean_Name_quickLt(v_a_801_, v_k_795_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; uint8_t v___x_804_; 
lean_dec(v_x_797_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = l_Lean_Name_quickLt(v_k_795_, v_a_801_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
lean_dec(v_m_800_);
lean_dec(v_x_796_);
v___x_805_ = lean_nat_dec_le(v___x_803_, v___y_793_);
return v___x_805_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = lean_nat_dec_eq(v_m_800_, v___x_803_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_nat_sub(v_m_800_, v___x_799_);
lean_dec(v_m_800_);
v___x_808_ = lean_nat_dec_lt(v___x_807_, v_x_796_);
if (v___x_808_ == 0)
{
v_x_797_ = v___x_807_;
goto _start;
}
else
{
lean_dec(v___x_807_);
lean_dec(v_x_796_);
return v___x_806_;
}
}
else
{
lean_dec(v_m_800_);
lean_dec(v_x_796_);
return v___x_802_;
}
}
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
lean_dec(v_x_796_);
v___x_810_ = lean_nat_add(v_m_800_, v___x_799_);
lean_dec(v_m_800_);
v___x_811_ = lean_nat_dec_le(v___x_810_, v_x_797_);
if (v___x_811_ == 0)
{
lean_dec(v___x_810_);
lean_dec(v_x_797_);
return v___x_811_;
}
else
{
v_x_796_ = v___x_810_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg___boxed(lean_object* v___y_813_, lean_object* v_as_814_, lean_object* v_k_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_813_, v_as_814_, v_k_815_, v_x_816_, v_x_817_);
lean_dec(v_k_815_);
lean_dec_ref(v_as_814_);
lean_dec(v___y_813_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_823_, lean_object* v_env_824_, lean_object* v_declName_825_, lean_object* v_asyncMode_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_box(1);
v___x_828_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_824_, v_declName_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; uint8_t v___x_830_; 
lean_inc(v_declName_825_);
v___x_829_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_827_, v_ext_823_, v_env_824_, v_asyncMode_826_, v_declName_825_);
v___x_830_ = l_Lean_NameSet_contains(v___x_829_, v_declName_825_);
lean_dec(v_declName_825_);
lean_dec(v___x_829_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_val_831_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_828_, 1);
v___x_832_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_833_ = 0;
v___x_834_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_832_, v_ext_823_, v_env_824_, v_val_831_, v___x_833_);
lean_dec(v_val_831_);
lean_dec_ref(v_env_824_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_array_get_size(v___x_834_);
v___x_837_ = lean_nat_dec_lt(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v___x_834_);
lean_dec(v_declName_825_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_sub(v___x_836_, v___x_838_);
v___x_840_ = lean_nat_dec_le(v___x_835_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v___x_839_);
lean_dec_ref(v___x_834_);
lean_dec(v_declName_825_);
return v___x_840_;
}
else
{
uint8_t v___x_841_; 
lean_inc(v___x_839_);
v___x_841_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___x_839_, v___x_834_, v_declName_825_, v___x_835_, v___x_839_);
lean_dec(v_declName_825_);
lean_dec_ref(v___x_834_);
lean_dec(v___x_839_);
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_842_, lean_object* v_env_843_, lean_object* v_declName_844_, lean_object* v_asyncMode_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_842_, v_env_843_, v_declName_844_, v_asyncMode_845_);
lean_dec(v_asyncMode_845_);
lean_dec_ref(v_ext_842_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(lean_object* v___y_848_, lean_object* v_as_849_, lean_object* v_k_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(v___y_848_, v_as_849_, v_k_850_, v_x_851_, v_x_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___boxed(lean_object* v___y_855_, lean_object* v_as_856_, lean_object* v_k_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
uint8_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0(v___y_855_, v_as_856_, v_k_857_, v_x_858_, v_x_859_, v_x_860_);
lean_dec(v_k_857_);
lean_dec_ref(v_as_856_);
lean_dec(v___y_855_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(lean_object* v_x_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed(lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(v_x_868_, v___y_869_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v_x_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(lean_object* v_s_872_, lean_object* v_x_873_){
_start:
{
lean_inc(v_s_872_);
return v_s_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed(lean_object* v_s_874_, lean_object* v_x_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(v_s_874_, v_x_875_);
lean_dec_ref(v_x_875_);
lean_dec(v_s_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1));
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed(lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(v_x_884_, v_x_885_);
lean_dec(v_x_885_);
lean_dec_ref(v_x_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_box(0);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed(lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(v_x_889_);
lean_dec(v_x_889_);
return v_res_890_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___f_895_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_896_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2));
v___f_897_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1));
v___f_898_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0));
v___x_899_ = lean_box(0);
v___x_900_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_901_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___f_898_);
lean_ctor_set(v___x_901_, 3, v___f_897_);
lean_ctor_set(v___x_901_, 4, v___f_896_);
lean_ctor_set(v___x_901_, 5, v___f_895_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg(){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___boxed(lean_object* v___dummy_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v_res_905_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0(void){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_00_u03b1_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg(){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg___boxed(lean_object* v___dummy_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_instInhabitedMapDeclarationExtension___redArg();
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_916_, lean_object* v_x_917_){
_start:
{
lean_object* v_fst_918_; lean_object* v_snd_919_; lean_object* v___x_920_; 
v_fst_918_ = lean_ctor_get(v_x_917_, 0);
lean_inc(v_fst_918_);
v_snd_919_ = lean_ctor_get(v_x_917_, 1);
lean_inc(v_snd_919_);
lean_dec_ref(v_x_917_);
v___x_920_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_918_, v_snd_919_, v_s_916_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_921_, lean_object* v_env_922_, lean_object* v_s_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_apply_2(v_exportEntriesFn_921_, v_env_922_, v_s_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
return v_x_926_;
}
else
{
lean_object* v_head_928_; lean_object* v_tail_929_; lean_object* v___x_930_; 
v_head_928_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_head_928_);
v_tail_929_ = lean_ctor_get(v_x_927_, 1);
lean_inc(v_tail_929_);
lean_dec_ref_known(v_x_927_, 2);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_925_, v_head_928_);
if (lean_obj_tag(v___x_930_) == 1)
{
lean_object* v_val_931_; lean_object* v___x_932_; 
v_val_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_928_, v_val_931_, v_x_926_);
v_x_926_ = v___x_932_;
v_x_927_ = v_tail_929_;
goto _start;
}
else
{
lean_dec(v___x_930_);
lean_dec(v_head_928_);
v_x_927_ = v_tail_929_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_935_, v_x_936_, v_x_937_);
lean_dec(v_newState_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_939_, lean_object* v_newState_940_, lean_object* v_newConsts_941_, lean_object* v_s_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_940_, v_s_942_, v_newConsts_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_944_, lean_object* v_newState_945_, lean_object* v_newConsts_946_, lean_object* v_s_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_944_, v_newState_945_, v_newConsts_946_, v_s_947_);
lean_dec(v_newState_945_);
lean_dec(v_x_944_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0));
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_951_);
lean_dec(v_x_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_959_, lean_object* v_x_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_964_, v_x_965_, v___y_966_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_x_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_978_, lean_object* v_asyncMode_979_, uint8_t v_logWrites_980_, lean_object* v_exportEntriesFn_981_){
_start:
{
lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___f_983_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_984_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1), 3, 1);
lean_closure_set(v___f_984_, 0, v_exportEntriesFn_981_);
v___f_985_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_986_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_987_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_988_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_989_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_990_ = 0;
v___x_991_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_991_, 0, v_name_978_);
lean_ctor_set(v___x_991_, 1, v___f_987_);
lean_ctor_set(v___x_991_, 2, v___f_988_);
lean_ctor_set(v___x_991_, 3, v___f_983_);
lean_ctor_set(v___x_991_, 4, v___f_984_);
lean_ctor_set(v___x_991_, 5, v___f_985_);
lean_ctor_set(v___x_991_, 6, v_asyncMode_979_);
lean_ctor_set(v___x_991_, 7, v___x_989_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*8, v___x_990_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*8 + 1, v_logWrites_980_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___f_986_);
v___x_993_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_993_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_993_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_1010_, lean_object* v_asyncMode_1011_, lean_object* v_logWrites_1012_, lean_object* v_exportEntriesFn_1013_, lean_object* v_a_1014_){
_start:
{
uint8_t v_logWrites_boxed_1015_; lean_object* v_res_1016_; 
v_logWrites_boxed_1015_ = lean_unbox(v_logWrites_1012_);
v_res_1016_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1010_, v_asyncMode_1011_, v_logWrites_boxed_1015_, v_exportEntriesFn_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_1017_, lean_object* v_name_1018_, lean_object* v_asyncMode_1019_, uint8_t v_logWrites_1020_, lean_object* v_exportEntriesFn_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1018_, v_asyncMode_1019_, v_logWrites_1020_, v_exportEntriesFn_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_name_1025_, lean_object* v_asyncMode_1026_, lean_object* v_logWrites_1027_, lean_object* v_exportEntriesFn_1028_, lean_object* v_a_1029_){
_start:
{
uint8_t v_logWrites_boxed_1030_; lean_object* v_res_1031_; 
v_logWrites_boxed_1030_ = lean_unbox(v_logWrites_1027_);
v_res_1031_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_1024_, v_name_1025_, v_asyncMode_1026_, v_logWrites_boxed_1030_, v_exportEntriesFn_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_1032_, lean_object* v_newState_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_1033_, v_x_1034_, v_x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_1037_, lean_object* v_newState_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_1037_, v_newState_1038_, v_x_1039_, v_x_1040_);
lean_dec(v_newState_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___lam__0(lean_object* v_addEntryFn_1042_, lean_object* v___x_1043_, lean_object* v_s_1044_){
_start:
{
lean_object* v_importedEntries_1045_; lean_object* v_state_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_importedEntries_1045_ = lean_ctor_get(v_s_1044_, 0);
v_state_1046_ = lean_ctor_get(v_s_1044_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_s_1044_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v_s_1044_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_state_1046_);
lean_inc(v_importedEntries_1045_);
lean_dec(v_s_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_state_1050_; lean_object* v___x_1052_; 
v_state_1050_ = lean_apply_2(v_addEntryFn_1042_, v_state_1046_, v___x_1043_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_state_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_importedEntries_1045_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_state_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_1061_, lean_object* v_env_1062_, lean_object* v_declName_1063_, lean_object* v_val_1064_, uint8_t v_allowOverwrite_1065_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1062_, v_declName_1063_);
if (lean_obj_tag(v___x_1077_) == 1)
{
lean_object* v_val_1078_; lean_object* v_name_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_val_1064_);
v_val_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v_name_1079_ = lean_ctor_get(v_ext_1061_, 1);
lean_inc(v_name_1079_);
lean_dec_ref(v_ext_1061_);
v___x_1080_ = lean_box(0);
v___x_1081_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1082_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1083_ = lean_unsigned_to_nat(179u);
v___x_1084_ = lean_unsigned_to_nat(4u);
v___x_1085_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1086_ = 1;
v___x_1087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1063_, v___x_1086_);
v___x_1088_ = lean_string_append(v___x_1085_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
v___x_1091_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1079_, v___x_1086_);
v___x_1092_ = lean_string_append(v___x_1090_, v___x_1091_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
v___x_1095_ = l_Lean_Environment_allImportedModuleNames(v_env_1062_);
v___x_1096_ = lean_array_get(v___x_1080_, v___x_1095_, v_val_1078_);
lean_dec(v_val_1078_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1096_, v___x_1086_);
v___x_1098_ = lean_string_append(v___x_1094_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
v___x_1101_ = l_mkPanicMessageWithDecl(v___x_1081_, v___x_1082_, v___x_1083_, v___x_1084_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = lean_panic_fn_borrowed(v_env_1062_, v___x_1101_);
lean_dec_ref(v_env_1062_);
return v___x_1102_;
}
else
{
lean_dec(v___x_1077_);
if (v_allowOverwrite_1065_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1103_ = lean_box(1);
v___x_1104_ = lean_box(1);
v___x_1105_ = lean_box(0);
lean_inc_ref(v_env_1062_);
v___x_1106_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1103_, v_ext_1061_, v_env_1062_, v___x_1104_, v___x_1105_, v_allowOverwrite_1065_);
v___x_1107_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1063_, v___x_1106_);
lean_dec(v___x_1106_);
if (v___x_1107_ == 0)
{
goto v___jp_1066_;
}
else
{
lean_object* v_name_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_val_1064_);
v_name_1108_ = lean_ctor_get(v_ext_1061_, 1);
lean_inc(v_name_1108_);
lean_dec_ref(v_ext_1061_);
v___x_1109_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1110_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1111_ = lean_unsigned_to_nat(186u);
v___x_1112_ = lean_unsigned_to_nat(4u);
v___x_1113_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1114_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1063_, v___x_1107_);
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1117_ = lean_string_append(v___x_1115_, v___x_1116_);
v___x_1118_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1108_, v___x_1107_);
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__5));
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
v___x_1122_ = l_mkPanicMessageWithDecl(v___x_1109_, v___x_1110_, v___x_1111_, v___x_1112_, v___x_1121_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = lean_panic_fn_borrowed(v_env_1062_, v___x_1122_);
lean_dec_ref(v_env_1062_);
return v___x_1123_;
}
}
else
{
goto v___jp_1066_;
}
}
v___jp_1066_:
{
lean_object* v_toEnvExtension_1067_; lean_object* v_addEntryFn_1068_; lean_object* v_asyncMode_1069_; uint8_t v_logWrites_1070_; lean_object* v___x_1071_; lean_object* v___f_1072_; uint8_t v___x_1073_; 
v_toEnvExtension_1067_ = lean_ctor_get(v_ext_1061_, 0);
lean_inc_ref(v_toEnvExtension_1067_);
v_addEntryFn_1068_ = lean_ctor_get(v_ext_1061_, 3);
lean_inc(v_addEntryFn_1068_);
lean_dec_ref(v_ext_1061_);
v_asyncMode_1069_ = lean_ctor_get(v_toEnvExtension_1067_, 2);
lean_inc(v_asyncMode_1069_);
v_logWrites_1070_ = lean_ctor_get_uint8(v_toEnvExtension_1067_, sizeof(void*)*6);
lean_inc(v_declName_1063_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_declName_1063_);
lean_ctor_set(v___x_1071_, 1, v_val_1064_);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_insert___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1072_, 0, v_addEntryFn_1068_);
lean_closure_set(v___f_1072_, 1, v___x_1071_);
v___x_1073_ = 1;
if (v_logWrites_1070_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1067_, v_env_1062_, v___f_1072_, v_asyncMode_1069_, v_declName_1063_, v___x_1073_);
lean_dec(v_asyncMode_1069_);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_inc(v_declName_1063_);
v___x_1075_ = l_Lean_Environment_logDeclChange(v_env_1062_, v_declName_1063_);
v___x_1076_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1067_, v___x_1075_, v___f_1072_, v_asyncMode_1069_, v_declName_1063_, v___x_1073_);
lean_dec(v_asyncMode_1069_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___boxed(lean_object* v_ext_1124_, lean_object* v_env_1125_, lean_object* v_declName_1126_, lean_object* v_val_1127_, lean_object* v_allowOverwrite_1128_){
_start:
{
uint8_t v_allowOverwrite_boxed_1129_; lean_object* v_res_1130_; 
v_allowOverwrite_boxed_1129_ = lean_unbox(v_allowOverwrite_1128_);
v_res_1130_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1124_, v_env_1125_, v_declName_1126_, v_val_1127_, v_allowOverwrite_boxed_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_1131_, lean_object* v_ext_1132_, lean_object* v_env_1133_, lean_object* v_declName_1134_, lean_object* v_val_1135_, uint8_t v_allowOverwrite_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1132_, v_env_1133_, v_declName_1134_, v_val_1135_, v_allowOverwrite_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_ext_1139_, lean_object* v_env_1140_, lean_object* v_declName_1141_, lean_object* v_val_1142_, lean_object* v_allowOverwrite_1143_){
_start:
{
uint8_t v_allowOverwrite_boxed_1144_; lean_object* v_res_1145_; 
v_allowOverwrite_boxed_1144_ = lean_unbox(v_allowOverwrite_1143_);
v_res_1145_ = l_Lean_MapDeclarationExtension_insert(v_00_u03b1_1138_, v_ext_1139_, v_env_1140_, v_declName_1141_, v_val_1142_, v_allowOverwrite_boxed_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(lean_object* v_a_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_fst_1148_; lean_object* v_fst_1149_; uint8_t v___x_1150_; 
v_fst_1148_ = lean_ctor_get(v_a_1146_, 0);
v_fst_1149_ = lean_ctor_get(v_b_1147_, 0);
v___x_1150_ = l_Lean_Name_quickLt(v_fst_1148_, v_fst_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0___boxed(lean_object* v_a_1151_, lean_object* v_b_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l_Lean_MapDeclarationExtension_find_x3f___redArg___lam__0(v_a_1151_, v_b_1152_);
lean_dec_ref(v_b_1152_);
lean_dec_ref(v_a_1151_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_inst_1157_, lean_object* v_ext_1158_, lean_object* v_env_1159_, lean_object* v_declName_1160_, lean_object* v_asyncMode_1161_, uint8_t v_level_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_box(1);
v___x_1164_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1159_, v_declName_1160_);
if (lean_obj_tag(v___x_1164_) == 0)
{
uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v_inst_1157_);
v___x_1165_ = 0;
lean_inc(v_declName_1160_);
v___x_1166_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1163_, v_ext_1158_, v_env_1159_, v_asyncMode_1161_, v_declName_1160_, v___x_1165_);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1166_, v_declName_1160_);
lean_dec(v_declName_1160_);
lean_dec(v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v_val_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_val_1168_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1169_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1163_, v_ext_1158_, v_env_1159_, v_val_1168_, v_level_1162_);
lean_dec(v_val_1168_);
lean_dec_ref(v_env_1159_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_array_get_size(v___x_1169_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v___x_1169_);
lean_dec(v_declName_1160_);
lean_dec(v_inst_1157_);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_sub(v___x_1171_, v___x_1174_);
v___x_1176_ = lean_nat_dec_le(v___x_1170_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec(v___x_1175_);
lean_dec_ref(v___x_1169_);
lean_dec(v_declName_1160_);
lean_dec(v_inst_1157_);
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___f_1178_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_declName_1160_);
lean_ctor_set(v___x_1179_, 1, v_inst_1157_);
v___x_1180_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__1));
v___x_1181_ = l_Array_binSearchAux___redArg(v___f_1178_, v___x_1180_, v___x_1169_, v___x_1179_, v___x_1170_, v___x_1175_);
lean_dec_ref(v___x_1169_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v_val_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_val_1183_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v___x_1181_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_val_1183_);
lean_dec(v___x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_snd_1187_; lean_object* v___x_1189_; 
v_snd_1187_ = lean_ctor_get(v_val_1183_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_val_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_snd_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_snd_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_inst_1192_, lean_object* v_ext_1193_, lean_object* v_env_1194_, lean_object* v_declName_1195_, lean_object* v_asyncMode_1196_, lean_object* v_level_1197_){
_start:
{
uint8_t v_level_boxed_1198_; lean_object* v_res_1199_; 
v_level_boxed_1198_ = lean_unbox(v_level_1197_);
v_res_1199_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1192_, v_ext_1193_, v_env_1194_, v_declName_1195_, v_asyncMode_1196_, v_level_boxed_1198_);
lean_dec(v_asyncMode_1196_);
lean_dec_ref(v_ext_1193_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1200_, lean_object* v_inst_1201_, lean_object* v_ext_1202_, lean_object* v_env_1203_, lean_object* v_declName_1204_, lean_object* v_asyncMode_1205_, uint8_t v_level_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_inst_1201_, v_ext_1202_, v_env_1203_, v_declName_1204_, v_asyncMode_1205_, v_level_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_inst_1209_, lean_object* v_ext_1210_, lean_object* v_env_1211_, lean_object* v_declName_1212_, lean_object* v_asyncMode_1213_, lean_object* v_level_1214_){
_start:
{
uint8_t v_level_boxed_1215_; lean_object* v_res_1216_; 
v_level_boxed_1215_ = lean_unbox(v_level_1214_);
v_res_1216_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1208_, v_inst_1209_, v_ext_1210_, v_env_1211_, v_declName_1212_, v_asyncMode_1213_, v_level_boxed_1215_);
lean_dec(v_asyncMode_1213_);
lean_dec_ref(v_ext_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_inst_1218_, lean_object* v_ext_1219_, lean_object* v_env_1220_, lean_object* v_declName_1221_, lean_object* v_asyncMode_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(1);
v___x_1224_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1220_, v_declName_1221_);
if (lean_obj_tag(v___x_1224_) == 0)
{
uint8_t v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
lean_dec(v_inst_1218_);
v___x_1225_ = 0;
lean_inc(v_declName_1221_);
v___x_1226_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1223_, v_ext_1219_, v_env_1220_, v_asyncMode_1222_, v_declName_1221_, v___x_1225_);
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1221_, v___x_1226_);
lean_dec(v___x_1226_);
lean_dec(v_declName_1221_);
return v___x_1227_;
}
else
{
lean_object* v_val_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_val_1228_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1229_ = 0;
v___x_1230_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1223_, v_ext_1219_, v_env_1220_, v_val_1228_, v___x_1229_);
lean_dec(v_val_1228_);
lean_dec_ref(v_env_1220_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_array_get_size(v___x_1230_);
v___x_1233_ = lean_nat_dec_lt(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec_ref(v___x_1230_);
lean_dec(v_declName_1221_);
lean_dec(v_inst_1218_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_sub(v___x_1232_, v___x_1234_);
v___x_1236_ = lean_nat_dec_le(v___x_1231_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v___x_1235_);
lean_dec_ref(v___x_1230_);
lean_dec(v_declName_1221_);
lean_dec(v_inst_1218_);
return v___x_1236_;
}
else
{
lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___f_1237_ = ((lean_object*)(l_Lean_MapDeclarationExtension_find_x3f___redArg___closed__0));
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_declName_1221_);
lean_ctor_set(v___x_1238_, 1, v_inst_1218_);
v___x_1239_ = ((lean_object*)(l_Lean_MapDeclarationExtension_contains___redArg___closed__0));
v___x_1240_ = l_Array_binSearchAux___redArg(v___f_1237_, v___x_1239_, v___x_1230_, v___x_1238_, v___x_1231_, v___x_1235_);
lean_dec_ref(v___x_1230_);
v___x_1241_ = lean_unbox(v___x_1240_);
lean_dec(v___x_1240_);
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_inst_1242_, lean_object* v_ext_1243_, lean_object* v_env_1244_, lean_object* v_declName_1245_, lean_object* v_asyncMode_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1242_, v_ext_1243_, v_env_1244_, v_declName_1245_, v_asyncMode_1246_);
lean_dec(v_asyncMode_1246_);
lean_dec_ref(v_ext_1243_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1249_, lean_object* v_inst_1250_, lean_object* v_ext_1251_, lean_object* v_env_1252_, lean_object* v_declName_1253_, lean_object* v_asyncMode_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_MapDeclarationExtension_contains___redArg(v_inst_1250_, v_ext_1251_, v_env_1252_, v_declName_1253_, v_asyncMode_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_inst_1257_, lean_object* v_ext_1258_, lean_object* v_env_1259_, lean_object* v_declName_1260_, lean_object* v_asyncMode_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1256_, v_inst_1257_, v_ext_1258_, v_env_1259_, v_declName_1260_, v_asyncMode_1261_);
lean_dec(v_asyncMode_1261_);
lean_dec_ref(v_ext_1258_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
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
