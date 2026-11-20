// Lean compiler output
// Module: Lean.EnvExtension
// Imports: public import Lean.Environment import Init.Data.UInt.Lemmas
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findByName_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findByName_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findByName_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findByName_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_containsSortedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_containsSortedName___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_TagDeclarationExtension_isTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_TagDeclarationExtension_isTagged___closed__0 = (const lean_object*)&l_Lean_TagDeclarationExtension_isTagged___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg(lean_object* v_entries_535_, lean_object* v_declName_536_, size_t v_lo_537_, size_t v_hi_538_){
_start:
{
size_t v___x_539_; size_t v___x_540_; size_t v_m_541_; lean_object* v_e_542_; lean_object* v_fst_543_; uint8_t v___x_544_; 
v___x_539_ = lean_usize_add(v_lo_537_, v_hi_538_);
v___x_540_ = ((size_t)1ULL);
v_m_541_ = lean_usize_shift_right(v___x_539_, v___x_540_);
v_e_542_ = lean_array_uget_borrowed(v_entries_535_, v_m_541_);
v_fst_543_ = lean_ctor_get(v_e_542_, 0);
v___x_544_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_543_, v_declName_536_);
switch(v___x_544_)
{
case 0:
{
size_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_usize_add(v_m_541_, v___x_540_);
v___x_546_ = lean_usize_dec_le(v___x_545_, v_hi_538_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
v_lo_537_ = v___x_545_;
goto _start;
}
}
case 1:
{
lean_object* v___x_549_; 
lean_inc(v_e_542_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_e_542_);
return v___x_549_;
}
default: 
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_lo_537_, v_m_541_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(0);
return v___x_551_;
}
else
{
size_t v___x_552_; 
v___x_552_ = lean_usize_sub(v_m_541_, v___x_540_);
v_hi_538_ = v___x_552_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg___boxed(lean_object* v_entries_554_, lean_object* v_declName_555_, lean_object* v_lo_556_, lean_object* v_hi_557_){
_start:
{
size_t v_lo_boxed_558_; size_t v_hi_boxed_559_; lean_object* v_res_560_; 
v_lo_boxed_558_ = lean_unbox_usize(v_lo_556_);
lean_dec(v_lo_556_);
v_hi_boxed_559_ = lean_unbox_usize(v_hi_557_);
lean_dec(v_hi_557_);
v_res_560_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg(v_entries_554_, v_declName_555_, v_lo_boxed_558_, v_hi_boxed_559_);
lean_dec(v_declName_555_);
lean_dec_ref(v_entries_554_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize(lean_object* v_00_u03b1_561_, lean_object* v_entries_562_, lean_object* v_declName_563_, lean_object* v_hsize_564_, size_t v_lo_565_, size_t v_hi_566_, lean_object* v_hlo_567_, lean_object* v_hhi_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg(v_entries_562_, v_declName_563_, v_lo_565_, v_hi_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___boxed(lean_object* v_00_u03b1_570_, lean_object* v_entries_571_, lean_object* v_declName_572_, lean_object* v_hsize_573_, lean_object* v_lo_574_, lean_object* v_hi_575_, lean_object* v_hlo_576_, lean_object* v_hhi_577_){
_start:
{
size_t v_lo_boxed_578_; size_t v_hi_boxed_579_; lean_object* v_res_580_; 
v_lo_boxed_578_ = lean_unbox_usize(v_lo_574_);
lean_dec(v_lo_574_);
v_hi_boxed_579_ = lean_unbox_usize(v_hi_575_);
lean_dec(v_hi_575_);
v_res_580_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize(v_00_u03b1_570_, v_entries_571_, v_declName_572_, v_hsize_573_, v_lo_boxed_578_, v_hi_boxed_579_, v_hlo_576_, v_hhi_577_);
lean_dec(v_declName_572_);
lean_dec_ref(v_entries_571_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___redArg(uint8_t v_x_581_, lean_object* v_h__1_582_, lean_object* v_h__2_583_, lean_object* v_h__3_584_){
_start:
{
switch(v_x_581_)
{
case 0:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_h__3_584_);
lean_dec(v_h__2_583_);
v___x_585_ = lean_box(0);
v___x_586_ = lean_apply_1(v_h__1_582_, v___x_585_);
return v___x_586_;
}
case 1:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__2_583_);
lean_dec(v_h__1_582_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_apply_1(v_h__3_584_, v___x_587_);
return v___x_588_;
}
default: 
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_h__3_584_);
lean_dec(v_h__1_582_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_apply_1(v_h__2_583_, v___x_589_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___redArg___boxed(lean_object* v_x_591_, lean_object* v_h__1_592_, lean_object* v_h__2_593_, lean_object* v_h__3_594_){
_start:
{
uint8_t v_x_33__boxed_595_; lean_object* v_res_596_; 
v_x_33__boxed_595_ = lean_unbox(v_x_591_);
v_res_596_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___redArg(v_x_33__boxed_595_, v_h__1_592_, v_h__2_593_, v_h__3_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter(lean_object* v_motive_597_, uint8_t v_x_598_, lean_object* v_h__1_599_, lean_object* v_h__2_600_, lean_object* v_h__3_601_){
_start:
{
switch(v_x_598_)
{
case 0:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_h__3_601_);
lean_dec(v_h__2_600_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_apply_1(v_h__1_599_, v___x_602_);
return v___x_603_;
}
case 1:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v_h__2_600_);
lean_dec(v_h__1_599_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_apply_1(v_h__3_601_, v___x_604_);
return v___x_605_;
}
default: 
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v_h__3_601_);
lean_dec(v_h__1_599_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_apply_1(v_h__2_600_, v___x_606_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter___boxed(lean_object* v_motive_608_, lean_object* v_x_609_, lean_object* v_h__1_610_, lean_object* v_h__2_611_, lean_object* v_h__3_612_){
_start:
{
uint8_t v_x_48__boxed_613_; lean_object* v_res_614_; 
v_x_48__boxed_613_ = lean_unbox(v_x_609_);
v_res_614_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize_match__1_splitter(v_motive_608_, v_x_48__boxed_613_, v_h__1_610_, v_h__2_611_, v_h__3_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg(lean_object* v_entries_615_, lean_object* v_declName_616_, lean_object* v_lo_617_, lean_object* v_hi_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_m_621_; lean_object* v_e_622_; lean_object* v_fst_623_; uint8_t v___x_624_; 
v___x_619_ = lean_nat_add(v_lo_617_, v_hi_618_);
v___x_620_ = lean_unsigned_to_nat(1u);
v_m_621_ = lean_nat_shiftr(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
v_e_622_ = lean_array_fget_borrowed(v_entries_615_, v_m_621_);
v_fst_623_ = lean_ctor_get(v_e_622_, 0);
v___x_624_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_623_, v_declName_616_);
switch(v___x_624_)
{
case 0:
{
lean_object* v___x_625_; uint8_t v___x_626_; 
lean_dec(v_lo_617_);
v___x_625_ = lean_nat_add(v_m_621_, v___x_620_);
lean_dec(v_m_621_);
v___x_626_ = lean_nat_dec_le(v___x_625_, v_hi_618_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec(v___x_625_);
lean_dec(v_hi_618_);
v___x_627_ = lean_box(0);
return v___x_627_;
}
else
{
v_lo_617_ = v___x_625_;
goto _start;
}
}
case 1:
{
lean_object* v___x_629_; 
lean_dec(v_m_621_);
lean_dec(v_hi_618_);
lean_dec(v_lo_617_);
lean_inc(v_e_622_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_e_622_);
return v___x_629_;
}
default: 
{
lean_object* v___x_630_; uint8_t v___x_631_; 
lean_dec(v_hi_618_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_nat_dec_eq(v_m_621_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_nat_sub(v_m_621_, v___x_620_);
lean_dec(v_m_621_);
v___x_633_ = lean_nat_dec_lt(v___x_632_, v_lo_617_);
if (v___x_633_ == 0)
{
v_hi_618_ = v___x_632_;
goto _start;
}
else
{
lean_object* v___x_635_; 
lean_dec(v___x_632_);
lean_dec(v_lo_617_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
else
{
lean_object* v___x_636_; 
lean_dec(v_m_621_);
lean_dec(v_lo_617_);
v___x_636_ = lean_box(0);
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg___boxed(lean_object* v_entries_637_, lean_object* v_declName_638_, lean_object* v_lo_639_, lean_object* v_hi_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg(v_entries_637_, v_declName_638_, v_lo_639_, v_hi_640_);
lean_dec(v_declName_638_);
lean_dec_ref(v_entries_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go(lean_object* v_00_u03b1_642_, lean_object* v_entries_643_, lean_object* v_declName_644_, lean_object* v_lo_645_, lean_object* v_hi_646_, lean_object* v_hlo_647_, lean_object* v_hhi_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg(v_entries_643_, v_declName_644_, v_lo_645_, v_hi_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___boxed(lean_object* v_00_u03b1_650_, lean_object* v_entries_651_, lean_object* v_declName_652_, lean_object* v_lo_653_, lean_object* v_hi_654_, lean_object* v_hlo_655_, lean_object* v_hhi_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go(v_00_u03b1_650_, v_entries_651_, v_declName_652_, v_lo_653_, v_hi_654_, v_hlo_655_, v_hhi_656_);
lean_dec(v_declName_652_);
lean_dec_ref(v_entries_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f___redArg(lean_object* v_entries_658_, lean_object* v_declName_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_entries_658_);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_box(0);
return v___x_663_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(2147483647u);
v___x_665_ = lean_nat_dec_lt(v___x_661_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_sub(v___x_661_, v___x_666_);
v___x_668_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_go___redArg(v_entries_658_, v_declName_659_, v___x_660_, v___x_667_);
return v___x_668_;
}
else
{
size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_669_ = ((size_t)0ULL);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_sub(v___x_661_, v___x_670_);
v___x_672_ = lean_usize_of_nat(v___x_671_);
lean_dec(v___x_671_);
v___x_673_ = l___private_Lean_EnvExtension_0__Lean_findSortedByName_x3f_goUSize___redArg(v_entries_658_, v_declName_659_, v___x_669_, v___x_672_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f___redArg___boxed(lean_object* v_entries_674_, lean_object* v_declName_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_findSortedByName_x3f___redArg(v_entries_674_, v_declName_675_);
lean_dec(v_declName_675_);
lean_dec_ref(v_entries_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f(lean_object* v_00_u03b1_677_, lean_object* v_entries_678_, lean_object* v_declName_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_findSortedByName_x3f___redArg(v_entries_678_, v_declName_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSortedByName_x3f___boxed(lean_object* v_00_u03b1_681_, lean_object* v_entries_682_, lean_object* v_declName_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_findSortedByName_x3f(v_00_u03b1_681_, v_entries_682_, v_declName_683_);
lean_dec(v_declName_683_);
lean_dec_ref(v_entries_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg(lean_object* v_entries_685_, lean_object* v_declName_686_, lean_object* v_i_687_){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_array_get_size(v_entries_685_);
v___x_689_ = lean_nat_dec_lt(v_i_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
lean_dec(v_i_687_);
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
lean_object* v_e_691_; lean_object* v_fst_692_; uint8_t v___x_693_; 
v_e_691_ = lean_array_fget_borrowed(v_entries_685_, v_i_687_);
v_fst_692_ = lean_ctor_get(v_e_691_, 0);
v___x_693_ = lean_name_eq(v_fst_692_, v_declName_686_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_i_687_, v___x_694_);
lean_dec(v_i_687_);
v_i_687_ = v___x_695_;
goto _start;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_i_687_);
lean_inc(v_e_691_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_e_691_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg___boxed(lean_object* v_entries_698_, lean_object* v_declName_699_, lean_object* v_i_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg(v_entries_698_, v_declName_699_, v_i_700_);
lean_dec(v_declName_699_);
lean_dec_ref(v_entries_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go(lean_object* v_00_u03b1_702_, lean_object* v_entries_703_, lean_object* v_declName_704_, lean_object* v_i_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg(v_entries_703_, v_declName_704_, v_i_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___boxed(lean_object* v_00_u03b1_707_, lean_object* v_entries_708_, lean_object* v_declName_709_, lean_object* v_i_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go(v_00_u03b1_707_, v_entries_708_, v_declName_709_, v_i_710_);
lean_dec(v_declName_709_);
lean_dec_ref(v_entries_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_findByName_x3f___redArg(lean_object* v_entries_712_, lean_object* v_declName_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l___private_Lean_EnvExtension_0__Lean_findByName_x3f_go___redArg(v_entries_712_, v_declName_713_, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_findByName_x3f___redArg___boxed(lean_object* v_entries_716_, lean_object* v_declName_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_findByName_x3f___redArg(v_entries_716_, v_declName_717_);
lean_dec(v_declName_717_);
lean_dec_ref(v_entries_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_findByName_x3f(lean_object* v_00_u03b1_719_, lean_object* v_entries_720_, lean_object* v_declName_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_findByName_x3f___redArg(v_entries_720_, v_declName_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_findByName_x3f___boxed(lean_object* v_00_u03b1_723_, lean_object* v_entries_724_, lean_object* v_declName_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_findByName_x3f(v_00_u03b1_723_, v_entries_724_, v_declName_725_);
lean_dec(v_declName_725_);
lean_dec_ref(v_entries_724_);
return v_res_726_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg(lean_object* v_names_727_, lean_object* v_declName_728_, size_t v_lo_729_, size_t v_hi_730_){
_start:
{
size_t v___x_731_; size_t v___x_732_; size_t v_m_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_731_ = lean_usize_add(v_lo_729_, v_hi_730_);
v___x_732_ = ((size_t)1ULL);
v_m_733_ = lean_usize_shift_right(v___x_731_, v___x_732_);
v___x_734_ = lean_array_uget_borrowed(v_names_727_, v_m_733_);
v___x_735_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v___x_734_, v_declName_728_);
switch(v___x_735_)
{
case 0:
{
size_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_usize_add(v_m_733_, v___x_732_);
v___x_737_ = lean_usize_dec_le(v___x_736_, v_hi_730_);
if (v___x_737_ == 0)
{
return v___x_737_;
}
else
{
v_lo_729_ = v___x_736_;
goto _start;
}
}
case 1:
{
uint8_t v___x_739_; 
v___x_739_ = 1;
return v___x_739_;
}
default: 
{
uint8_t v___x_740_; 
v___x_740_ = lean_usize_dec_lt(v_lo_729_, v_m_733_);
if (v___x_740_ == 0)
{
return v___x_740_;
}
else
{
size_t v___x_741_; 
v___x_741_ = lean_usize_sub(v_m_733_, v___x_732_);
v_hi_730_ = v___x_741_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg___boxed(lean_object* v_names_743_, lean_object* v_declName_744_, lean_object* v_lo_745_, lean_object* v_hi_746_){
_start:
{
size_t v_lo_boxed_747_; size_t v_hi_boxed_748_; uint8_t v_res_749_; lean_object* v_r_750_; 
v_lo_boxed_747_ = lean_unbox_usize(v_lo_745_);
lean_dec(v_lo_745_);
v_hi_boxed_748_ = lean_unbox_usize(v_hi_746_);
lean_dec(v_hi_746_);
v_res_749_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg(v_names_743_, v_declName_744_, v_lo_boxed_747_, v_hi_boxed_748_);
lean_dec(v_declName_744_);
lean_dec_ref(v_names_743_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize(lean_object* v_names_751_, lean_object* v_declName_752_, lean_object* v_hsize_753_, size_t v_lo_754_, size_t v_hi_755_, lean_object* v_hlo_756_, lean_object* v_hhi_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg(v_names_751_, v_declName_752_, v_lo_754_, v_hi_755_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___boxed(lean_object* v_names_759_, lean_object* v_declName_760_, lean_object* v_hsize_761_, lean_object* v_lo_762_, lean_object* v_hi_763_, lean_object* v_hlo_764_, lean_object* v_hhi_765_){
_start:
{
size_t v_lo_boxed_766_; size_t v_hi_boxed_767_; uint8_t v_res_768_; lean_object* v_r_769_; 
v_lo_boxed_766_ = lean_unbox_usize(v_lo_762_);
lean_dec(v_lo_762_);
v_hi_boxed_767_ = lean_unbox_usize(v_hi_763_);
lean_dec(v_hi_763_);
v_res_768_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize(v_names_759_, v_declName_760_, v_hsize_761_, v_lo_boxed_766_, v_hi_boxed_767_, v_hlo_764_, v_hhi_765_);
lean_dec(v_declName_760_);
lean_dec_ref(v_names_759_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg(lean_object* v_names_770_, lean_object* v_declName_771_, lean_object* v_lo_772_, lean_object* v_hi_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_m_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_774_ = lean_nat_add(v_lo_772_, v_hi_773_);
v___x_775_ = lean_unsigned_to_nat(1u);
v_m_776_ = lean_nat_shiftr(v___x_774_, v___x_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_array_fget_borrowed(v_names_770_, v_m_776_);
v___x_778_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v___x_777_, v_declName_771_);
switch(v___x_778_)
{
case 0:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
lean_dec(v_lo_772_);
v___x_779_ = lean_nat_add(v_m_776_, v___x_775_);
lean_dec(v_m_776_);
v___x_780_ = lean_nat_dec_le(v___x_779_, v_hi_773_);
if (v___x_780_ == 0)
{
lean_dec(v___x_779_);
lean_dec(v_hi_773_);
return v___x_780_;
}
else
{
v_lo_772_ = v___x_779_;
goto _start;
}
}
case 1:
{
uint8_t v___x_782_; 
lean_dec(v_m_776_);
lean_dec(v_hi_773_);
lean_dec(v_lo_772_);
v___x_782_ = 1;
return v___x_782_;
}
default: 
{
lean_object* v___x_783_; uint8_t v___x_784_; 
lean_dec(v_hi_773_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_nat_dec_eq(v_m_776_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_nat_sub(v_m_776_, v___x_775_);
lean_dec(v_m_776_);
v___x_786_ = lean_nat_dec_lt(v___x_785_, v_lo_772_);
if (v___x_786_ == 0)
{
v_hi_773_ = v___x_785_;
goto _start;
}
else
{
lean_dec(v___x_785_);
lean_dec(v_lo_772_);
return v___x_784_;
}
}
else
{
uint8_t v___x_788_; 
lean_dec(v_m_776_);
lean_dec(v_lo_772_);
v___x_788_ = 0;
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg___boxed(lean_object* v_names_789_, lean_object* v_declName_790_, lean_object* v_lo_791_, lean_object* v_hi_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg(v_names_789_, v_declName_790_, v_lo_791_, v_hi_792_);
lean_dec(v_declName_790_);
lean_dec_ref(v_names_789_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_EnvExtension_0__Lean_containsSortedName_go(lean_object* v_names_795_, lean_object* v_declName_796_, lean_object* v_lo_797_, lean_object* v_hi_798_, lean_object* v_hlo_799_, lean_object* v_hhi_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg(v_names_795_, v_declName_796_, v_lo_797_, v_hi_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___boxed(lean_object* v_names_802_, lean_object* v_declName_803_, lean_object* v_lo_804_, lean_object* v_hi_805_, lean_object* v_hlo_806_, lean_object* v_hhi_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_go(v_names_802_, v_declName_803_, v_lo_804_, v_hi_805_, v_hlo_806_, v_hhi_807_);
lean_dec(v_declName_803_);
lean_dec_ref(v_names_802_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t l_Lean_containsSortedName(lean_object* v_names_810_, lean_object* v_declName_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_array_get_size(v_names_810_);
v___x_814_ = lean_nat_dec_lt(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
return v___x_814_;
}
else
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(2147483647u);
v___x_816_ = lean_nat_dec_lt(v___x_813_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_sub(v___x_813_, v___x_817_);
v___x_819_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_go___redArg(v_names_810_, v_declName_811_, v___x_812_, v___x_818_);
return v___x_819_;
}
else
{
size_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; size_t v___x_823_; uint8_t v___x_824_; 
v___x_820_ = ((size_t)0ULL);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_sub(v___x_813_, v___x_821_);
v___x_823_ = lean_usize_of_nat(v___x_822_);
lean_dec(v___x_822_);
v___x_824_ = l___private_Lean_EnvExtension_0__Lean_containsSortedName_goUSize___redArg(v_names_810_, v_declName_811_, v___x_820_, v___x_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_containsSortedName___boxed(lean_object* v_names_825_, lean_object* v_declName_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Lean_containsSortedName(v_names_825_, v_declName_826_);
lean_dec(v_declName_826_);
lean_dec_ref(v_names_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
static lean_object* _init_l_Lean_mkTagDeclarationExtension___auto__1(void){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0(lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_NameSet_empty;
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__0___boxed(lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_mkTagDeclarationExtension___lam__0(v_x_832_);
lean_dec_ref(v_x_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(lean_object* v_hi_834_, lean_object* v_pivot_835_, lean_object* v_as_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = lean_nat_dec_lt(v_k_838_, v_hi_834_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_k_838_);
v___x_840_ = lean_array_fswap(v_as_836_, v_i_837_, v_hi_834_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_i_837_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_array_fget_borrowed(v_as_836_, v_k_838_);
v___x_843_ = l_Lean_Name_quickLt(v___x_842_, v_pivot_835_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_add(v_k_838_, v___x_844_);
lean_dec(v_k_838_);
v_k_838_ = v___x_845_;
goto _start;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_array_fswap(v_as_836_, v_i_837_, v_k_838_);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_i_837_, v___x_848_);
lean_dec(v_i_837_);
v___x_850_ = lean_nat_add(v_k_838_, v___x_848_);
lean_dec(v_k_838_);
v_as_836_ = v___x_847_;
v_i_837_ = v___x_849_;
v_k_838_ = v___x_850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg___boxed(lean_object* v_hi_852_, lean_object* v_pivot_853_, lean_object* v_as_854_, lean_object* v_i_855_, lean_object* v_k_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_852_, v_pivot_853_, v_as_854_, v_i_855_, v_k_856_);
lean_dec(v_pivot_853_);
lean_dec(v_hi_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object* v_n_858_, lean_object* v_as_859_, lean_object* v_lo_860_, lean_object* v_hi_861_){
_start:
{
lean_object* v___y_863_; uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_lt(v_lo_860_, v_hi_861_);
if (v___x_873_ == 0)
{
lean_dec(v_lo_860_);
return v_as_859_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_mid_876_; lean_object* v___y_878_; lean_object* v___y_884_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_874_ = lean_nat_add(v_lo_860_, v_hi_861_);
v___x_875_ = lean_unsigned_to_nat(1u);
v_mid_876_ = lean_nat_shiftr(v___x_874_, v___x_875_);
lean_dec(v___x_874_);
v___x_889_ = lean_array_fget_borrowed(v_as_859_, v_mid_876_);
v___x_890_ = lean_array_fget_borrowed(v_as_859_, v_lo_860_);
v___x_891_ = l_Lean_Name_quickLt(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
v___y_884_ = v_as_859_;
goto v___jp_883_;
}
else
{
lean_object* v___x_892_; 
v___x_892_ = lean_array_fswap(v_as_859_, v_lo_860_, v_mid_876_);
v___y_884_ = v___x_892_;
goto v___jp_883_;
}
v___jp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_array_fget_borrowed(v___y_878_, v_mid_876_);
v___x_880_ = lean_array_fget_borrowed(v___y_878_, v_hi_861_);
v___x_881_ = l_Lean_Name_quickLt(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v_mid_876_);
v___y_863_ = v___y_878_;
goto v___jp_862_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_array_fswap(v___y_878_, v_mid_876_, v_hi_861_);
lean_dec(v_mid_876_);
v___y_863_ = v___x_882_;
goto v___jp_862_;
}
}
v___jp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_array_fget_borrowed(v___y_884_, v_hi_861_);
v___x_886_ = lean_array_fget_borrowed(v___y_884_, v_lo_860_);
v___x_887_ = l_Lean_Name_quickLt(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
v___y_878_ = v___y_884_;
goto v___jp_877_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_array_fswap(v___y_884_, v_lo_860_, v_hi_861_);
v___y_878_ = v___x_888_;
goto v___jp_877_;
}
}
}
v___jp_862_:
{
lean_object* v_pivot_864_; lean_object* v___x_865_; lean_object* v_fst_866_; lean_object* v_snd_867_; uint8_t v___x_868_; 
v_pivot_864_ = lean_array_fget(v___y_863_, v_hi_861_);
lean_inc_n(v_lo_860_, 2);
v___x_865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_861_, v_pivot_864_, v___y_863_, v_lo_860_, v_lo_860_);
lean_dec(v_pivot_864_);
v_fst_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_fst_866_);
v_snd_867_ = lean_ctor_get(v___x_865_, 1);
lean_inc(v_snd_867_);
lean_dec_ref(v___x_865_);
v___x_868_ = lean_nat_dec_le(v_hi_861_, v_fst_866_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_858_, v_snd_867_, v_lo_860_, v_fst_866_);
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = lean_nat_add(v_fst_866_, v___x_870_);
lean_dec(v_fst_866_);
v_as_859_ = v___x_869_;
v_lo_860_ = v___x_871_;
goto _start;
}
else
{
lean_dec(v_fst_866_);
lean_dec(v_lo_860_);
return v_snd_867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg___boxed(lean_object* v_n_893_, lean_object* v_as_894_, lean_object* v_lo_895_, lean_object* v_hi_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_893_, v_as_894_, v_lo_895_, v_hi_896_);
lean_dec(v_hi_896_);
lean_dec(v_n_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__1(lean_object* v_es_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_899_ = lean_array_mk(v_es_898_);
v___x_900_ = lean_array_get_size(v___x_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___y_906_; uint8_t v___x_910_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_sub(v___x_900_, v___x_903_);
v___x_910_ = lean_nat_dec_le(v___x_901_, v___x_904_);
if (v___x_910_ == 0)
{
lean_inc(v___x_904_);
v___y_906_ = v___x_904_;
goto v___jp_905_;
}
else
{
v___y_906_ = v___x_901_;
goto v___jp_905_;
}
v___jp_905_:
{
uint8_t v___x_907_; 
v___x_907_ = lean_nat_dec_le(v___y_906_, v___x_904_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec(v___x_904_);
lean_inc(v___y_906_);
v___x_908_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_900_, v___x_899_, v___y_906_, v___y_906_);
lean_dec(v___y_906_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v___x_900_, v___x_899_, v___y_906_, v___x_904_);
lean_dec(v___x_904_);
return v___x_909_;
}
}
}
else
{
return v___x_899_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_mkTagDeclarationExtension___lam__2(lean_object* v_x1_911_, lean_object* v_x2_912_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = l_Lean_NameSet_contains(v_x1_911_, v_x2_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
v___x_914_ = 1;
return v___x_914_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = 0;
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___lam__2___boxed(lean_object* v_x1_916_, lean_object* v_x2_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Lean_mkTagDeclarationExtension___lam__2(v_x1_916_, v_x2_917_);
lean_dec(v_x2_917_);
lean_dec(v_x1_916_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension(lean_object* v_name_929_, lean_object* v_asyncMode_930_, uint8_t v_logWrites_931_){
_start:
{
lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___f_933_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__0));
v___f_934_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__1));
v___f_935_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__2));
v___x_936_ = lean_box(0);
v___x_937_ = ((lean_object*)(l_Lean_mkTagDeclarationExtension___closed__5));
v___x_938_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_938_, 0, v_name_929_);
lean_ctor_set(v___x_938_, 1, v___f_933_);
lean_ctor_set(v___x_938_, 2, v___f_934_);
lean_ctor_set(v___x_938_, 3, v___f_935_);
lean_ctor_set(v___x_938_, 4, v___x_936_);
lean_ctor_set(v___x_938_, 5, v_asyncMode_930_);
lean_ctor_set(v___x_938_, 6, v___x_937_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*7, v_logWrites_931_);
v___x_939_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkTagDeclarationExtension___boxed(lean_object* v_name_940_, lean_object* v_asyncMode_941_, lean_object* v_logWrites_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_logWrites_boxed_944_; lean_object* v_res_945_; 
v_logWrites_boxed_944_ = lean_unbox(v_logWrites_942_);
v_res_945_ = l_Lean_mkTagDeclarationExtension(v_name_940_, v_asyncMode_941_, v_logWrites_boxed_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(lean_object* v_n_946_, lean_object* v_as_947_, lean_object* v_lo_948_, lean_object* v_hi_949_, lean_object* v_w_950_, lean_object* v_hlo_951_, lean_object* v_hhi_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___redArg(v_n_946_, v_as_947_, v_lo_948_, v_hi_949_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0___boxed(lean_object* v_n_954_, lean_object* v_as_955_, lean_object* v_lo_956_, lean_object* v_hi_957_, lean_object* v_w_958_, lean_object* v_hlo_959_, lean_object* v_hhi_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0(v_n_954_, v_as_955_, v_lo_956_, v_hi_957_, v_w_958_, v_hlo_959_, v_hhi_960_);
lean_dec(v_hi_957_);
lean_dec(v_n_954_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(lean_object* v_n_962_, lean_object* v_lo_963_, lean_object* v_hi_964_, lean_object* v_hhi_965_, lean_object* v_pivot_966_, lean_object* v_as_967_, lean_object* v_i_968_, lean_object* v_k_969_, lean_object* v_ilo_970_, lean_object* v_ik_971_, lean_object* v_w_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___redArg(v_hi_964_, v_pivot_966_, v_as_967_, v_i_968_, v_k_969_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0___boxed(lean_object* v_n_974_, lean_object* v_lo_975_, lean_object* v_hi_976_, lean_object* v_hhi_977_, lean_object* v_pivot_978_, lean_object* v_as_979_, lean_object* v_i_980_, lean_object* v_k_981_, lean_object* v_ilo_982_, lean_object* v_ik_983_, lean_object* v_w_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mkTagDeclarationExtension_spec__0_spec__0(v_n_974_, v_lo_975_, v_hi_976_, v_hhi_977_, v_pivot_978_, v_as_979_, v_i_980_, v_k_981_, v_ilo_982_, v_ik_983_, v_w_984_);
lean_dec(v_pivot_978_);
lean_dec(v_hi_976_);
lean_dec(v_lo_975_);
lean_dec(v_n_974_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__0(v_x_991_, v___y_992_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_x_991_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(lean_object* v_s_995_, lean_object* v_x_996_){
_start:
{
lean_inc_ref(v_s_995_);
return v_s_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1___boxed(lean_object* v_s_997_, lean_object* v_x_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__1(v_s_997_, v_x_998_);
lean_dec(v_x_998_);
lean_dec_ref(v_s_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___closed__1));
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__2(v_x_1007_, v_x_1008_);
lean_dec_ref(v_x_1008_);
lean_dec_ref(v_x_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(lean_object* v_x_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_box(0);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3___boxed(lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_TagDeclarationExtension_instInhabited___aux__1___lam__3(v_x_1012_);
lean_dec_ref(v_x_1012_);
return v_res_1013_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___f_1018_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__3));
v___f_1019_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__2));
v___f_1020_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__1));
v___f_1021_ = ((lean_object*)(l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__0));
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_1024_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
lean_ctor_set(v___x_1024_, 2, v___f_1021_);
lean_ctor_set(v___x_1024_, 3, v___f_1020_);
lean_ctor_set(v___x_1024_, 4, v___f_1019_);
lean_ctor_set(v___x_1024_, 5, v___f_1018_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1(void){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_instInhabited(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4, &l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4_once, _init_l_Lean_TagDeclarationExtension_instInhabited___aux__1___closed__4);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(lean_object* v_env_1027_, lean_object* v_msg_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_panic_fn_borrowed(v_env_1027_, v_msg_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0___boxed(lean_object* v_env_1030_, lean_object* v_msg_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_panic___at___00Lean_TagDeclarationExtension_tag_spec__0(v_env_1030_, v_msg_1031_);
lean_dec_ref(v_env_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag___lam__0(lean_object* v_addEntryFn_1033_, lean_object* v_declName_1034_, lean_object* v_s_1035_){
_start:
{
lean_object* v_importedEntries_1036_; lean_object* v_state_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
v_importedEntries_1036_ = lean_ctor_get(v_s_1035_, 0);
v_state_1037_ = lean_ctor_get(v_s_1035_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_s_1035_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1039_ = v_s_1035_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_state_1037_);
lean_inc(v_importedEntries_1036_);
lean_dec(v_s_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_state_1041_; lean_object* v___x_1043_; 
v_state_1041_ = lean_apply_2(v_addEntryFn_1033_, v_state_1037_, v_declName_1034_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v_state_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_importedEntries_1036_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_state_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
static lean_object* _init_l_Lean_TagDeclarationExtension_tag___closed__3(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1049_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__2));
v___x_1050_ = lean_unsigned_to_nat(4u);
v___x_1051_ = lean_unsigned_to_nat(233u);
v___x_1052_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__1));
v___x_1053_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1054_ = l_mkPanicMessageWithDecl(v___x_1053_, v___x_1052_, v___x_1051_, v___x_1050_, v___x_1049_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_tag(lean_object* v_ext_1055_, lean_object* v_env_1056_, lean_object* v_declName_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Lean_Name_isAnonymous(v_declName_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1056_, v_declName_1057_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1060_ = lean_box(1);
v___x_1061_ = lean_box(1);
v___x_1062_ = lean_box(0);
lean_inc_ref(v_env_1056_);
v___x_1063_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1060_, v_ext_1055_, v_env_1056_, v___x_1061_, v___x_1062_);
v___x_1064_ = l_Lean_NameSet_contains(v___x_1063_, v_declName_1057_);
lean_dec(v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v_toEnvExtension_1065_; lean_object* v_addEntryFn_1066_; lean_object* v_asyncMode_1067_; uint8_t v_logWrites_1068_; lean_object* v___f_1069_; uint8_t v___x_1070_; 
v_toEnvExtension_1065_ = lean_ctor_get(v_ext_1055_, 0);
lean_inc_ref(v_toEnvExtension_1065_);
v_addEntryFn_1066_ = lean_ctor_get(v_ext_1055_, 3);
lean_inc(v_addEntryFn_1066_);
lean_dec_ref(v_ext_1055_);
v_asyncMode_1067_ = lean_ctor_get(v_toEnvExtension_1065_, 2);
lean_inc(v_asyncMode_1067_);
v_logWrites_1068_ = lean_ctor_get_uint8(v_toEnvExtension_1065_, sizeof(void*)*6);
lean_inc(v_declName_1057_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_TagDeclarationExtension_tag___lam__0), 3, 2);
lean_closure_set(v___f_1069_, 0, v_addEntryFn_1066_);
lean_closure_set(v___f_1069_, 1, v_declName_1057_);
v___x_1070_ = 1;
if (v_logWrites_1068_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1065_, v_env_1056_, v___f_1069_, v_asyncMode_1067_, v_declName_1057_, v___x_1070_);
lean_dec(v_asyncMode_1067_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_inc(v_declName_1057_);
v___x_1072_ = l_Lean_Environment_logDeclChange(v_env_1056_, v_declName_1057_);
v___x_1073_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1065_, v___x_1072_, v___f_1069_, v_asyncMode_1067_, v_declName_1057_, v___x_1070_);
lean_dec(v_asyncMode_1067_);
return v___x_1073_;
}
}
else
{
lean_dec(v_declName_1057_);
lean_dec_ref(v_ext_1055_);
return v_env_1056_;
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref_known(v___x_1059_, 1);
lean_dec(v_declName_1057_);
lean_dec_ref(v_ext_1055_);
v___x_1074_ = lean_obj_once(&l_Lean_TagDeclarationExtension_tag___closed__3, &l_Lean_TagDeclarationExtension_tag___closed__3_once, _init_l_Lean_TagDeclarationExtension_tag___closed__3);
v___x_1075_ = lean_panic_fn_borrowed(v_env_1056_, v___x_1074_);
lean_dec_ref(v_env_1056_);
return v___x_1075_;
}
}
else
{
lean_dec(v_declName_1057_);
lean_dec_ref(v_ext_1055_);
return v_env_1056_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object* v_ext_1079_, lean_object* v_env_1080_, lean_object* v_declName_1081_, lean_object* v_asyncMode_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(1);
v___x_1084_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1080_, v_declName_1081_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
lean_inc(v_declName_1081_);
v___x_1085_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1083_, v_ext_1079_, v_env_1080_, v_asyncMode_1082_, v_declName_1081_);
v___x_1086_ = l_Lean_NameSet_contains(v___x_1085_, v_declName_1081_);
lean_dec(v_declName_1081_);
lean_dec(v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_val_1087_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1088_ = ((lean_object*)(l_Lean_TagDeclarationExtension_isTagged___closed__0));
v___x_1089_ = 0;
v___x_1090_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1088_, v_ext_1079_, v_env_1080_, v_val_1087_, v___x_1089_);
lean_dec(v_val_1087_);
lean_dec_ref(v_env_1080_);
v___x_1091_ = l_Lean_containsSortedName(v___x_1090_, v_declName_1081_);
lean_dec(v_declName_1081_);
lean_dec_ref(v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagDeclarationExtension_isTagged___boxed(lean_object* v_ext_1092_, lean_object* v_env_1093_, lean_object* v_declName_1094_, lean_object* v_asyncMode_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Lean_TagDeclarationExtension_isTagged(v_ext_1092_, v_env_1093_, v_declName_1094_, v_asyncMode_1095_);
lean_dec(v_asyncMode_1095_);
lean_dec_ref(v_ext_1092_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(lean_object* v_x_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0___boxed(lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__0(v_x_1103_, v___y_1104_);
lean_dec_ref(v___y_1104_);
lean_dec_ref(v_x_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(lean_object* v_s_1107_, lean_object* v_x_1108_){
_start:
{
lean_inc(v_s_1107_);
return v_s_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1___boxed(lean_object* v_s_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__1(v_s_1109_, v_x_1110_);
lean_dec_ref(v_x_1110_);
lean_dec(v_s_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__1));
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2(v_x_1119_, v_x_1120_);
lean_dec(v_x_1120_);
lean_dec_ref(v_x_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(lean_object* v_x_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3___boxed(lean_object* v_x_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__3(v_x_1124_);
lean_dec(v_x_1124_);
return v_res_1125_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___f_1130_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_1131_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__2));
v___f_1132_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__1));
v___f_1133_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__0));
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4, &l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SimplePersistentEnvExtension_instInhabited___aux__1___redArg___closed__4);
v___x_1136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
lean_ctor_set(v___x_1136_, 2, v___f_1133_);
lean_ctor_set(v___x_1136_, 3, v___f_1132_);
lean_ctor_set(v___x_1136_, 4, v___f_1131_);
lean_ctor_set(v___x_1136_, 5, v___f_1130_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg(){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4, &l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__4);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default___redArg___boxed(lean_object* v___dummy_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v_res_1140_;
}
}
static lean_object* _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0(void){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_instInhabitedMapDeclarationExtension_default___redArg();
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension_default(lean_object* v_00_u03b1_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg(){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension___redArg___boxed(lean_object* v___dummy_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_instInhabitedMapDeclarationExtension___redArg();
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMapDeclarationExtension(lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_obj_once(&l_Lean_instInhabitedMapDeclarationExtension_default___closed__0, &l_Lean_instInhabitedMapDeclarationExtension_default___closed__0_once, _init_l_Lean_instInhabitedMapDeclarationExtension_default___closed__0);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_mkMapDeclarationExtension___auto__3(void){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_obj_once(&l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28, &l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28_once, _init_l_Lean_SimplePersistentEnvExtensionDescr_name___autoParam___closed__28);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__0(lean_object* v_s_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1155_; 
v_fst_1153_ = lean_ctor_get(v_x_1152_, 0);
lean_inc(v_fst_1153_);
v_snd_1154_ = lean_ctor_get(v_x_1152_, 1);
lean_inc(v_snd_1154_);
lean_dec_ref(v_x_1152_);
v___x_1155_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1153_, v_snd_1154_, v_s_1151_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__1(lean_object* v_exportEntriesFn_1156_, lean_object* v_env_1157_, lean_object* v_s_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_apply_2(v_exportEntriesFn_1156_, v_env_1157_, v_s_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(lean_object* v_newState_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
return v_x_1161_;
}
else
{
lean_object* v_head_1163_; lean_object* v_tail_1164_; lean_object* v___x_1165_; 
v_head_1163_ = lean_ctor_get(v_x_1162_, 0);
lean_inc(v_head_1163_);
v_tail_1164_ = lean_ctor_get(v_x_1162_, 1);
lean_inc(v_tail_1164_);
lean_dec_ref_known(v_x_1162_, 2);
v___x_1165_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_1160_, v_head_1163_);
if (lean_obj_tag(v___x_1165_) == 1)
{
lean_object* v_val_1166_; lean_object* v___x_1167_; 
v_val_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_1163_, v_val_1166_, v_x_1161_);
v_x_1161_ = v___x_1167_;
v_x_1162_ = v_tail_1164_;
goto _start;
}
else
{
lean_dec(v___x_1165_);
lean_dec(v_head_1163_);
v_x_1162_ = v_tail_1164_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg___boxed(lean_object* v_newState_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_1170_, v_x_1171_, v_x_1172_);
lean_dec(v_newState_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3(lean_object* v_x_1174_, lean_object* v_newState_1175_, lean_object* v_newConsts_1176_, lean_object* v_s_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_1175_, v_s_1177_, v_newConsts_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__3___boxed(lean_object* v_x_1179_, lean_object* v_newState_1180_, lean_object* v_newConsts_1181_, lean_object* v_s_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_mkMapDeclarationExtension___redArg___lam__3(v_x_1179_, v_newState_1180_, v_newConsts_1181_, v_s_1182_);
lean_dec(v_newState_1180_);
lean_dec(v_x_1179_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2(lean_object* v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___lam__2___closed__0));
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__2___boxed(lean_object* v_x_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_mkMapDeclarationExtension___redArg___lam__2(v_x_1186_);
lean_dec(v_x_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4(lean_object* v___x_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__4___boxed(lean_object* v___x_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_mkMapDeclarationExtension___redArg___lam__4(v___x_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5(lean_object* v___x_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1194_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___lam__5___boxed(lean_object* v___x_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_mkMapDeclarationExtension___redArg___lam__5(v___x_1199_, v_x_1200_, v___y_1201_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v_x_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object* v_name_1213_, lean_object* v_asyncMode_1214_, uint8_t v_logWrites_1215_, lean_object* v_exportEntriesFn_1216_){
_start:
{
lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___f_1218_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__0));
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_mkMapDeclarationExtension___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1219_, 0, v_exportEntriesFn_1216_);
v___f_1220_ = ((lean_object*)(l_Lean_instInhabitedMapDeclarationExtension_default___redArg___closed__3));
v___f_1221_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__2));
v___f_1222_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__3));
v___f_1223_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__4));
v___x_1224_ = ((lean_object*)(l_Lean_mkMapDeclarationExtension___redArg___closed__5));
v___x_1225_ = 0;
v___x_1226_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1226_, 0, v_name_1213_);
lean_ctor_set(v___x_1226_, 1, v___f_1222_);
lean_ctor_set(v___x_1226_, 2, v___f_1223_);
lean_ctor_set(v___x_1226_, 3, v___f_1218_);
lean_ctor_set(v___x_1226_, 4, v___f_1219_);
lean_ctor_set(v___x_1226_, 5, v___f_1220_);
lean_ctor_set(v___x_1226_, 6, v_asyncMode_1214_);
lean_ctor_set(v___x_1226_, 7, v___x_1224_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*8, v___x_1225_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*8 + 1, v_logWrites_1215_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___f_1221_);
v___x_1228_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___redArg___boxed(lean_object* v_name_1245_, lean_object* v_asyncMode_1246_, lean_object* v_logWrites_1247_, lean_object* v_exportEntriesFn_1248_, lean_object* v_a_1249_){
_start:
{
uint8_t v_logWrites_boxed_1250_; lean_object* v_res_1251_; 
v_logWrites_boxed_1250_ = lean_unbox(v_logWrites_1247_);
v_res_1251_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1245_, v_asyncMode_1246_, v_logWrites_boxed_1250_, v_exportEntriesFn_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension(lean_object* v_00_u03b1_1252_, lean_object* v_name_1253_, lean_object* v_asyncMode_1254_, uint8_t v_logWrites_1255_, lean_object* v_exportEntriesFn_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_mkMapDeclarationExtension___redArg(v_name_1253_, v_asyncMode_1254_, v_logWrites_1255_, v_exportEntriesFn_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMapDeclarationExtension___boxed(lean_object* v_00_u03b1_1259_, lean_object* v_name_1260_, lean_object* v_asyncMode_1261_, lean_object* v_logWrites_1262_, lean_object* v_exportEntriesFn_1263_, lean_object* v_a_1264_){
_start:
{
uint8_t v_logWrites_boxed_1265_; lean_object* v_res_1266_; 
v_logWrites_boxed_1265_ = lean_unbox(v_logWrites_1262_);
v_res_1266_ = l_Lean_mkMapDeclarationExtension(v_00_u03b1_1259_, v_name_1260_, v_asyncMode_1261_, v_logWrites_boxed_1265_, v_exportEntriesFn_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(lean_object* v_00_u03b1_1267_, lean_object* v_newState_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___redArg(v_newState_1268_, v_x_1269_, v_x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_newState_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_List_foldl___at___00Lean_mkMapDeclarationExtension_spec__0(v_00_u03b1_1272_, v_newState_1273_, v_x_1274_, v_x_1275_);
lean_dec(v_newState_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___lam__0(lean_object* v_addEntryFn_1277_, lean_object* v___x_1278_, lean_object* v_s_1279_){
_start:
{
lean_object* v_importedEntries_1280_; lean_object* v_state_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_importedEntries_1280_ = lean_ctor_get(v_s_1279_, 0);
v_state_1281_ = lean_ctor_get(v_s_1279_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_s_1279_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v_s_1279_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_state_1281_);
lean_inc(v_importedEntries_1280_);
lean_dec(v_s_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_state_1285_; lean_object* v___x_1287_; 
v_state_1285_ = lean_apply_2(v_addEntryFn_1277_, v_state_1281_, v___x_1278_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v_state_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_importedEntries_1280_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_state_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object* v_ext_1296_, lean_object* v_env_1297_, lean_object* v_declName_1298_, lean_object* v_val_1299_, uint8_t v_allowOverwrite_1300_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1297_, v_declName_1298_);
if (lean_obj_tag(v___x_1312_) == 1)
{
lean_object* v_val_1313_; lean_object* v_name_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v_val_1299_);
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v_name_1314_ = lean_ctor_get(v_ext_1296_, 1);
lean_inc(v_name_1314_);
lean_dec_ref(v_ext_1296_);
v___x_1315_ = lean_box(0);
v___x_1316_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1317_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1318_ = lean_unsigned_to_nat(292u);
v___x_1319_ = lean_unsigned_to_nat(4u);
v___x_1320_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1321_ = 1;
v___x_1322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1298_, v___x_1321_);
v___x_1323_ = lean_string_append(v___x_1320_, v___x_1322_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1325_ = lean_string_append(v___x_1323_, v___x_1324_);
v___x_1326_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1314_, v___x_1321_);
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__3));
v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
v___x_1330_ = l_Lean_Environment_allImportedModuleNames(v_env_1297_);
v___x_1331_ = lean_array_get(v___x_1315_, v___x_1330_, v_val_1313_);
lean_dec(v_val_1313_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1331_, v___x_1321_);
v___x_1333_ = lean_string_append(v___x_1329_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__4));
v___x_1335_ = lean_string_append(v___x_1333_, v___x_1334_);
v___x_1336_ = l_mkPanicMessageWithDecl(v___x_1316_, v___x_1317_, v___x_1318_, v___x_1319_, v___x_1335_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_panic_fn_borrowed(v_env_1297_, v___x_1336_);
lean_dec_ref(v_env_1297_);
return v___x_1337_;
}
else
{
lean_dec(v___x_1312_);
if (v_allowOverwrite_1300_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1338_ = lean_box(1);
v___x_1339_ = lean_box(1);
v___x_1340_ = lean_box(0);
lean_inc_ref(v_env_1297_);
v___x_1341_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1338_, v_ext_1296_, v_env_1297_, v___x_1339_, v___x_1340_, v_allowOverwrite_1300_);
v___x_1342_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1298_, v___x_1341_);
lean_dec(v___x_1341_);
if (v___x_1342_ == 0)
{
goto v___jp_1301_;
}
else
{
lean_object* v_name_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_val_1299_);
v_name_1343_ = lean_ctor_get(v_ext_1296_, 1);
lean_inc(v_name_1343_);
lean_dec_ref(v_ext_1296_);
v___x_1344_ = ((lean_object*)(l_Lean_TagDeclarationExtension_tag___closed__0));
v___x_1345_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__0));
v___x_1346_ = lean_unsigned_to_nat(299u);
v___x_1347_ = lean_unsigned_to_nat(4u);
v___x_1348_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__1));
v___x_1349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1298_, v___x_1342_);
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__2));
v___x_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
v___x_1353_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1343_, v___x_1342_);
v___x_1354_ = lean_string_append(v___x_1352_, v___x_1353_);
lean_dec_ref(v___x_1353_);
v___x_1355_ = ((lean_object*)(l_Lean_MapDeclarationExtension_insert___redArg___closed__5));
v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
v___x_1357_ = l_mkPanicMessageWithDecl(v___x_1344_, v___x_1345_, v___x_1346_, v___x_1347_, v___x_1356_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_panic_fn_borrowed(v_env_1297_, v___x_1357_);
lean_dec_ref(v_env_1297_);
return v___x_1358_;
}
}
else
{
goto v___jp_1301_;
}
}
v___jp_1301_:
{
lean_object* v_toEnvExtension_1302_; lean_object* v_addEntryFn_1303_; lean_object* v_asyncMode_1304_; uint8_t v_logWrites_1305_; lean_object* v___x_1306_; lean_object* v___f_1307_; uint8_t v___x_1308_; 
v_toEnvExtension_1302_ = lean_ctor_get(v_ext_1296_, 0);
lean_inc_ref(v_toEnvExtension_1302_);
v_addEntryFn_1303_ = lean_ctor_get(v_ext_1296_, 3);
lean_inc(v_addEntryFn_1303_);
lean_dec_ref(v_ext_1296_);
v_asyncMode_1304_ = lean_ctor_get(v_toEnvExtension_1302_, 2);
lean_inc(v_asyncMode_1304_);
v_logWrites_1305_ = lean_ctor_get_uint8(v_toEnvExtension_1302_, sizeof(void*)*6);
lean_inc(v_declName_1298_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_declName_1298_);
lean_ctor_set(v___x_1306_, 1, v_val_1299_);
v___f_1307_ = lean_alloc_closure((void*)(l_Lean_MapDeclarationExtension_insert___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1307_, 0, v_addEntryFn_1303_);
lean_closure_set(v___f_1307_, 1, v___x_1306_);
v___x_1308_ = 1;
if (v_logWrites_1305_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1302_, v_env_1297_, v___f_1307_, v_asyncMode_1304_, v_declName_1298_, v___x_1308_);
lean_dec(v_asyncMode_1304_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_inc(v_declName_1298_);
v___x_1310_ = l_Lean_Environment_logDeclChange(v_env_1297_, v_declName_1298_);
v___x_1311_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1302_, v___x_1310_, v___f_1307_, v_asyncMode_1304_, v_declName_1298_, v___x_1308_);
lean_dec(v_asyncMode_1304_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___redArg___boxed(lean_object* v_ext_1359_, lean_object* v_env_1360_, lean_object* v_declName_1361_, lean_object* v_val_1362_, lean_object* v_allowOverwrite_1363_){
_start:
{
uint8_t v_allowOverwrite_boxed_1364_; lean_object* v_res_1365_; 
v_allowOverwrite_boxed_1364_ = lean_unbox(v_allowOverwrite_1363_);
v_res_1365_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1359_, v_env_1360_, v_declName_1361_, v_val_1362_, v_allowOverwrite_boxed_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert(lean_object* v_00_u03b1_1366_, lean_object* v_ext_1367_, lean_object* v_env_1368_, lean_object* v_declName_1369_, lean_object* v_val_1370_, uint8_t v_allowOverwrite_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_MapDeclarationExtension_insert___redArg(v_ext_1367_, v_env_1368_, v_declName_1369_, v_val_1370_, v_allowOverwrite_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_insert___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_ext_1374_, lean_object* v_env_1375_, lean_object* v_declName_1376_, lean_object* v_val_1377_, lean_object* v_allowOverwrite_1378_){
_start:
{
uint8_t v_allowOverwrite_boxed_1379_; lean_object* v_res_1380_; 
v_allowOverwrite_boxed_1379_ = lean_unbox(v_allowOverwrite_1378_);
v_res_1380_ = l_Lean_MapDeclarationExtension_insert(v_00_u03b1_1373_, v_ext_1374_, v_env_1375_, v_declName_1376_, v_val_1377_, v_allowOverwrite_boxed_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object* v_ext_1381_, lean_object* v_env_1382_, lean_object* v_declName_1383_, lean_object* v_asyncMode_1384_, uint8_t v_level_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(1);
v___x_1387_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1382_, v_declName_1383_);
if (lean_obj_tag(v___x_1387_) == 0)
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = 0;
lean_inc(v_declName_1383_);
v___x_1389_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1386_, v_ext_1381_, v_env_1382_, v_asyncMode_1384_, v_declName_1383_, v___x_1388_);
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1389_, v_declName_1383_);
lean_dec(v_declName_1383_);
lean_dec(v___x_1389_);
return v___x_1390_;
}
else
{
lean_object* v_val_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_val_1391_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1392_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1386_, v_ext_1381_, v_env_1382_, v_val_1391_, v_level_1385_);
lean_dec(v_val_1391_);
lean_dec_ref(v_env_1382_);
v___x_1393_ = l_Lean_findSortedByName_x3f___redArg(v___x_1392_, v_declName_1383_);
lean_dec(v_declName_1383_);
lean_dec_ref(v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
lean_object* v_val_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1403_; 
v_val_1395_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1397_ = v___x_1393_;
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_val_1395_);
lean_dec(v___x_1393_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_snd_1399_; lean_object* v___x_1401_; 
v_snd_1399_ = lean_ctor_get(v_val_1395_, 1);
lean_inc(v_snd_1399_);
lean_dec(v_val_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_snd_1399_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_snd_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg___boxed(lean_object* v_ext_1404_, lean_object* v_env_1405_, lean_object* v_declName_1406_, lean_object* v_asyncMode_1407_, lean_object* v_level_1408_){
_start:
{
uint8_t v_level_boxed_1409_; lean_object* v_res_1410_; 
v_level_boxed_1409_ = lean_unbox(v_level_1408_);
v_res_1410_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_ext_1404_, v_env_1405_, v_declName_1406_, v_asyncMode_1407_, v_level_boxed_1409_);
lean_dec(v_asyncMode_1407_);
lean_dec_ref(v_ext_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object* v_00_u03b1_1411_, lean_object* v_inst_1412_, lean_object* v_ext_1413_, lean_object* v_env_1414_, lean_object* v_declName_1415_, lean_object* v_asyncMode_1416_, uint8_t v_level_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v_ext_1413_, v_env_1414_, v_declName_1415_, v_asyncMode_1416_, v_level_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_find_x3f___boxed(lean_object* v_00_u03b1_1419_, lean_object* v_inst_1420_, lean_object* v_ext_1421_, lean_object* v_env_1422_, lean_object* v_declName_1423_, lean_object* v_asyncMode_1424_, lean_object* v_level_1425_){
_start:
{
uint8_t v_level_boxed_1426_; lean_object* v_res_1427_; 
v_level_boxed_1426_ = lean_unbox(v_level_1425_);
v_res_1427_ = l_Lean_MapDeclarationExtension_find_x3f(v_00_u03b1_1419_, v_inst_1420_, v_ext_1421_, v_env_1422_, v_declName_1423_, v_asyncMode_1424_, v_level_boxed_1426_);
lean_dec(v_asyncMode_1424_);
lean_dec_ref(v_ext_1421_);
lean_dec(v_inst_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object* v_ext_1428_, lean_object* v_env_1429_, lean_object* v_declName_1430_, lean_object* v_asyncMode_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_box(1);
v___x_1433_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1429_, v_declName_1430_);
if (lean_obj_tag(v___x_1433_) == 0)
{
uint8_t v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = 0;
lean_inc(v_declName_1430_);
v___x_1435_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1432_, v_ext_1428_, v_env_1429_, v_asyncMode_1431_, v_declName_1430_, v___x_1434_);
v___x_1436_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_1430_, v___x_1435_);
lean_dec(v___x_1435_);
lean_dec(v_declName_1430_);
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_val_1437_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1438_ = 0;
v___x_1439_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1432_, v_ext_1428_, v_env_1429_, v_val_1437_, v___x_1438_);
lean_dec(v_val_1437_);
lean_dec_ref(v_env_1429_);
v___x_1440_ = l_Lean_findSortedByName_x3f___redArg(v___x_1439_, v_declName_1430_);
lean_dec(v_declName_1430_);
lean_dec_ref(v___x_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
uint8_t v___x_1441_; 
v___x_1441_ = 0;
return v___x_1441_;
}
else
{
uint8_t v___x_1442_; 
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = 1;
return v___x_1442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___redArg___boxed(lean_object* v_ext_1443_, lean_object* v_env_1444_, lean_object* v_declName_1445_, lean_object* v_asyncMode_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Lean_MapDeclarationExtension_contains___redArg(v_ext_1443_, v_env_1444_, v_declName_1445_, v_asyncMode_1446_);
lean_dec(v_asyncMode_1446_);
lean_dec_ref(v_ext_1443_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT uint8_t l_Lean_MapDeclarationExtension_contains(lean_object* v_00_u03b1_1449_, lean_object* v_inst_1450_, lean_object* v_ext_1451_, lean_object* v_env_1452_, lean_object* v_declName_1453_, lean_object* v_asyncMode_1454_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = l_Lean_MapDeclarationExtension_contains___redArg(v_ext_1451_, v_env_1452_, v_declName_1453_, v_asyncMode_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MapDeclarationExtension_contains___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_inst_1457_, lean_object* v_ext_1458_, lean_object* v_env_1459_, lean_object* v_declName_1460_, lean_object* v_asyncMode_1461_){
_start:
{
uint8_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = l_Lean_MapDeclarationExtension_contains(v_00_u03b1_1456_, v_inst_1457_, v_ext_1458_, v_env_1459_, v_declName_1460_, v_asyncMode_1461_);
lean_dec(v_asyncMode_1461_);
lean_dec_ref(v_ext_1458_);
lean_dec(v_inst_1457_);
v_r_1463_ = lean_box(v_res_1462_);
return v_r_1463_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
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
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
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
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_EnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
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
