// Lean compiler output
// Module: Lake.Config.WorkspaceConfig
// Imports: public import Lake.Config.Defaults public import Lake.Config.MetaClasses meta import all Lake.Config.Meta import Lake.Config.Meta
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
extern lean_object* l_Lake_defaultPackagesDir;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedWorkspaceConfig_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedWorkspaceConfig;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprWorkspaceConfig_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "packagesDir"};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11;
static lean_once_cell_t l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprWorkspaceConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprWorkspaceConfig_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprWorkspaceConfig___closed__0 = (const lean_object*)&l_Lake_instReprWorkspaceConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprWorkspaceConfig = (const lean_object*)&l_Lake_instReprWorkspaceConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_WorkspaceConfig_packagesDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___closed__0 = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__0_value;
static const lean_closure_object l_Lake_WorkspaceConfig_packagesDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___closed__1 = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__1_value;
static const lean_closure_object l_Lake_WorkspaceConfig_packagesDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_WorkspaceConfig_packagesDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___closed__2 = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__2_value;
static const lean_closure_object l_Lake_WorkspaceConfig_packagesDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___closed__3 = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__0_value),((lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__1_value),((lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__2_value),((lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__3_value)}};
static const lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___closed__4 = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_WorkspaceConfig_packagesDir___proj = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_WorkspaceConfig_packagesDir_instConfigField = (const lean_object*)&l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value;
static const lean_array_object l_Lake_WorkspaceConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_WorkspaceConfig___fields___closed__0 = (const lean_object*)&l_Lake_WorkspaceConfig___fields___closed__0_value;
static const lean_ctor_object l_Lake_WorkspaceConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 147, 205, 88, 160, 133, 8, 11)}};
static const lean_object* l_Lake_WorkspaceConfig___fields___closed__1 = (const lean_object*)&l_Lake_WorkspaceConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_WorkspaceConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_WorkspaceConfig___fields___closed__1_value),((lean_object*)&l_Lake_WorkspaceConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_WorkspaceConfig___fields___closed__2 = (const lean_object*)&l_Lake_WorkspaceConfig___fields___closed__2_value;
static lean_once_cell_t l_Lake_WorkspaceConfig___fields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_WorkspaceConfig___fields___closed__3;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig___fields;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigFields;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__0;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__1_value;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__2_value;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__3_value;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__4_value;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__5_value;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__6_value;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_WorkspaceConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_WorkspaceConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_WorkspaceConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__10_value;
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_WorkspaceConfig_instConfigInfo___closed__11;
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__12;
static const lean_closure_object l_Lake_WorkspaceConfig_instConfigInfo___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_WorkspaceConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__13 = (const lean_object*)&l_Lake_WorkspaceConfig_instConfigInfo___closed__13_value;
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_WorkspaceConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_WorkspaceConfig_instConfigInfo___closed__15;
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__16;
static lean_once_cell_t l_Lake_WorkspaceConfig_instConfigInfo___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_WorkspaceConfig_instConfigInfo___closed__17;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instEmptyCollection;
static lean_object* _init_l_Lake_instInhabitedWorkspaceConfig_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lake_defaultPackagesDir;
return v___x_1_;
}
}
static lean_object* _init_l_Lake_instInhabitedWorkspaceConfig(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Lake_defaultPackagesDir;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprWorkspaceConfig_repr_spec__0(lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_nat_to_int(v_a_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(15u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0));
v___x_25_ = lean_string_length(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11, &l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11_once, _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11);
v___x_27_ = lean_nat_to_int(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig_repr___redArg(lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_33_ = ((lean_object*)(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6));
v___x_34_ = lean_obj_once(&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7, &l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = ((lean_object*)(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9));
v___x_37_ = l_String_quote(v_x_32_);
v___x_38_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
v___x_39_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_36_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = l_Repr_addAppParen(v___x_39_, v___x_35_);
v___x_41_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_34_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = 0;
v___x_43_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*1, v___x_42_);
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_33_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = lean_obj_once(&l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12, &l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12_once, _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12);
v___x_46_ = ((lean_object*)(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13));
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_44_);
v___x_48_ = ((lean_object*)(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14));
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_47_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_45_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*1, v___x_42_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig_repr(lean_object* v_x_52_, lean_object* v_prec_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lake_instReprWorkspaceConfig_repr___redArg(v_x_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig_repr___boxed(lean_object* v_x_55_, lean_object* v_prec_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lake_instReprWorkspaceConfig_repr(v_x_55_, v_prec_56_);
lean_dec(v_prec_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(lean_object* v_cfg_60_){
_start:
{
lean_inc_ref(v_cfg_60_);
return v_cfg_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed(lean_object* v_cfg_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(v_cfg_61_);
lean_dec_ref(v_cfg_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(lean_object* v_val_63_, lean_object* v_cfg_64_){
_start:
{
lean_inc_ref(v_val_63_);
return v_val_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed(lean_object* v_val_65_, lean_object* v_cfg_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(v_val_65_, v_cfg_66_);
lean_dec_ref(v_cfg_66_);
lean_dec_ref(v_val_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__2(lean_object* v_f_68_, lean_object* v_cfg_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_apply_1(v_f_68_, v_cfg_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(lean_object* v_x_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lake_defaultPackagesDir;
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed(lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(v_x_73_);
lean_dec_ref(v_x_73_);
return v_res_74_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l_Lake_WorkspaceConfig___fields___closed__2));
v___x_95_ = ((lean_object*)(l_Lake_WorkspaceConfig___fields___closed__0));
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig___fields(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lake_WorkspaceConfig___fields___closed__3, &l_Lake_WorkspaceConfig___fields___closed__3_once, _init_l_Lake_WorkspaceConfig___fields___closed__3);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigFields(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lake_WorkspaceConfig___fields;
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigInfo___lam__0(lean_object* v_x1_99_, lean_object* v_x2_100_){
_start:
{
lean_object* v_name_101_; lean_object* v___x_102_; 
v_name_101_ = lean_ctor_get(v_x2_100_, 0);
lean_inc(v_name_101_);
v___x_102_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_101_, v_x2_100_, v_x1_99_);
return v___x_102_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = l_Lake_WorkspaceConfig___fields;
v___x_104_ = lean_array_get_size(v___x_103_);
return v___x_104_;
}
}
static uint8_t _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__0, &l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_dec_lt(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_box(1);
v___x_129_ = l_Lake_WorkspaceConfig___fields;
v___x_130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
static uint8_t _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__0, &l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0);
v___x_133_ = lean_nat_dec_le(v___x_132_, v___x_132_);
return v___x_133_;
}
}
static size_t _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_134_; size_t v___x_135_; 
v___x_134_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__0, &l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0);
v___x_135_ = lean_usize_of_nat(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_136_ = lean_box(1);
v___x_137_ = lean_usize_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__15, &l_Lake_WorkspaceConfig_instConfigInfo___closed__15_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__15);
v___x_138_ = ((size_t)0ULL);
v___x_139_ = l_Lake_WorkspaceConfig___fields;
v___f_140_ = ((lean_object*)(l_Lake_WorkspaceConfig_instConfigInfo___closed__13));
v___x_141_ = ((lean_object*)(l_Lake_WorkspaceConfig_instConfigInfo___closed__10));
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_141_, v___f_140_, v___x_139_, v___x_138_, v___x_137_, v___x_136_);
return v___x_142_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__16, &l_Lake_WorkspaceConfig_instConfigInfo___closed__16_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__16);
v___x_145_ = l_Lake_WorkspaceConfig___fields;
v___x_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_143_);
return v___x_146_;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_uint8_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__11, &l_Lake_WorkspaceConfig_instConfigInfo___closed__11_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__11);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__12, &l_Lake_WorkspaceConfig_instConfigInfo___closed__12_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__12);
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_uint8_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__14, &l_Lake_WorkspaceConfig_instConfigInfo___closed__14_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__14);
if (v___x_149_ == 0)
{
if (v___x_147_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__12, &l_Lake_WorkspaceConfig_instConfigInfo___closed__12_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__12);
return v___x_150_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__17, &l_Lake_WorkspaceConfig_instConfigInfo___closed__17_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__17);
return v___x_151_;
}
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lake_WorkspaceConfig_instConfigInfo___closed__17, &l_Lake_WorkspaceConfig_instConfigInfo___closed__17_once, _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__17);
return v___x_152_;
}
}
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instEmptyCollection(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lake_defaultPackagesDir;
return v___x_153_;
}
}
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_WorkspaceConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedWorkspaceConfig_default = _init_l_Lake_instInhabitedWorkspaceConfig_default();
lean_mark_persistent(l_Lake_instInhabitedWorkspaceConfig_default);
l_Lake_instInhabitedWorkspaceConfig = _init_l_Lake_instInhabitedWorkspaceConfig();
lean_mark_persistent(l_Lake_instInhabitedWorkspaceConfig);
l_Lake_WorkspaceConfig___fields = _init_l_Lake_WorkspaceConfig___fields();
lean_mark_persistent(l_Lake_WorkspaceConfig___fields);
l_Lake_WorkspaceConfig_instConfigFields = _init_l_Lake_WorkspaceConfig_instConfigFields();
lean_mark_persistent(l_Lake_WorkspaceConfig_instConfigFields);
l_Lake_WorkspaceConfig_instConfigInfo = _init_l_Lake_WorkspaceConfig_instConfigInfo();
lean_mark_persistent(l_Lake_WorkspaceConfig_instConfigInfo);
l_Lake_WorkspaceConfig_instEmptyCollection = _init_l_Lake_WorkspaceConfig_instEmptyCollection();
lean_mark_persistent(l_Lake_WorkspaceConfig_instEmptyCollection);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_WorkspaceConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_WorkspaceConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_WorkspaceConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_WorkspaceConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_WorkspaceConfig(builtin);
}
#ifdef __cplusplus
}
#endif
