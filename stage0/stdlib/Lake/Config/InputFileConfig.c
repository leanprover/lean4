// Lean compiler output
// Module: Lake.Config.InputFileConfig
// Imports: public import Lake.Config.Pattern public import Lake.Config.MetaClasses public import Init.Data.ToString.Name meta import all Lake.Config.Meta import Lake.Config.Meta
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Pattern_star___redArg();
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_InputFileConfig_path___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_path___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_path___proj___closed__0 = (const lean_object*)&l_Lake_InputFileConfig_path___proj___closed__0_value;
static const lean_closure_object l_Lake_InputFileConfig_path___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_path___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_path___proj___closed__1 = (const lean_object*)&l_Lake_InputFileConfig_path___proj___closed__1_value;
static const lean_closure_object l_Lake_InputFileConfig_path___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_path___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_path___proj___closed__2 = (const lean_object*)&l_Lake_InputFileConfig_path___proj___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path_instConfigField(lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_InputFileConfig_text___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___redArg___closed__0 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_InputFileConfig_text___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___redArg___closed__1 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_InputFileConfig_text___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___redArg___closed__2 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_InputFileConfig_text___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___redArg___closed__3 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_InputFileConfig_text___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__0_value),((lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__1_value),((lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__2_value),((lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_InputFileConfig_text___proj___redArg___closed__4 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_InputFileConfig_text___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFileConfig_text___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___boxed(lean_object*);
static const lean_array_object l_Lake_InputFileConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_InputFileConfig___fields___closed__0 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__0_value;
static const lean_string_object l_Lake_InputFileConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lake_InputFileConfig___fields___closed__1 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_InputFileConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputFileConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 173, 251, 55, 140, 124, 51, 22)}};
static const lean_object* l_Lake_InputFileConfig___fields___closed__2 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__2_value;
static const lean_ctor_object l_Lake_InputFileConfig___fields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig___fields___closed__2_value),((lean_object*)&l_Lake_InputFileConfig___fields___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_InputFileConfig___fields___closed__3 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__3_value;
static lean_once_cell_t l_Lake_InputFileConfig___fields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFileConfig___fields___closed__4;
static const lean_string_object l_Lake_InputFileConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lake_InputFileConfig___fields___closed__5 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_InputFileConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputFileConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(26, 32, 191, 158, 22, 157, 236, 165)}};
static const lean_object* l_Lake_InputFileConfig___fields___closed__6 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__6_value;
static const lean_ctor_object l_Lake_InputFileConfig___fields___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig___fields___closed__6_value),((lean_object*)&l_Lake_InputFileConfig___fields___closed__6_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_InputFileConfig___fields___closed__7 = (const lean_object*)&l_Lake_InputFileConfig___fields___closed__7_value;
static lean_once_cell_t l_Lake_InputFileConfig___fields___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFileConfig___fields___closed__8;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig___fields;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___redArg();
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_InputFileConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__0;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__1_value;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__2_value;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__3_value;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__4_value;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__5_value;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__6_value;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_InputFileConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_InputFileConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_InputFileConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__10_value;
static lean_once_cell_t l_Lake_InputFileConfig_instConfigInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_InputFileConfig_instConfigInfo___closed__11;
static const lean_closure_object l_Lake_InputFileConfig_instConfigInfo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__12 = (const lean_object*)&l_Lake_InputFileConfig_instConfigInfo___closed__12_value;
static lean_once_cell_t l_Lake_InputFileConfig_instConfigInfo___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_InputFileConfig_instConfigInfo___closed__13;
static lean_once_cell_t l_Lake_InputFileConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__14;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_InputDirConfig_path___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_path___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_path___proj___closed__0 = (const lean_object*)&l_Lake_InputDirConfig_path___proj___closed__0_value;
static const lean_closure_object l_Lake_InputDirConfig_path___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_path___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_path___proj___closed__1 = (const lean_object*)&l_Lake_InputDirConfig_path___proj___closed__1_value;
static const lean_closure_object l_Lake_InputDirConfig_path___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_path___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_path___proj___closed__2 = (const lean_object*)&l_Lake_InputDirConfig_path___proj___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path_instConfigField(lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_InputDirConfig_text___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___redArg___closed__0 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_InputDirConfig_text___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___redArg___closed__1 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_InputDirConfig_text___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___redArg___closed__2 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_InputDirConfig_text___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___redArg___closed__3 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_InputDirConfig_text___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__0_value),((lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__1_value),((lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__2_value),((lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_InputDirConfig_text___proj___redArg___closed__4 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_InputDirConfig_text___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_text___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___redArg___closed__0 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___redArg___closed__1 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___redArg___closed__2 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___redArg___closed__3 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_InputDirConfig_filter___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__0_value),((lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__1_value),((lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__2_value),((lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_InputDirConfig_filter___proj___redArg___closed__4 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_InputDirConfig_filter___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_filter___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___boxed(lean_object*);
static const lean_string_object l_Lake_InputDirConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "filter"};
static const lean_object* l_Lake_InputDirConfig___fields___closed__0 = (const lean_object*)&l_Lake_InputDirConfig___fields___closed__0_value;
static const lean_ctor_object l_Lake_InputDirConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputDirConfig___fields___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 153, 84, 166, 255, 252, 251, 161)}};
static const lean_object* l_Lake_InputDirConfig___fields___closed__1 = (const lean_object*)&l_Lake_InputDirConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_InputDirConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputDirConfig___fields___closed__1_value),((lean_object*)&l_Lake_InputDirConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_InputDirConfig___fields___closed__2 = (const lean_object*)&l_Lake_InputDirConfig___fields___closed__2_value;
static lean_once_cell_t l_Lake_InputDirConfig___fields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig___fields___closed__3;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig___fields;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg();
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___boxed(lean_object*);
static lean_once_cell_t l_Lake_InputDirConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_instConfigInfo___closed__0;
static lean_once_cell_t l_Lake_InputDirConfig_instConfigInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_InputDirConfig_instConfigInfo___closed__1;
static lean_once_cell_t l_Lake_InputDirConfig_instConfigInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_InputDirConfig_instConfigInfo___closed__2;
static lean_once_cell_t l_Lake_InputDirConfig_instConfigInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_instConfigInfo___closed__3;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__0(lean_object* v_cfg_1_){
_start:
{
lean_object* v_path_2_; 
v_path_2_ = lean_ctor_get(v_cfg_1_, 0);
lean_inc_ref(v_path_2_);
return v_path_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__0___boxed(lean_object* v_cfg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_InputFileConfig_path___proj___lam__0(v_cfg_3_);
lean_dec_ref(v_cfg_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__1(lean_object* v_val_5_, lean_object* v_cfg_6_){
_start:
{
uint8_t v_text_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_14_; 
v_text_7_ = lean_ctor_get_uint8(v_cfg_6_, sizeof(void*)*1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_cfg_6_);
if (v_isSharedCheck_14_ == 0)
{
lean_object* v_unused_15_; 
v_unused_15_ = lean_ctor_get(v_cfg_6_, 0);
lean_dec(v_unused_15_);
v___x_9_ = v_cfg_6_;
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
else
{
lean_dec(v_cfg_6_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 0, v_val_5_);
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_val_5_);
lean_ctor_set_uint8(v_reuseFailAlloc_13_, sizeof(void*)*1, v_text_7_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__2(lean_object* v_f_16_, lean_object* v_cfg_17_){
_start:
{
lean_object* v_path_18_; uint8_t v_text_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_27_; 
v_path_18_ = lean_ctor_get(v_cfg_17_, 0);
v_text_19_ = lean_ctor_get_uint8(v_cfg_17_, sizeof(void*)*1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_cfg_17_);
if (v_isSharedCheck_27_ == 0)
{
v___x_21_ = v_cfg_17_;
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_path_18_);
lean_dec(v_cfg_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_apply_1(v_f_16_, v_path_18_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_23_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_26_, sizeof(void*)*1, v_text_19_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__3(lean_object* v_name_28_, lean_object* v_x_29_){
_start:
{
uint8_t v___x_30_; lean_object* v___x_31_; 
v___x_30_ = 0;
v___x_31_ = l_Lean_Name_toString(v_name_28_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj___lam__3___boxed(lean_object* v_name_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_InputFileConfig_path___proj___lam__3(v_name_32_, v_x_33_);
lean_dec_ref(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path___proj(lean_object* v_name_38_){
_start:
{
lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v___f_39_ = ((lean_object*)(l_Lake_InputFileConfig_path___proj___closed__0));
v___f_40_ = ((lean_object*)(l_Lake_InputFileConfig_path___proj___closed__1));
v___f_41_ = ((lean_object*)(l_Lake_InputFileConfig_path___proj___closed__2));
v___f_42_ = lean_alloc_closure((void*)(l_Lake_InputFileConfig_path___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_42_, 0, v_name_38_);
v___x_43_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_43_, 0, v___f_39_);
lean_ctor_set(v___x_43_, 1, v___f_40_);
lean_ctor_set(v___x_43_, 2, v___f_41_);
lean_ctor_set(v___x_43_, 3, v___f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_path_instConfigField(lean_object* v_name_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lake_InputFileConfig_path___proj(v_name_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___redArg___lam__0(lean_object* v_cfg_46_){
_start:
{
uint8_t v_text_47_; 
v_text_47_ = lean_ctor_get_uint8(v_cfg_46_, sizeof(void*)*1);
return v_text_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__0___boxed(lean_object* v_cfg_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lake_InputFileConfig_text___proj___redArg___lam__0(v_cfg_48_);
lean_dec_ref(v_cfg_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__1(uint8_t v_val_51_, lean_object* v_cfg_52_){
_start:
{
lean_object* v_path_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_path_53_ = lean_ctor_get(v_cfg_52_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_cfg_52_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v_cfg_52_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_path_53_);
lean_dec(v_cfg_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_path_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*1, v_val_51_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__1___boxed(lean_object* v_val_61_, lean_object* v_cfg_62_){
_start:
{
uint8_t v_val_42__boxed_63_; lean_object* v_res_64_; 
v_val_42__boxed_63_ = lean_unbox(v_val_61_);
v_res_64_ = l_Lake_InputFileConfig_text___proj___redArg___lam__1(v_val_42__boxed_63_, v_cfg_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__2(lean_object* v_f_65_, lean_object* v_cfg_66_){
_start:
{
lean_object* v_path_67_; uint8_t v_text_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_78_; 
v_path_67_ = lean_ctor_get(v_cfg_66_, 0);
v_text_68_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_cfg_66_);
if (v_isSharedCheck_78_ == 0)
{
v___x_70_ = v_cfg_66_;
v_isShared_71_ = v_isSharedCheck_78_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_path_67_);
lean_dec(v_cfg_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_78_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_72_ = lean_box(v_text_68_);
v___x_73_ = lean_apply_1(v_f_65_, v___x_72_);
if (v_isShared_71_ == 0)
{
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_path_67_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
uint8_t v___x_76_; 
v___x_76_ = lean_unbox(v___x_73_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_76_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___redArg___lam__3(lean_object* v_x_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__3___boxed(lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lake_InputFileConfig_text___proj___redArg___lam__3(v_x_81_);
lean_dec_ref(v_x_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_Lake_InputFileConfig_text___proj___redArg___closed__4));
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_InputFileConfig_text___proj___redArg();
return v_res_96_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_text___proj___closed__0(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lake_InputFileConfig_text___proj___redArg();
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj(lean_object* v_name_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lake_InputFileConfig_text___proj___closed__0, &l_Lake_InputFileConfig_text___proj___closed__0_once, _init_l_Lake_InputFileConfig_text___proj___closed__0);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___boxed(lean_object* v_name_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lake_InputFileConfig_text___proj(v_name_100_);
lean_dec(v_name_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___redArg(){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lake_InputFileConfig_text___proj___closed__0, &l_Lake_InputFileConfig_text___proj___closed__0_once, _init_l_Lake_InputFileConfig_text___proj___closed__0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___redArg___boxed(lean_object* v___dummy_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lake_InputFileConfig_text_instConfigField___redArg();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField(lean_object* v_name_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lake_InputFileConfig_text___proj___closed__0, &l_Lake_InputFileConfig_text___proj___closed__0_once, _init_l_Lake_InputFileConfig_text___proj___closed__0);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___boxed(lean_object* v_name_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lake_InputFileConfig_text_instConfigField(v_name_108_);
lean_dec(v_name_108_);
return v_res_109_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__3));
v___x_120_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__0));
v___x_121_ = lean_array_push(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__7));
v___x_130_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__4, &l_Lake_InputFileConfig___fields___closed__4_once, _init_l_Lake_InputFileConfig___fields___closed__4);
v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lake_InputFileConfig___fields;
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lake_InputFileConfig_instConfigFields___redArg();
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields(lean_object* v_name_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lake_InputFileConfig___fields;
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___boxed(lean_object* v_name_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_InputFileConfig_instConfigFields(v_name_139_);
lean_dec(v_name_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigInfo___lam__0(lean_object* v_x1_141_, lean_object* v_x2_142_){
_start:
{
lean_object* v_name_143_; lean_object* v___x_144_; 
v_name_143_ = lean_ctor_get(v_x2_142_, 0);
lean_inc(v_name_143_);
v___x_144_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_143_, v_x2_142_, v_x1_141_);
return v___x_144_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = l_Lake_InputFileConfig___fields;
v___x_146_ = lean_array_get_size(v___x_145_);
return v___x_146_;
}
}
static uint8_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_nat_dec_lt(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static size_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_170_; size_t v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_171_ = lean_usize_of_nat(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_172_ = lean_box(1);
v___x_173_ = lean_usize_once(&l_Lake_InputFileConfig_instConfigInfo___closed__13, &l_Lake_InputFileConfig_instConfigInfo___closed__13_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__13);
v___x_174_ = ((size_t)0ULL);
v___x_175_ = l_Lake_InputFileConfig___fields;
v___f_176_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_177_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_177_, v___f_176_, v___x_175_, v___x_174_, v___x_173_, v___x_172_);
return v___x_178_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_179_; lean_object* v___y_181_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_179_ = l_Lake_InputFileConfig___fields;
v___x_184_ = lean_box(1);
v___x_185_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__11, &l_Lake_InputFileConfig_instConfigInfo___closed__11_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__11);
if (v___x_185_ == 0)
{
v___y_181_ = v___x_184_;
goto v___jp_180_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__14, &l_Lake_InputFileConfig_instConfigInfo___closed__14_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__14);
v___y_181_ = v___x_186_;
goto v___jp_180_;
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_181_);
v___x_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_179_);
lean_ctor_set(v___x_183_, 1, v___y_181_);
lean_ctor_set(v___x_183_, 2, v___x_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instEmptyCollection(lean_object* v_name_187_){
_start:
{
uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = 0;
v___x_189_ = l_Lean_Name_toString(v_name_187_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0(lean_object* v_cfg_191_){
_start:
{
lean_object* v_path_192_; 
v_path_192_ = lean_ctor_get(v_cfg_191_, 0);
lean_inc_ref(v_path_192_);
return v_path_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0___boxed(lean_object* v_cfg_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lake_InputDirConfig_path___proj___lam__0(v_cfg_193_);
lean_dec_ref(v_cfg_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__1(lean_object* v_val_195_, lean_object* v_cfg_196_){
_start:
{
uint8_t v_text_197_; lean_object* v_filter_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_text_197_ = lean_ctor_get_uint8(v_cfg_196_, sizeof(void*)*2);
v_filter_198_ = lean_ctor_get(v_cfg_196_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_cfg_196_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_cfg_196_, 0);
lean_dec(v_unused_206_);
v___x_200_ = v_cfg_196_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_filter_198_);
lean_dec(v_cfg_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v_val_195_);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_val_195_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_filter_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*2, v_text_197_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__2(lean_object* v_f_207_, lean_object* v_cfg_208_){
_start:
{
lean_object* v_path_209_; uint8_t v_text_210_; lean_object* v_filter_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
v_path_209_ = lean_ctor_get(v_cfg_208_, 0);
v_text_210_ = lean_ctor_get_uint8(v_cfg_208_, sizeof(void*)*2);
v_filter_211_ = lean_ctor_get(v_cfg_208_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_cfg_208_);
if (v_isSharedCheck_219_ == 0)
{
v___x_213_ = v_cfg_208_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_filter_211_);
lean_inc(v_path_209_);
lean_dec(v_cfg_208_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_apply_1(v_f_207_, v_path_209_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_filter_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*2, v_text_210_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3(lean_object* v_name_220_, lean_object* v_x_221_){
_start:
{
uint8_t v___x_222_; lean_object* v___x_223_; 
v___x_222_ = 0;
v___x_223_ = l_Lean_Name_toString(v_name_220_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3___boxed(lean_object* v_name_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lake_InputDirConfig_path___proj___lam__3(v_name_224_, v_x_225_);
lean_dec_ref(v_x_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj(lean_object* v_name_230_){
_start:
{
lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; 
v___f_231_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__0));
v___f_232_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__1));
v___f_233_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__2));
v___f_234_ = lean_alloc_closure((void*)(l_Lake_InputDirConfig_path___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_234_, 0, v_name_230_);
v___x_235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_235_, 0, v___f_231_);
lean_ctor_set(v___x_235_, 1, v___f_232_);
lean_ctor_set(v___x_235_, 2, v___f_233_);
lean_ctor_set(v___x_235_, 3, v___f_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path_instConfigField(lean_object* v_name_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lake_InputDirConfig_path___proj(v_name_236_);
return v___x_237_;
}
}
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__0(lean_object* v_cfg_238_){
_start:
{
uint8_t v_text_239_; 
v_text_239_ = lean_ctor_get_uint8(v_cfg_238_, sizeof(void*)*2);
return v_text_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__0___boxed(lean_object* v_cfg_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lake_InputDirConfig_text___proj___redArg___lam__0(v_cfg_240_);
lean_dec_ref(v_cfg_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1(uint8_t v_val_243_, lean_object* v_cfg_244_){
_start:
{
lean_object* v_path_245_; lean_object* v_filter_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_path_245_ = lean_ctor_get(v_cfg_244_, 0);
v_filter_246_ = lean_ctor_get(v_cfg_244_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_cfg_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v_cfg_244_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_filter_246_);
lean_inc(v_path_245_);
lean_dec(v_cfg_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_path_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_filter_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*2, v_val_243_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1___boxed(lean_object* v_val_254_, lean_object* v_cfg_255_){
_start:
{
uint8_t v_val_45__boxed_256_; lean_object* v_res_257_; 
v_val_45__boxed_256_ = lean_unbox(v_val_254_);
v_res_257_ = l_Lake_InputDirConfig_text___proj___redArg___lam__1(v_val_45__boxed_256_, v_cfg_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__2(lean_object* v_f_258_, lean_object* v_cfg_259_){
_start:
{
lean_object* v_path_260_; uint8_t v_text_261_; lean_object* v_filter_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_272_; 
v_path_260_ = lean_ctor_get(v_cfg_259_, 0);
v_text_261_ = lean_ctor_get_uint8(v_cfg_259_, sizeof(void*)*2);
v_filter_262_ = lean_ctor_get(v_cfg_259_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_cfg_259_);
if (v_isSharedCheck_272_ == 0)
{
v___x_264_ = v_cfg_259_;
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_filter_262_);
lean_inc(v_path_260_);
lean_dec(v_cfg_259_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = lean_box(v_text_261_);
v___x_267_ = lean_apply_1(v_f_258_, v___x_266_);
if (v_isShared_265_ == 0)
{
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_path_260_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_filter_262_);
v___x_269_ = v_reuseFailAlloc_271_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
uint8_t v___x_270_; 
v___x_270_ = lean_unbox(v___x_267_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*2, v___x_270_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__3(lean_object* v_x_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__3___boxed(lean_object* v_x_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Lake_InputDirConfig_text___proj___redArg___lam__3(v_x_275_);
lean_dec_ref(v_x_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg(){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lake_InputDirConfig_text___proj___redArg___closed__4));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___boxed(lean_object* v___dummy_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lake_InputDirConfig_text___proj___redArg();
return v_res_290_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_text___proj___closed__0(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lake_InputDirConfig_text___proj___redArg();
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj(lean_object* v_name_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___boxed(lean_object* v_name_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_InputDirConfig_text___proj(v_name_294_);
lean_dec(v_name_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg(){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg___boxed(lean_object* v___dummy_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lake_InputDirConfig_text_instConfigField___redArg();
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField(lean_object* v_name_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___boxed(lean_object* v_name_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lake_InputDirConfig_text_instConfigField(v_name_302_);
lean_dec(v_name_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0(lean_object* v_cfg_304_){
_start:
{
lean_object* v_filter_305_; 
v_filter_305_ = lean_ctor_get(v_cfg_304_, 1);
lean_inc_ref(v_filter_305_);
return v_filter_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0___boxed(lean_object* v_cfg_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lake_InputDirConfig_filter___proj___redArg___lam__0(v_cfg_306_);
lean_dec_ref(v_cfg_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__1(lean_object* v_val_308_, lean_object* v_cfg_309_){
_start:
{
lean_object* v_path_310_; uint8_t v_text_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_path_310_ = lean_ctor_get(v_cfg_309_, 0);
v_text_311_ = lean_ctor_get_uint8(v_cfg_309_, sizeof(void*)*2);
v_isSharedCheck_318_ = !lean_is_exclusive(v_cfg_309_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v_cfg_309_, 1);
lean_dec(v_unused_319_);
v___x_313_ = v_cfg_309_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_path_310_);
lean_dec(v_cfg_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_val_308_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_path_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_val_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_317_, sizeof(void*)*2, v_text_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__2(lean_object* v_f_320_, lean_object* v_cfg_321_){
_start:
{
lean_object* v_path_322_; uint8_t v_text_323_; lean_object* v_filter_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_path_322_ = lean_ctor_get(v_cfg_321_, 0);
v_text_323_ = lean_ctor_get_uint8(v_cfg_321_, sizeof(void*)*2);
v_filter_324_ = lean_ctor_get(v_cfg_321_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_cfg_321_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v_cfg_321_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_filter_324_);
lean_inc(v_path_322_);
lean_dec(v_cfg_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_apply_1(v_f_320_, v_filter_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_path_322_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*2, v_text_323_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lake_Pattern_star___redArg();
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3(lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3___boxed(lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lake_InputDirConfig_filter___proj___redArg___lam__3(v_x_336_);
lean_dec_ref(v_x_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg(){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = ((lean_object*)(l_Lake_InputDirConfig_filter___proj___redArg___closed__4));
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___boxed(lean_object* v___dummy_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lake_InputDirConfig_filter___proj___redArg();
return v_res_350_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___closed__0(void){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lake_InputDirConfig_filter___proj___redArg();
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj(lean_object* v_name_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___boxed(lean_object* v_name_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_InputDirConfig_filter___proj(v_name_354_);
lean_dec(v_name_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg(){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg___boxed(lean_object* v___dummy_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lake_InputDirConfig_filter_instConfigField___redArg();
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField(lean_object* v_name_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___boxed(lean_object* v_name_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lake_InputDirConfig_filter_instConfigField(v_name_362_);
lean_dec(v_name_362_);
return v_res_363_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lake_InputDirConfig___fields___closed__2));
v___x_372_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
v___x_373_ = lean_array_push(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_obj_once(&l_Lake_InputDirConfig___fields___closed__3, &l_Lake_InputDirConfig___fields___closed__3_once, _init_l_Lake_InputDirConfig___fields___closed__3);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lake_InputDirConfig___fields;
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lake_InputDirConfig_instConfigFields___redArg();
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields(lean_object* v_name_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lake_InputDirConfig___fields;
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___boxed(lean_object* v_name_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_InputDirConfig_instConfigFields(v_name_381_);
lean_dec(v_name_381_);
return v_res_382_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lake_InputDirConfig___fields;
v___x_384_ = lean_array_get_size(v___x_383_);
return v___x_384_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_385_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_nat_dec_lt(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static size_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_388_; size_t v___x_389_; 
v___x_388_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_389_ = lean_usize_of_nat(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_390_ = lean_box(1);
v___x_391_ = lean_usize_once(&l_Lake_InputDirConfig_instConfigInfo___closed__2, &l_Lake_InputDirConfig_instConfigInfo___closed__2_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__2);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l_Lake_InputDirConfig___fields;
v___f_394_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_395_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_395_, v___f_394_, v___x_393_, v___x_392_, v___x_391_, v___x_390_);
return v___x_396_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_397_; lean_object* v___y_399_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_397_ = l_Lake_InputDirConfig___fields;
v___x_402_ = lean_box(1);
v___x_403_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__1, &l_Lake_InputDirConfig_instConfigInfo___closed__1_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__1);
if (v___x_403_ == 0)
{
v___y_399_ = v___x_402_;
goto v___jp_398_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__3, &l_Lake_InputDirConfig_instConfigInfo___closed__3_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__3);
v___y_399_ = v___x_404_;
goto v___jp_398_;
}
v___jp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_399_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_397_);
lean_ctor_set(v___x_401_, 1, v___y_399_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instEmptyCollection(lean_object* v_name_405_){
_start:
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = 0;
v___x_407_ = l_Lean_Name_toString(v_name_405_, v___x_406_);
v___x_408_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0);
v___x_409_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*2, v___x_406_);
return v___x_409_;
}
}
lean_object* runtime_initialize_Lake_Config_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_InputFileConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_InputFileConfig___fields = _init_l_Lake_InputFileConfig___fields();
lean_mark_persistent(l_Lake_InputFileConfig___fields);
l_Lake_InputFileConfig_instConfigInfo = _init_l_Lake_InputFileConfig_instConfigInfo();
lean_mark_persistent(l_Lake_InputFileConfig_instConfigInfo);
l_Lake_InputDirConfig___fields = _init_l_Lake_InputDirConfig___fields();
lean_mark_persistent(l_Lake_InputDirConfig___fields);
l_Lake_InputDirConfig_instConfigInfo = _init_l_Lake_InputDirConfig_instConfigInfo();
lean_mark_persistent(l_Lake_InputDirConfig_instConfigInfo);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_InputFileConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Pattern(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_InputFileConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_InputFileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_InputFileConfig(builtin);
}
#ifdef __cplusplus
}
#endif
