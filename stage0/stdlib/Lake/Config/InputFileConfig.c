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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
static uint8_t l_Lake_InputFileConfig_instConfigInfo___closed__13;
static lean_once_cell_t l_Lake_InputFileConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_InputFileConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_InputFileConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFileConfig_instConfigInfo___closed__15;
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
static uint8_t l_Lake_InputDirConfig_instConfigInfo___closed__2;
static lean_once_cell_t l_Lake_InputDirConfig_instConfigInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_InputDirConfig_instConfigInfo___closed__3;
static lean_once_cell_t l_Lake_InputDirConfig_instConfigInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_instConfigInfo___closed__4;
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
static uint8_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_171_ = lean_nat_dec_le(v___x_170_, v___x_170_);
return v___x_171_;
}
}
static size_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_172_; size_t v___x_173_; 
v___x_172_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_173_ = lean_usize_of_nat(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_174_ = lean_box(1);
v___x_175_ = lean_usize_once(&l_Lake_InputFileConfig_instConfigInfo___closed__14, &l_Lake_InputFileConfig_instConfigInfo___closed__14_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__14);
v___x_176_ = ((size_t)0ULL);
v___x_177_ = l_Lake_InputFileConfig___fields;
v___f_178_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_179_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_179_, v___f_178_, v___x_177_, v___x_176_, v___x_175_, v___x_174_);
return v___x_180_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_181_ = l_Lake_InputFileConfig___fields;
v___x_186_ = lean_box(1);
v___x_187_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__11, &l_Lake_InputFileConfig_instConfigInfo___closed__11_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__11);
if (v___x_187_ == 0)
{
v___y_183_ = v___x_186_;
goto v___jp_182_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__13, &l_Lake_InputFileConfig_instConfigInfo___closed__13_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__13);
if (v___x_188_ == 0)
{
if (v___x_187_ == 0)
{
v___y_183_ = v___x_186_;
goto v___jp_182_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__15, &l_Lake_InputFileConfig_instConfigInfo___closed__15_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__15);
v___y_183_ = v___x_189_;
goto v___jp_182_;
}
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__15, &l_Lake_InputFileConfig_instConfigInfo___closed__15_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__15);
v___y_183_ = v___x_190_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_183_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_181_);
lean_ctor_set(v___x_185_, 1, v___y_183_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instEmptyCollection(lean_object* v_name_191_){
_start:
{
uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = 0;
v___x_193_ = l_Lean_Name_toString(v_name_191_, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0(lean_object* v_cfg_195_){
_start:
{
lean_object* v_path_196_; 
v_path_196_ = lean_ctor_get(v_cfg_195_, 0);
lean_inc_ref(v_path_196_);
return v_path_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0___boxed(lean_object* v_cfg_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lake_InputDirConfig_path___proj___lam__0(v_cfg_197_);
lean_dec_ref(v_cfg_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__1(lean_object* v_val_199_, lean_object* v_cfg_200_){
_start:
{
uint8_t v_text_201_; lean_object* v_filter_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_text_201_ = lean_ctor_get_uint8(v_cfg_200_, sizeof(void*)*2);
v_filter_202_ = lean_ctor_get(v_cfg_200_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_cfg_200_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v_cfg_200_, 0);
lean_dec(v_unused_210_);
v___x_204_ = v_cfg_200_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_filter_202_);
lean_dec(v_cfg_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v_val_199_);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_val_199_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_filter_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_208_, sizeof(void*)*2, v_text_201_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__2(lean_object* v_f_211_, lean_object* v_cfg_212_){
_start:
{
lean_object* v_path_213_; uint8_t v_text_214_; lean_object* v_filter_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_path_213_ = lean_ctor_get(v_cfg_212_, 0);
v_text_214_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*2);
v_filter_215_ = lean_ctor_get(v_cfg_212_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_cfg_212_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v_cfg_212_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_filter_215_);
lean_inc(v_path_213_);
lean_dec(v_cfg_212_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_apply_1(v_f_211_, v_path_213_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_filter_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_222_, sizeof(void*)*2, v_text_214_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3(lean_object* v_name_224_, lean_object* v_x_225_){
_start:
{
uint8_t v___x_226_; lean_object* v___x_227_; 
v___x_226_ = 0;
v___x_227_ = l_Lean_Name_toString(v_name_224_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3___boxed(lean_object* v_name_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lake_InputDirConfig_path___proj___lam__3(v_name_228_, v_x_229_);
lean_dec_ref(v_x_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj(lean_object* v_name_234_){
_start:
{
lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; 
v___f_235_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__0));
v___f_236_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__1));
v___f_237_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__2));
v___f_238_ = lean_alloc_closure((void*)(l_Lake_InputDirConfig_path___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_238_, 0, v_name_234_);
v___x_239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_239_, 0, v___f_235_);
lean_ctor_set(v___x_239_, 1, v___f_236_);
lean_ctor_set(v___x_239_, 2, v___f_237_);
lean_ctor_set(v___x_239_, 3, v___f_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path_instConfigField(lean_object* v_name_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lake_InputDirConfig_path___proj(v_name_240_);
return v___x_241_;
}
}
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__0(lean_object* v_cfg_242_){
_start:
{
uint8_t v_text_243_; 
v_text_243_ = lean_ctor_get_uint8(v_cfg_242_, sizeof(void*)*2);
return v_text_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__0___boxed(lean_object* v_cfg_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Lake_InputDirConfig_text___proj___redArg___lam__0(v_cfg_244_);
lean_dec_ref(v_cfg_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1(uint8_t v_val_247_, lean_object* v_cfg_248_){
_start:
{
lean_object* v_path_249_; lean_object* v_filter_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_path_249_ = lean_ctor_get(v_cfg_248_, 0);
v_filter_250_ = lean_ctor_get(v_cfg_248_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_cfg_248_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v_cfg_248_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_filter_250_);
lean_inc(v_path_249_);
lean_dec(v_cfg_248_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_path_249_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_filter_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*2, v_val_247_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1___boxed(lean_object* v_val_258_, lean_object* v_cfg_259_){
_start:
{
uint8_t v_val_45__boxed_260_; lean_object* v_res_261_; 
v_val_45__boxed_260_ = lean_unbox(v_val_258_);
v_res_261_ = l_Lake_InputDirConfig_text___proj___redArg___lam__1(v_val_45__boxed_260_, v_cfg_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__2(lean_object* v_f_262_, lean_object* v_cfg_263_){
_start:
{
lean_object* v_path_264_; uint8_t v_text_265_; lean_object* v_filter_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_276_; 
v_path_264_ = lean_ctor_get(v_cfg_263_, 0);
v_text_265_ = lean_ctor_get_uint8(v_cfg_263_, sizeof(void*)*2);
v_filter_266_ = lean_ctor_get(v_cfg_263_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_cfg_263_);
if (v_isSharedCheck_276_ == 0)
{
v___x_268_ = v_cfg_263_;
v_isShared_269_ = v_isSharedCheck_276_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_filter_266_);
lean_inc(v_path_264_);
lean_dec(v_cfg_263_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_276_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_box(v_text_265_);
v___x_271_ = lean_apply_1(v_f_262_, v___x_270_);
if (v_isShared_269_ == 0)
{
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_path_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_filter_266_);
v___x_273_ = v_reuseFailAlloc_275_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
uint8_t v___x_274_; 
v___x_274_ = lean_unbox(v___x_271_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*2, v___x_274_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__3(lean_object* v_x_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__3___boxed(lean_object* v_x_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Lake_InputDirConfig_text___proj___redArg___lam__3(v_x_279_);
lean_dec_ref(v_x_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg(){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = ((lean_object*)(l_Lake_InputDirConfig_text___proj___redArg___closed__4));
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___boxed(lean_object* v___dummy_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lake_InputDirConfig_text___proj___redArg();
return v_res_294_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_text___proj___closed__0(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lake_InputDirConfig_text___proj___redArg();
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj(lean_object* v_name_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___boxed(lean_object* v_name_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lake_InputDirConfig_text___proj(v_name_298_);
lean_dec(v_name_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg(){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg___boxed(lean_object* v___dummy_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lake_InputDirConfig_text_instConfigField___redArg();
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField(lean_object* v_name_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___boxed(lean_object* v_name_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lake_InputDirConfig_text_instConfigField(v_name_306_);
lean_dec(v_name_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0(lean_object* v_cfg_308_){
_start:
{
lean_object* v_filter_309_; 
v_filter_309_ = lean_ctor_get(v_cfg_308_, 1);
lean_inc_ref(v_filter_309_);
return v_filter_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0___boxed(lean_object* v_cfg_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lake_InputDirConfig_filter___proj___redArg___lam__0(v_cfg_310_);
lean_dec_ref(v_cfg_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__1(lean_object* v_val_312_, lean_object* v_cfg_313_){
_start:
{
lean_object* v_path_314_; uint8_t v_text_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_path_314_ = lean_ctor_get(v_cfg_313_, 0);
v_text_315_ = lean_ctor_get_uint8(v_cfg_313_, sizeof(void*)*2);
v_isSharedCheck_322_ = !lean_is_exclusive(v_cfg_313_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v_cfg_313_, 1);
lean_dec(v_unused_323_);
v___x_317_ = v_cfg_313_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_path_314_);
lean_dec(v_cfg_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v_val_312_);
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_path_314_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*2, v_text_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__2(lean_object* v_f_324_, lean_object* v_cfg_325_){
_start:
{
lean_object* v_path_326_; uint8_t v_text_327_; lean_object* v_filter_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_path_326_ = lean_ctor_get(v_cfg_325_, 0);
v_text_327_ = lean_ctor_get_uint8(v_cfg_325_, sizeof(void*)*2);
v_filter_328_ = lean_ctor_get(v_cfg_325_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_cfg_325_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v_cfg_325_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_filter_328_);
lean_inc(v_path_326_);
lean_dec(v_cfg_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_apply_1(v_f_324_, v_filter_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_path_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*2, v_text_327_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lake_Pattern_star___redArg();
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3(lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3___boxed(lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lake_InputDirConfig_filter___proj___redArg___lam__3(v_x_340_);
lean_dec_ref(v_x_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg(){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_Lake_InputDirConfig_filter___proj___redArg___closed__4));
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___boxed(lean_object* v___dummy_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lake_InputDirConfig_filter___proj___redArg();
return v_res_354_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___closed__0(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lake_InputDirConfig_filter___proj___redArg();
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj(lean_object* v_name_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___boxed(lean_object* v_name_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lake_InputDirConfig_filter___proj(v_name_358_);
lean_dec(v_name_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg(){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg___boxed(lean_object* v___dummy_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lake_InputDirConfig_filter_instConfigField___redArg();
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField(lean_object* v_name_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___boxed(lean_object* v_name_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lake_InputDirConfig_filter_instConfigField(v_name_366_);
lean_dec(v_name_366_);
return v_res_367_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l_Lake_InputDirConfig___fields___closed__2));
v___x_376_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
v___x_377_ = lean_array_push(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lake_InputDirConfig___fields___closed__3, &l_Lake_InputDirConfig___fields___closed__3_once, _init_l_Lake_InputDirConfig___fields___closed__3);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lake_InputDirConfig___fields;
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_InputDirConfig_instConfigFields___redArg();
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields(lean_object* v_name_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lake_InputDirConfig___fields;
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___boxed(lean_object* v_name_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lake_InputDirConfig_instConfigFields(v_name_385_);
lean_dec(v_name_385_);
return v_res_386_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = l_Lake_InputDirConfig___fields;
v___x_388_ = lean_array_get_size(v___x_387_);
return v___x_388_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_dec_lt(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_393_ = lean_nat_dec_le(v___x_392_, v___x_392_);
return v___x_393_;
}
}
static size_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_394_; size_t v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_395_ = lean_usize_of_nat(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_396_ = lean_box(1);
v___x_397_ = lean_usize_once(&l_Lake_InputDirConfig_instConfigInfo___closed__3, &l_Lake_InputDirConfig_instConfigInfo___closed__3_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__3);
v___x_398_ = ((size_t)0ULL);
v___x_399_ = l_Lake_InputDirConfig___fields;
v___f_400_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_401_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_401_, v___f_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_402_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_403_; lean_object* v___y_405_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_403_ = l_Lake_InputDirConfig___fields;
v___x_408_ = lean_box(1);
v___x_409_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__1, &l_Lake_InputDirConfig_instConfigInfo___closed__1_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__1);
if (v___x_409_ == 0)
{
v___y_405_ = v___x_408_;
goto v___jp_404_;
}
else
{
uint8_t v___x_410_; 
v___x_410_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__2, &l_Lake_InputDirConfig_instConfigInfo___closed__2_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__2);
if (v___x_410_ == 0)
{
if (v___x_409_ == 0)
{
v___y_405_ = v___x_408_;
goto v___jp_404_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__4, &l_Lake_InputDirConfig_instConfigInfo___closed__4_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__4);
v___y_405_ = v___x_411_;
goto v___jp_404_;
}
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__4, &l_Lake_InputDirConfig_instConfigInfo___closed__4_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__4);
v___y_405_ = v___x_412_;
goto v___jp_404_;
}
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_405_);
v___x_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_403_);
lean_ctor_set(v___x_407_, 1, v___y_405_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instEmptyCollection(lean_object* v_name_413_){
_start:
{
uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = 0;
v___x_415_ = l_Lean_Name_toString(v_name_413_, v___x_414_);
v___x_416_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0);
v___x_417_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*2, v___x_414_);
return v___x_417_;
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
