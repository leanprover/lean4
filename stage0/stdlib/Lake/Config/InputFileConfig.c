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
uint8_t l_Lake_InputFileConfig_text___proj___redArg___lam__0(lean_object* v_cfg_46_){
_start:
{
uint8_t v_text_47_; 
v_text_47_ = lean_ctor_get_uint8(v_cfg_46_, sizeof(void*)*1);
return v_text_47_;
}
}
LEAN_EXPORT void l_Lake_InputFileConfig_text___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_46_ = stack[0].m_obj;
uint8_t v_res_48_;
v_res_48_ = l_Lake_InputFileConfig_text___proj___redArg___lam__0(v_cfg_46_);
stack->m_num = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__0___boxed(lean_object* v_cfg_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lake_InputFileConfig_text___proj___redArg___lam__0(v_cfg_49_);
lean_dec_ref(v_cfg_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__1(uint8_t v_val_52_, lean_object* v_cfg_53_){
_start:
{
lean_object* v_path_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_path_54_ = lean_ctor_get(v_cfg_53_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_cfg_53_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v_cfg_53_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_path_54_);
lean_dec(v_cfg_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_path_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v_val_52_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT void l_Lake_InputFileConfig_text___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_52_ = stack[0].m_num;
lean_object* v_cfg_53_ = stack[1].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lake_InputFileConfig_text___proj___redArg___lam__1(v_val_52_, v_cfg_53_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__1___boxed(lean_object* v_val_63_, lean_object* v_cfg_64_){
_start:
{
uint8_t v_val_44__boxed_65_; lean_object* v_res_66_; 
v_val_44__boxed_65_ = lean_unbox(v_val_63_);
v_res_66_ = l_Lake_InputFileConfig_text___proj___redArg___lam__1(v_val_44__boxed_65_, v_cfg_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__2(lean_object* v_f_67_, lean_object* v_cfg_68_){
_start:
{
lean_object* v_path_69_; uint8_t v_text_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_80_; 
v_path_69_ = lean_ctor_get(v_cfg_68_, 0);
v_text_70_ = lean_ctor_get_uint8(v_cfg_68_, sizeof(void*)*1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_cfg_68_);
if (v_isSharedCheck_80_ == 0)
{
v___x_72_ = v_cfg_68_;
v_isShared_73_ = v_isSharedCheck_80_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_path_69_);
lean_dec(v_cfg_68_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_80_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lean_box(v_text_70_);
v___x_75_ = lean_apply_1(v_f_67_, v___x_74_);
if (v_isShared_73_ == 0)
{
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_path_69_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
uint8_t v___x_78_; 
v___x_78_ = lean_unbox(v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_78_);
return v___x_77_;
}
}
}
}
uint8_t l_Lake_InputFileConfig_text___proj___redArg___lam__3(lean_object* v_x_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
LEAN_EXPORT void l_Lake_InputFileConfig_text___proj___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_81_ = stack[0].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Lake_InputFileConfig_text___proj___redArg___lam__3(v_x_81_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___lam__3___boxed(lean_object* v_x_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lake_InputFileConfig_text___proj___redArg___lam__3(v_x_84_);
lean_dec_ref(v_x_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
lean_object* l_Lake_InputFileConfig_text___proj___redArg(){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Lake_InputFileConfig_text___proj___redArg___closed__4));
return v___x_97_;
}
}
LEAN_EXPORT void l_Lake_InputFileConfig_text___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_98_;
v_res_98_ = l_Lake_InputFileConfig_text___proj___redArg();
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lake_InputFileConfig_text___proj___redArg();
return v_res_100_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_text___proj___closed__0(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lake_InputFileConfig_text___proj___redArg();
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj(lean_object* v_name_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lake_InputFileConfig_text___proj___closed__0, &l_Lake_InputFileConfig_text___proj___closed__0_once, _init_l_Lake_InputFileConfig_text___proj___closed__0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___boxed(lean_object* v_name_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lake_InputFileConfig_text___proj(v_name_104_);
lean_dec(v_name_104_);
return v_res_105_;
}
}
lean_object* l_Lake_InputFileConfig_text_instConfigField___redArg(){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lake_InputFileConfig_text___proj___closed__0, &l_Lake_InputFileConfig_text___proj___closed__0_once, _init_l_Lake_InputFileConfig_text___proj___closed__0);
return v___x_107_;
}
}
LEAN_EXPORT void l_Lake_InputFileConfig_text_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_108_;
v_res_108_ = l_Lake_InputFileConfig_text_instConfigField___redArg();
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lake_InputFileConfig_text_instConfigField___redArg();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField(lean_object* v_name_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lake_InputFileConfig_text___proj___closed__0, &l_Lake_InputFileConfig_text___proj___closed__0_once, _init_l_Lake_InputFileConfig_text___proj___closed__0);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___boxed(lean_object* v_name_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lake_InputFileConfig_text_instConfigField(v_name_113_);
lean_dec(v_name_113_);
return v_res_114_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__3));
v___x_125_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__0));
v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__7));
v___x_135_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__4, &l_Lake_InputFileConfig___fields___closed__4_once, _init_l_Lake_InputFileConfig___fields___closed__4);
v___x_136_ = lean_array_push(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
return v___x_137_;
}
}
lean_object* l_Lake_InputFileConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lake_InputFileConfig___fields;
return v___x_139_;
}
}
LEAN_EXPORT void l_Lake_InputFileConfig_instConfigFields___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_140_;
v_res_140_ = l_Lake_InputFileConfig_instConfigFields___redArg();
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lake_InputFileConfig_instConfigFields___redArg();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields(lean_object* v_name_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lake_InputFileConfig___fields;
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___boxed(lean_object* v_name_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lake_InputFileConfig_instConfigFields(v_name_145_);
lean_dec(v_name_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigInfo___lam__0(lean_object* v_x1_147_, lean_object* v_x2_148_){
_start:
{
lean_object* v_name_149_; lean_object* v___x_150_; 
v_name_149_ = lean_ctor_get(v_x2_148_, 0);
lean_inc(v_name_149_);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_149_, v_x2_148_, v_x1_147_);
return v___x_150_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = l_Lake_InputFileConfig___fields;
v___x_152_ = lean_array_get_size(v___x_151_);
return v___x_152_;
}
}
static uint8_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_nat_dec_lt(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static uint8_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_177_ = lean_nat_dec_le(v___x_176_, v___x_176_);
return v___x_177_;
}
}
static size_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_178_; size_t v___x_179_; 
v___x_178_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_179_ = lean_usize_of_nat(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_180_; size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_180_ = lean_box(1);
v___x_181_ = lean_usize_once(&l_Lake_InputFileConfig_instConfigInfo___closed__14, &l_Lake_InputFileConfig_instConfigInfo___closed__14_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__14);
v___x_182_ = ((size_t)0ULL);
v___x_183_ = l_Lake_InputFileConfig___fields;
v___f_184_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_185_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_185_, v___f_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_186_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_187_; lean_object* v___y_189_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_187_ = l_Lake_InputFileConfig___fields;
v___x_192_ = lean_box(1);
v___x_193_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__11, &l_Lake_InputFileConfig_instConfigInfo___closed__11_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__11);
if (v___x_193_ == 0)
{
v___y_189_ = v___x_192_;
goto v___jp_188_;
}
else
{
uint8_t v___x_194_; 
v___x_194_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__13, &l_Lake_InputFileConfig_instConfigInfo___closed__13_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__13);
if (v___x_194_ == 0)
{
if (v___x_193_ == 0)
{
v___y_189_ = v___x_192_;
goto v___jp_188_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__15, &l_Lake_InputFileConfig_instConfigInfo___closed__15_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__15);
v___y_189_ = v___x_195_;
goto v___jp_188_;
}
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__15, &l_Lake_InputFileConfig_instConfigInfo___closed__15_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__15);
v___y_189_ = v___x_196_;
goto v___jp_188_;
}
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_189_);
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_187_);
lean_ctor_set(v___x_191_, 1, v___y_189_);
lean_ctor_set(v___x_191_, 2, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instEmptyCollection(lean_object* v_name_197_){
_start:
{
uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = 0;
v___x_199_ = l_Lean_Name_toString(v_name_197_, v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0(lean_object* v_cfg_201_){
_start:
{
lean_object* v_path_202_; 
v_path_202_ = lean_ctor_get(v_cfg_201_, 0);
lean_inc_ref(v_path_202_);
return v_path_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0___boxed(lean_object* v_cfg_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lake_InputDirConfig_path___proj___lam__0(v_cfg_203_);
lean_dec_ref(v_cfg_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__1(lean_object* v_val_205_, lean_object* v_cfg_206_){
_start:
{
uint8_t v_text_207_; lean_object* v_filter_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_text_207_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*2);
v_filter_208_ = lean_ctor_get(v_cfg_206_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_cfg_206_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_cfg_206_, 0);
lean_dec(v_unused_216_);
v___x_210_ = v_cfg_206_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_filter_208_);
lean_dec(v_cfg_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v_val_205_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_val_205_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_filter_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*2, v_text_207_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__2(lean_object* v_f_217_, lean_object* v_cfg_218_){
_start:
{
lean_object* v_path_219_; uint8_t v_text_220_; lean_object* v_filter_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_path_219_ = lean_ctor_get(v_cfg_218_, 0);
v_text_220_ = lean_ctor_get_uint8(v_cfg_218_, sizeof(void*)*2);
v_filter_221_ = lean_ctor_get(v_cfg_218_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_cfg_218_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_cfg_218_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_filter_221_);
lean_inc(v_path_219_);
lean_dec(v_cfg_218_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_apply_1(v_f_217_, v_path_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_filter_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*2, v_text_220_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3(lean_object* v_name_230_, lean_object* v_x_231_){
_start:
{
uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_232_ = 0;
v___x_233_ = l_Lean_Name_toString(v_name_230_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3___boxed(lean_object* v_name_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lake_InputDirConfig_path___proj___lam__3(v_name_234_, v_x_235_);
lean_dec_ref(v_x_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj(lean_object* v_name_240_){
_start:
{
lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; 
v___f_241_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__0));
v___f_242_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__1));
v___f_243_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__2));
v___f_244_ = lean_alloc_closure((void*)(l_Lake_InputDirConfig_path___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_244_, 0, v_name_240_);
v___x_245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_245_, 0, v___f_241_);
lean_ctor_set(v___x_245_, 1, v___f_242_);
lean_ctor_set(v___x_245_, 2, v___f_243_);
lean_ctor_set(v___x_245_, 3, v___f_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path_instConfigField(lean_object* v_name_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lake_InputDirConfig_path___proj(v_name_246_);
return v___x_247_;
}
}
uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__0(lean_object* v_cfg_248_){
_start:
{
uint8_t v_text_249_; 
v_text_249_ = lean_ctor_get_uint8(v_cfg_248_, sizeof(void*)*2);
return v_text_249_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_text___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_248_ = stack[0].m_obj;
uint8_t v_res_250_;
v_res_250_ = l_Lake_InputDirConfig_text___proj___redArg___lam__0(v_cfg_248_);
stack->m_num = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__0___boxed(lean_object* v_cfg_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Lake_InputDirConfig_text___proj___redArg___lam__0(v_cfg_251_);
lean_dec_ref(v_cfg_251_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1(uint8_t v_val_254_, lean_object* v_cfg_255_){
_start:
{
lean_object* v_path_256_; lean_object* v_filter_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_path_256_ = lean_ctor_get(v_cfg_255_, 0);
v_filter_257_ = lean_ctor_get(v_cfg_255_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_cfg_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v_cfg_255_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_filter_257_);
lean_inc(v_path_256_);
lean_dec(v_cfg_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_path_256_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_filter_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*2, v_val_254_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_text___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_254_ = stack[0].m_num;
lean_object* v_cfg_255_ = stack[1].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lake_InputDirConfig_text___proj___redArg___lam__1(v_val_254_, v_cfg_255_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__1___boxed(lean_object* v_val_266_, lean_object* v_cfg_267_){
_start:
{
uint8_t v_val_47__boxed_268_; lean_object* v_res_269_; 
v_val_47__boxed_268_ = lean_unbox(v_val_266_);
v_res_269_ = l_Lake_InputDirConfig_text___proj___redArg___lam__1(v_val_47__boxed_268_, v_cfg_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__2(lean_object* v_f_270_, lean_object* v_cfg_271_){
_start:
{
lean_object* v_path_272_; uint8_t v_text_273_; lean_object* v_filter_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_284_; 
v_path_272_ = lean_ctor_get(v_cfg_271_, 0);
v_text_273_ = lean_ctor_get_uint8(v_cfg_271_, sizeof(void*)*2);
v_filter_274_ = lean_ctor_get(v_cfg_271_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_cfg_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_276_ = v_cfg_271_;
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_filter_274_);
lean_inc(v_path_272_);
lean_dec(v_cfg_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = lean_box(v_text_273_);
v___x_279_ = lean_apply_1(v_f_270_, v___x_278_);
if (v_isShared_277_ == 0)
{
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_path_272_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_filter_274_);
v___x_281_ = v_reuseFailAlloc_283_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
uint8_t v___x_282_; 
v___x_282_ = lean_unbox(v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*2, v___x_282_);
return v___x_281_;
}
}
}
}
uint8_t l_Lake_InputDirConfig_text___proj___redArg___lam__3(lean_object* v_x_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_text___proj___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_285_ = stack[0].m_obj;
uint8_t v_res_287_;
v_res_287_ = l_Lake_InputDirConfig_text___proj___redArg___lam__3(v_x_285_);
stack->m_num = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___lam__3___boxed(lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lake_InputDirConfig_text___proj___redArg___lam__3(v_x_288_);
lean_dec_ref(v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
lean_object* l_Lake_InputDirConfig_text___proj___redArg(){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lake_InputDirConfig_text___proj___redArg___closed__4));
return v___x_301_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_text___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_302_;
v_res_302_ = l_Lake_InputDirConfig_text___proj___redArg();
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___redArg___boxed(lean_object* v___dummy_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lake_InputDirConfig_text___proj___redArg();
return v_res_304_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_text___proj___closed__0(void){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lake_InputDirConfig_text___proj___redArg();
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj(lean_object* v_name_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___boxed(lean_object* v_name_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lake_InputDirConfig_text___proj(v_name_308_);
lean_dec(v_name_308_);
return v_res_309_;
}
}
lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg(){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_text_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_312_;
v_res_312_ = l_Lake_InputDirConfig_text_instConfigField___redArg();
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___redArg___boxed(lean_object* v___dummy_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lake_InputDirConfig_text_instConfigField___redArg();
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField(lean_object* v_name_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Lake_InputDirConfig_text___proj___closed__0, &l_Lake_InputDirConfig_text___proj___closed__0_once, _init_l_Lake_InputDirConfig_text___proj___closed__0);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___boxed(lean_object* v_name_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lake_InputDirConfig_text_instConfigField(v_name_317_);
lean_dec(v_name_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0(lean_object* v_cfg_319_){
_start:
{
lean_object* v_filter_320_; 
v_filter_320_ = lean_ctor_get(v_cfg_319_, 1);
lean_inc_ref(v_filter_320_);
return v_filter_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__0___boxed(lean_object* v_cfg_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lake_InputDirConfig_filter___proj___redArg___lam__0(v_cfg_321_);
lean_dec_ref(v_cfg_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__1(lean_object* v_val_323_, lean_object* v_cfg_324_){
_start:
{
lean_object* v_path_325_; uint8_t v_text_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_path_325_ = lean_ctor_get(v_cfg_324_, 0);
v_text_326_ = lean_ctor_get_uint8(v_cfg_324_, sizeof(void*)*2);
v_isSharedCheck_333_ = !lean_is_exclusive(v_cfg_324_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_cfg_324_, 1);
lean_dec(v_unused_334_);
v___x_328_ = v_cfg_324_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_path_325_);
lean_dec(v_cfg_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_val_323_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_path_325_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_val_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*2, v_text_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__2(lean_object* v_f_335_, lean_object* v_cfg_336_){
_start:
{
lean_object* v_path_337_; uint8_t v_text_338_; lean_object* v_filter_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_path_337_ = lean_ctor_get(v_cfg_336_, 0);
v_text_338_ = lean_ctor_get_uint8(v_cfg_336_, sizeof(void*)*2);
v_filter_339_ = lean_ctor_get(v_cfg_336_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_cfg_336_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v_cfg_336_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_filter_339_);
lean_inc(v_path_337_);
lean_dec(v_cfg_336_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_apply_1(v_f_335_, v_filter_339_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_path_337_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*2, v_text_338_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lake_Pattern_star___redArg();
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3(lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___lam__3___boxed(lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lake_InputDirConfig_filter___proj___redArg___lam__3(v_x_351_);
lean_dec_ref(v_x_351_);
return v_res_352_;
}
}
lean_object* l_Lake_InputDirConfig_filter___proj___redArg(){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = ((lean_object*)(l_Lake_InputDirConfig_filter___proj___redArg___closed__4));
return v___x_363_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_filter___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_364_;
v_res_364_ = l_Lake_InputDirConfig_filter___proj___redArg();
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___redArg___boxed(lean_object* v___dummy_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lake_InputDirConfig_filter___proj___redArg();
return v_res_366_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___closed__0(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lake_InputDirConfig_filter___proj___redArg();
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj(lean_object* v_name_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___boxed(lean_object* v_name_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_InputDirConfig_filter___proj(v_name_370_);
lean_dec(v_name_370_);
return v_res_371_;
}
}
lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg(){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_filter_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_374_;
v_res_374_ = l_Lake_InputDirConfig_filter_instConfigField___redArg();
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___redArg___boxed(lean_object* v___dummy_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lake_InputDirConfig_filter_instConfigField___redArg();
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField(lean_object* v_name_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___closed__0, &l_Lake_InputDirConfig_filter___proj___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___closed__0);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___boxed(lean_object* v_name_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lake_InputDirConfig_filter_instConfigField(v_name_379_);
lean_dec(v_name_379_);
return v_res_380_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lake_InputDirConfig___fields___closed__2));
v___x_389_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
v___x_390_ = lean_array_push(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lake_InputDirConfig___fields___closed__3, &l_Lake_InputDirConfig___fields___closed__3_once, _init_l_Lake_InputDirConfig___fields___closed__3);
return v___x_391_;
}
}
lean_object* l_Lake_InputDirConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lake_InputDirConfig___fields;
return v___x_393_;
}
}
LEAN_EXPORT void l_Lake_InputDirConfig_instConfigFields___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_394_;
v_res_394_ = l_Lake_InputDirConfig_instConfigFields___redArg();
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lake_InputDirConfig_instConfigFields___redArg();
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields(lean_object* v_name_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lake_InputDirConfig___fields;
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___boxed(lean_object* v_name_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lake_InputDirConfig_instConfigFields(v_name_399_);
lean_dec(v_name_399_);
return v_res_400_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = l_Lake_InputDirConfig___fields;
v___x_402_ = lean_array_get_size(v___x_401_);
return v___x_402_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_nat_dec_lt(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_407_ = lean_nat_dec_le(v___x_406_, v___x_406_);
return v___x_407_;
}
}
static size_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_408_; size_t v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_409_ = lean_usize_of_nat(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_410_ = lean_box(1);
v___x_411_ = lean_usize_once(&l_Lake_InputDirConfig_instConfigInfo___closed__3, &l_Lake_InputDirConfig_instConfigInfo___closed__3_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__3);
v___x_412_ = ((size_t)0ULL);
v___x_413_ = l_Lake_InputDirConfig___fields;
v___f_414_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_415_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_415_, v___f_414_, v___x_413_, v___x_412_, v___x_411_, v___x_410_);
return v___x_416_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_417_; lean_object* v___y_419_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_417_ = l_Lake_InputDirConfig___fields;
v___x_422_ = lean_box(1);
v___x_423_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__1, &l_Lake_InputDirConfig_instConfigInfo___closed__1_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__1);
if (v___x_423_ == 0)
{
v___y_419_ = v___x_422_;
goto v___jp_418_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__2, &l_Lake_InputDirConfig_instConfigInfo___closed__2_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__2);
if (v___x_424_ == 0)
{
if (v___x_423_ == 0)
{
v___y_419_ = v___x_422_;
goto v___jp_418_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__4, &l_Lake_InputDirConfig_instConfigInfo___closed__4_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__4);
v___y_419_ = v___x_425_;
goto v___jp_418_;
}
}
else
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__4, &l_Lake_InputDirConfig_instConfigInfo___closed__4_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__4);
v___y_419_ = v___x_426_;
goto v___jp_418_;
}
}
v___jp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_419_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_417_);
lean_ctor_set(v___x_421_, 1, v___y_419_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instEmptyCollection(lean_object* v_name_427_){
_start:
{
uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = 0;
v___x_429_ = l_Lean_Name_toString(v_name_427_, v___x_428_);
v___x_430_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___redArg___lam__3___closed__0);
v___x_431_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*2, v___x_428_);
return v___x_431_;
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
