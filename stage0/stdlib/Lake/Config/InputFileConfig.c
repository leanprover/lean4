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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_Pattern_star(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_InputFileConfig_text___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___closed__0 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___closed__0_value;
static const lean_closure_object l_Lake_InputFileConfig_text___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___closed__1 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___closed__1_value;
static const lean_closure_object l_Lake_InputFileConfig_text___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___closed__2 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___closed__2_value;
static const lean_closure_object l_Lake_InputFileConfig_text___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputFileConfig_text___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFileConfig_text___proj___closed__3 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___closed__3_value;
static const lean_ctor_object l_Lake_InputFileConfig_text___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputFileConfig_text___proj___closed__0_value),((lean_object*)&l_Lake_InputFileConfig_text___proj___closed__1_value),((lean_object*)&l_Lake_InputFileConfig_text___proj___closed__2_value),((lean_object*)&l_Lake_InputFileConfig_text___proj___closed__3_value)}};
static const lean_object* l_Lake_InputFileConfig_text___proj___closed__4 = (const lean_object*)&l_Lake_InputFileConfig_text___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_InputDirConfig_text___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___closed__0 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___closed__0_value;
static const lean_closure_object l_Lake_InputDirConfig_text___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___closed__1 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___closed__1_value;
static const lean_closure_object l_Lake_InputDirConfig_text___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___closed__2 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___closed__2_value;
static const lean_closure_object l_Lake_InputDirConfig_text___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_text___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_text___proj___closed__3 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___closed__3_value;
static const lean_ctor_object l_Lake_InputDirConfig_text___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputDirConfig_text___proj___closed__0_value),((lean_object*)&l_Lake_InputDirConfig_text___proj___closed__1_value),((lean_object*)&l_Lake_InputDirConfig_text___proj___closed__2_value),((lean_object*)&l_Lake_InputDirConfig_text___proj___closed__3_value)}};
static const lean_object* l_Lake_InputDirConfig_text___proj___closed__4 = (const lean_object*)&l_Lake_InputDirConfig_text___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDirConfig_filter___proj___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___closed__0 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__0_value;
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___closed__1 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__1_value;
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___closed__2 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__2_value;
static const lean_closure_object l_Lake_InputDirConfig_filter___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputDirConfig_filter___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDirConfig_filter___proj___closed__3 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__3_value;
static const lean_ctor_object l_Lake_InputDirConfig_filter___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__0_value),((lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__1_value),((lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__2_value),((lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__3_value)}};
static const lean_object* l_Lake_InputDirConfig_filter___proj___closed__4 = (const lean_object*)&l_Lake_InputDirConfig_filter___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___lam__0(lean_object* v_cfg_46_){
_start:
{
uint8_t v_text_47_; 
v_text_47_ = lean_ctor_get_uint8(v_cfg_46_, sizeof(void*)*1);
return v_text_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__0___boxed(lean_object* v_cfg_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lake_InputFileConfig_text___proj___lam__0(v_cfg_48_);
lean_dec_ref(v_cfg_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__1(uint8_t v_val_51_, lean_object* v_cfg_52_){
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
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__1___boxed(lean_object* v_val_61_, lean_object* v_cfg_62_){
_start:
{
uint8_t v_val_41__boxed_63_; lean_object* v_res_64_; 
v_val_41__boxed_63_ = lean_unbox(v_val_61_);
v_res_64_ = l_Lake_InputFileConfig_text___proj___lam__1(v_val_41__boxed_63_, v_cfg_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__2(lean_object* v_f_65_, lean_object* v_cfg_66_){
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
LEAN_EXPORT uint8_t l_Lake_InputFileConfig_text___proj___lam__3(lean_object* v_x_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___lam__3___boxed(lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lake_InputFileConfig_text___proj___lam__3(v_x_81_);
lean_dec_ref(v_x_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj(lean_object* v_name_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_Lake_InputFileConfig_text___proj___closed__4));
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text___proj___boxed(lean_object* v_name_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_InputFileConfig_text___proj(v_name_95_);
lean_dec(v_name_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField(lean_object* v_name_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lake_InputFileConfig_text___proj(v_name_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_text_instConfigField___boxed(lean_object* v_name_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lake_InputFileConfig_text_instConfigField(v_name_99_);
lean_dec(v_name_99_);
return v_res_100_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__3));
v___x_111_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__0));
v___x_112_ = lean_array_push(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((lean_object*)(l_Lake_InputFileConfig___fields___closed__7));
v___x_121_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__4, &l_Lake_InputFileConfig___fields___closed__4_once, _init_l_Lake_InputFileConfig___fields___closed__4);
v___x_122_ = lean_array_push(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lake_InputFileConfig___fields(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields(lean_object* v_name_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lake_InputFileConfig___fields;
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigFields___boxed(lean_object* v_name_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_InputFileConfig_instConfigFields(v_name_126_);
lean_dec(v_name_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instConfigInfo___lam__0(lean_object* v_x1_128_, lean_object* v_x2_129_){
_start:
{
lean_object* v_name_130_; lean_object* v___x_131_; 
v_name_130_ = lean_ctor_get(v_x2_129_, 0);
lean_inc(v_name_130_);
v___x_131_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_130_, v_x2_129_, v_x1_128_);
return v___x_131_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = l_Lake_InputFileConfig___fields;
v___x_133_ = lean_array_get_size(v___x_132_);
return v___x_133_;
}
}
static uint8_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_nat_dec_lt(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static uint8_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_158_ = lean_nat_dec_le(v___x_157_, v___x_157_);
return v___x_158_;
}
}
static size_t _init_l_Lake_InputFileConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_159_; size_t v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__0, &l_Lake_InputFileConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__0);
v___x_160_ = lean_usize_of_nat(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_161_ = lean_box(1);
v___x_162_ = lean_usize_once(&l_Lake_InputFileConfig_instConfigInfo___closed__14, &l_Lake_InputFileConfig_instConfigInfo___closed__14_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__14);
v___x_163_ = ((size_t)0ULL);
v___x_164_ = l_Lake_InputFileConfig___fields;
v___f_165_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_166_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_166_, v___f_165_, v___x_164_, v___x_163_, v___x_162_, v___x_161_);
return v___x_167_;
}
}
static lean_object* _init_l_Lake_InputFileConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_168_; lean_object* v___y_170_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_168_ = l_Lake_InputFileConfig___fields;
v___x_173_ = lean_box(1);
v___x_174_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__11, &l_Lake_InputFileConfig_instConfigInfo___closed__11_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__11);
if (v___x_174_ == 0)
{
v___y_170_ = v___x_173_;
goto v___jp_169_;
}
else
{
uint8_t v___x_175_; 
v___x_175_ = lean_uint8_once(&l_Lake_InputFileConfig_instConfigInfo___closed__13, &l_Lake_InputFileConfig_instConfigInfo___closed__13_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__13);
if (v___x_175_ == 0)
{
if (v___x_174_ == 0)
{
v___y_170_ = v___x_173_;
goto v___jp_169_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__15, &l_Lake_InputFileConfig_instConfigInfo___closed__15_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__15);
v___y_170_ = v___x_176_;
goto v___jp_169_;
}
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lake_InputFileConfig_instConfigInfo___closed__15, &l_Lake_InputFileConfig_instConfigInfo___closed__15_once, _init_l_Lake_InputFileConfig_instConfigInfo___closed__15);
v___y_170_ = v___x_177_;
goto v___jp_169_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_170_);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_168_);
lean_ctor_set(v___x_172_, 1, v___y_170_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileConfig_instEmptyCollection(lean_object* v_name_178_){
_start:
{
uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = 0;
v___x_180_ = l_Lean_Name_toString(v_name_178_, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0(lean_object* v_cfg_182_){
_start:
{
lean_object* v_path_183_; 
v_path_183_ = lean_ctor_get(v_cfg_182_, 0);
lean_inc_ref(v_path_183_);
return v_path_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__0___boxed(lean_object* v_cfg_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lake_InputDirConfig_path___proj___lam__0(v_cfg_184_);
lean_dec_ref(v_cfg_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__1(lean_object* v_val_186_, lean_object* v_cfg_187_){
_start:
{
uint8_t v_text_188_; lean_object* v_filter_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_text_188_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*2);
v_filter_189_ = lean_ctor_get(v_cfg_187_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_cfg_187_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v_cfg_187_, 0);
lean_dec(v_unused_197_);
v___x_191_ = v_cfg_187_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_filter_189_);
lean_dec(v_cfg_187_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v_val_186_);
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_val_186_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_filter_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*2, v_text_188_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__2(lean_object* v_f_198_, lean_object* v_cfg_199_){
_start:
{
lean_object* v_path_200_; uint8_t v_text_201_; lean_object* v_filter_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_path_200_ = lean_ctor_get(v_cfg_199_, 0);
v_text_201_ = lean_ctor_get_uint8(v_cfg_199_, sizeof(void*)*2);
v_filter_202_ = lean_ctor_get(v_cfg_199_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_cfg_199_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v_cfg_199_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_filter_202_);
lean_inc(v_path_200_);
lean_dec(v_cfg_199_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_apply_1(v_f_198_, v_path_200_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_filter_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_209_, sizeof(void*)*2, v_text_201_);
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
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3(lean_object* v_name_211_, lean_object* v_x_212_){
_start:
{
uint8_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = 0;
v___x_214_ = l_Lean_Name_toString(v_name_211_, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj___lam__3___boxed(lean_object* v_name_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_InputDirConfig_path___proj___lam__3(v_name_215_, v_x_216_);
lean_dec_ref(v_x_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path___proj(lean_object* v_name_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; 
v___f_222_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__0));
v___f_223_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__1));
v___f_224_ = ((lean_object*)(l_Lake_InputDirConfig_path___proj___closed__2));
v___f_225_ = lean_alloc_closure((void*)(l_Lake_InputDirConfig_path___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_225_, 0, v_name_221_);
v___x_226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_226_, 0, v___f_222_);
lean_ctor_set(v___x_226_, 1, v___f_223_);
lean_ctor_set(v___x_226_, 2, v___f_224_);
lean_ctor_set(v___x_226_, 3, v___f_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_path_instConfigField(lean_object* v_name_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lake_InputDirConfig_path___proj(v_name_227_);
return v___x_228_;
}
}
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___lam__0(lean_object* v_cfg_229_){
_start:
{
uint8_t v_text_230_; 
v_text_230_ = lean_ctor_get_uint8(v_cfg_229_, sizeof(void*)*2);
return v_text_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__0___boxed(lean_object* v_cfg_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lake_InputDirConfig_text___proj___lam__0(v_cfg_231_);
lean_dec_ref(v_cfg_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__1(uint8_t v_val_234_, lean_object* v_cfg_235_){
_start:
{
lean_object* v_path_236_; lean_object* v_filter_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_path_236_ = lean_ctor_get(v_cfg_235_, 0);
v_filter_237_ = lean_ctor_get(v_cfg_235_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_cfg_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v_cfg_235_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_filter_237_);
lean_inc(v_path_236_);
lean_dec(v_cfg_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_path_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_filter_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*2, v_val_234_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__1___boxed(lean_object* v_val_245_, lean_object* v_cfg_246_){
_start:
{
uint8_t v_val_44__boxed_247_; lean_object* v_res_248_; 
v_val_44__boxed_247_ = lean_unbox(v_val_245_);
v_res_248_ = l_Lake_InputDirConfig_text___proj___lam__1(v_val_44__boxed_247_, v_cfg_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__2(lean_object* v_f_249_, lean_object* v_cfg_250_){
_start:
{
lean_object* v_path_251_; uint8_t v_text_252_; lean_object* v_filter_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_263_; 
v_path_251_ = lean_ctor_get(v_cfg_250_, 0);
v_text_252_ = lean_ctor_get_uint8(v_cfg_250_, sizeof(void*)*2);
v_filter_253_ = lean_ctor_get(v_cfg_250_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v_cfg_250_);
if (v_isSharedCheck_263_ == 0)
{
v___x_255_ = v_cfg_250_;
v_isShared_256_ = v_isSharedCheck_263_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_filter_253_);
lean_inc(v_path_251_);
lean_dec(v_cfg_250_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_263_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = lean_box(v_text_252_);
v___x_258_ = lean_apply_1(v_f_249_, v___x_257_);
if (v_isShared_256_ == 0)
{
v___x_260_ = v___x_255_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_path_251_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_filter_253_);
v___x_260_ = v_reuseFailAlloc_262_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
uint8_t v___x_261_; 
v___x_261_ = lean_unbox(v___x_258_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*2, v___x_261_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_InputDirConfig_text___proj___lam__3(lean_object* v_x_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___lam__3___boxed(lean_object* v_x_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Lake_InputDirConfig_text___proj___lam__3(v_x_266_);
lean_dec_ref(v_x_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj(lean_object* v_name_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = ((lean_object*)(l_Lake_InputDirConfig_text___proj___closed__4));
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text___proj___boxed(lean_object* v_name_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lake_InputDirConfig_text___proj(v_name_280_);
lean_dec(v_name_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField(lean_object* v_name_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lake_InputDirConfig_text___proj(v_name_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_text_instConfigField___boxed(lean_object* v_name_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lake_InputDirConfig_text_instConfigField(v_name_284_);
lean_dec(v_name_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__0(lean_object* v_cfg_286_){
_start:
{
lean_object* v_filter_287_; 
v_filter_287_ = lean_ctor_get(v_cfg_286_, 1);
lean_inc_ref(v_filter_287_);
return v_filter_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__0___boxed(lean_object* v_cfg_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_InputDirConfig_filter___proj___lam__0(v_cfg_288_);
lean_dec_ref(v_cfg_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__1(lean_object* v_val_290_, lean_object* v_cfg_291_){
_start:
{
lean_object* v_path_292_; uint8_t v_text_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_path_292_ = lean_ctor_get(v_cfg_291_, 0);
v_text_293_ = lean_ctor_get_uint8(v_cfg_291_, sizeof(void*)*2);
v_isSharedCheck_300_ = !lean_is_exclusive(v_cfg_291_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v_cfg_291_, 1);
lean_dec(v_unused_301_);
v___x_295_ = v_cfg_291_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_path_292_);
lean_dec(v_cfg_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_val_290_);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_path_292_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_val_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_299_, sizeof(void*)*2, v_text_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__2(lean_object* v_f_302_, lean_object* v_cfg_303_){
_start:
{
lean_object* v_path_304_; uint8_t v_text_305_; lean_object* v_filter_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_path_304_ = lean_ctor_get(v_cfg_303_, 0);
v_text_305_ = lean_ctor_get_uint8(v_cfg_303_, sizeof(void*)*2);
v_filter_306_ = lean_ctor_get(v_cfg_303_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_cfg_303_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v_cfg_303_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_filter_306_);
lean_inc(v_path_304_);
lean_dec(v_cfg_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_apply_1(v_f_302_, v_filter_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_path_304_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*2, v_text_305_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
static lean_object* _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lake_Pattern_star(lean_box(0), lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__3(lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___lam__3___boxed(lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lake_InputDirConfig_filter___proj___lam__3(v_x_318_);
lean_dec_ref(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj(lean_object* v_name_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = ((lean_object*)(l_Lake_InputDirConfig_filter___proj___closed__4));
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter___proj___boxed(lean_object* v_name_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lake_InputDirConfig_filter___proj(v_name_331_);
lean_dec(v_name_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField(lean_object* v_name_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lake_InputDirConfig_filter___proj(v_name_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_filter_instConfigField___boxed(lean_object* v_name_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lake_InputDirConfig_filter_instConfigField(v_name_335_);
lean_dec(v_name_335_);
return v_res_336_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = ((lean_object*)(l_Lake_InputDirConfig___fields___closed__2));
v___x_345_ = lean_obj_once(&l_Lake_InputFileConfig___fields___closed__8, &l_Lake_InputFileConfig___fields___closed__8_once, _init_l_Lake_InputFileConfig___fields___closed__8);
v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lake_InputDirConfig___fields(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lake_InputDirConfig___fields___closed__3, &l_Lake_InputDirConfig___fields___closed__3_once, _init_l_Lake_InputDirConfig___fields___closed__3);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields(lean_object* v_name_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lake_InputDirConfig___fields;
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instConfigFields___boxed(lean_object* v_name_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lake_InputDirConfig_instConfigFields(v_name_350_);
lean_dec(v_name_350_);
return v_res_351_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = l_Lake_InputDirConfig___fields;
v___x_353_ = lean_array_get_size(v___x_352_);
return v___x_353_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_nat_dec_lt(v___x_355_, v___x_354_);
return v___x_356_;
}
}
static uint8_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_358_ = lean_nat_dec_le(v___x_357_, v___x_357_);
return v___x_358_;
}
}
static size_t _init_l_Lake_InputDirConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_359_; size_t v___x_360_; 
v___x_359_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__0, &l_Lake_InputDirConfig_instConfigInfo___closed__0_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__0);
v___x_360_ = lean_usize_of_nat(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_361_ = lean_box(1);
v___x_362_ = lean_usize_once(&l_Lake_InputDirConfig_instConfigInfo___closed__3, &l_Lake_InputDirConfig_instConfigInfo___closed__3_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__3);
v___x_363_ = ((size_t)0ULL);
v___x_364_ = l_Lake_InputDirConfig___fields;
v___f_365_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__12));
v___x_366_ = ((lean_object*)(l_Lake_InputFileConfig_instConfigInfo___closed__10));
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_366_, v___f_365_, v___x_364_, v___x_363_, v___x_362_, v___x_361_);
return v___x_367_;
}
}
static lean_object* _init_l_Lake_InputDirConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_368_; lean_object* v___y_370_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_368_ = l_Lake_InputDirConfig___fields;
v___x_373_ = lean_box(1);
v___x_374_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__1, &l_Lake_InputDirConfig_instConfigInfo___closed__1_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__1);
if (v___x_374_ == 0)
{
v___y_370_ = v___x_373_;
goto v___jp_369_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_uint8_once(&l_Lake_InputDirConfig_instConfigInfo___closed__2, &l_Lake_InputDirConfig_instConfigInfo___closed__2_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__2);
if (v___x_375_ == 0)
{
if (v___x_374_ == 0)
{
v___y_370_ = v___x_373_;
goto v___jp_369_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__4, &l_Lake_InputDirConfig_instConfigInfo___closed__4_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__4);
v___y_370_ = v___x_376_;
goto v___jp_369_;
}
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lake_InputDirConfig_instConfigInfo___closed__4, &l_Lake_InputDirConfig_instConfigInfo___closed__4_once, _init_l_Lake_InputDirConfig_instConfigInfo___closed__4);
v___y_370_ = v___x_377_;
goto v___jp_369_;
}
}
v___jp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_370_);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_368_);
lean_ctor_set(v___x_372_, 1, v___y_370_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirConfig_instEmptyCollection(lean_object* v_name_378_){
_start:
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = 0;
v___x_380_ = l_Lean_Name_toString(v_name_378_, v___x_379_);
v___x_381_ = lean_obj_once(&l_Lake_InputDirConfig_filter___proj___lam__3___closed__0, &l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once, _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0);
v___x_382_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*2, v___x_379_);
return v___x_382_;
}
}
lean_object* runtime_initialize_Lake_Config_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_InputFileConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
