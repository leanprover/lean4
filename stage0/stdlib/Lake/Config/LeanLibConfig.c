// Lean compiler output
// Module: Lake.Config.LeanLibConfig
// Imports: public import Lean.Compiler.NameMangling public import Lake.Util.Casing public import Lake.Build.Facets public import Lake.Config.LeanConfig public import Lake.Config.Glob meta import all Lake.Config.Meta import Lake.Config.Meta
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_oFacet;
extern lean_object* l_Lake_Module_oExportFacet;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_LeanConfig___fields;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lake_Glob_matches(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instInhabitedLeanLibConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__0_value;
static const lean_array_object l_Lake_instInhabitedLeanLibConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value;
static const lean_ctor_object l_Lake_instInhabitedLeanLibConfig_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__2_value;
static const lean_string_object l_Lake_instInhabitedLeanLibConfig_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__3_value;
static const lean_string_object l_Lake_instInhabitedLeanLibConfig_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__4 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__4_value;
static lean_once_cell_t l_Lake_instInhabitedLeanLibConfig_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__5;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_srcDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_roots___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_roots___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_roots___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_roots___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_roots___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_roots___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_roots___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_roots___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_roots___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_roots___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_roots___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_roots___proj___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__3(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_globs___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_globs___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_libName___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_libName___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanLibConfig_needs___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_needs___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_needs___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_precompileModules___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileModules___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileModules___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileModules___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig_precompileModules___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_defaultFacets___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_nativeFacets___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_allowImportAll___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_allowImportAll___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_allowImportAll___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig_allowImportAll___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(lean_object*);
static const lean_array_object l_Lake_LeanLibConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__0_value;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 241, 97, 48, 55, 77, 36, 145)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__3_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__4;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "roots"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__5 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 73, 39, 112, 55, 103, 176)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__6 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__6_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__6_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__6_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__7 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__7_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__8;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "globs"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__9 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__9_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__9_value),LEAN_SCALAR_PTR_LITERAL(2, 64, 222, 202, 250, 190, 94, 19)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__10 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__10_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__10_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__10_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__11 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__11_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__12;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "libName"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__13 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__13_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__13_value),LEAN_SCALAR_PTR_LITERAL(19, 171, 234, 84, 17, 149, 3, 152)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__14 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__14_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__14_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__15 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__15_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__16;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libPrefixOnWindows"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__17 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__17_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__17_value),LEAN_SCALAR_PTR_LITERAL(26, 75, 58, 45, 181, 132, 175, 34)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__18 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__18_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__18_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__18_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__19 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__19_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__20;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "needs"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__21 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__21_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__21_value),LEAN_SCALAR_PTR_LITERAL(215, 219, 176, 39, 126, 76, 70, 199)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__22 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__22_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__22_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__22_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__23 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__23_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__24;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "extraDepTargets"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__25 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__25_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__25_value),LEAN_SCALAR_PTR_LITERAL(232, 29, 68, 154, 160, 50, 56, 5)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__26 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__26_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__26_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__26_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__27 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__27_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__28;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileModules"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__29 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__29_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__29_value),LEAN_SCALAR_PTR_LITERAL(210, 72, 98, 56, 225, 29, 247, 45)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__30 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__30_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__30_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__30_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__31 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__31_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__32;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "defaultFacets"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__33 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__33_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__33_value),LEAN_SCALAR_PTR_LITERAL(74, 73, 74, 204, 169, 19, 96, 134)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__34 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__34_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__34_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__34_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__35 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__35_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__36;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeFacets"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__37 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__37_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__37_value),LEAN_SCALAR_PTR_LITERAL(130, 15, 19, 239, 40, 85, 158, 29)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__38 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__38_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__38_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__38_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__39 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__39_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__40;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__41 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__41_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__41_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__42 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__42_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__42_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__42_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__43 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__43_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__44;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__45;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__46 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__46_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__46_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__47 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__47_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__47_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__47_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__48 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__48_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__49;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig___fields;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__0;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__3_value;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__4_value;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__5_value;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__6_value;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_LeanLibConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_LeanLibConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_LeanLibConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__10_value;
static lean_once_cell_t l_Lake_LeanLibConfig_instConfigInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_LeanLibConfig_instConfigInfo___closed__11;
static const lean_closure_object l_Lake_LeanLibConfig_instConfigInfo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__12 = (const lean_object*)&l_Lake_LeanLibConfig_instConfigInfo___closed__12_value;
static lean_once_cell_t l_Lake_LeanLibConfig_instConfigInfo___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_LeanLibConfig_instConfigInfo___closed__13;
static lean_once_cell_t l_Lake_LeanLibConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_LeanLibConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_LeanLibConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_instConfigInfo___closed__15;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__0(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_instEmptyCollection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_instEmptyCollection___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instEmptyCollection___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_instEmptyCollection___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0(uint8_t v_shouldExport_1_){
_start:
{
lean_object* v___y_3_; 
if (v_shouldExport_1_ == 0)
{
lean_object* v___x_7_; 
v___x_7_ = l_Lake_Module_oFacet;
v___y_3_ = v___x_7_;
goto v___jp_2_;
}
else
{
lean_object* v___x_8_; 
v___x_8_ = l_Lake_Module_oExportFacet;
v___y_3_ = v___x_8_;
goto v___jp_2_;
}
v___jp_2_:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_mk_empty_array_with_capacity(v___x_4_);
lean_inc(v___y_3_);
v___x_6_ = lean_array_push(v___x_5_, v___y_3_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(lean_object* v_shouldExport_9_){
_start:
{
uint8_t v_shouldExport_boxed_10_; lean_object* v_res_11_; 
v_shouldExport_boxed_10_ = lean_unbox(v_shouldExport_9_);
v_res_11_ = l_Lake_instInhabitedLeanLibConfig_default___lam__0(v_shouldExport_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(size_t v_sz_12_, size_t v_i_13_, lean_object* v_bs_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lean_usize_dec_lt(v_i_13_, v_sz_12_);
if (v___x_15_ == 0)
{
return v_bs_14_;
}
else
{
lean_object* v_v_16_; lean_object* v___x_17_; lean_object* v_bs_x27_18_; lean_object* v___x_19_; size_t v___x_20_; size_t v___x_21_; lean_object* v___x_22_; 
v_v_16_ = lean_array_uget(v_bs_14_, v_i_13_);
v___x_17_ = lean_unsigned_to_nat(0u);
v_bs_x27_18_ = lean_array_uset(v_bs_14_, v_i_13_, v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v_v_16_);
v___x_20_ = ((size_t)1ULL);
v___x_21_ = lean_usize_add(v_i_13_, v___x_20_);
v___x_22_ = lean_array_uset(v_bs_x27_18_, v_i_13_, v___x_19_);
v_i_13_ = v___x_21_;
v_bs_14_ = v___x_22_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0___boxed(lean_object* v_sz_24_, lean_object* v_i_25_, lean_object* v_bs_26_){
_start:
{
size_t v_sz_boxed_27_; size_t v_i_boxed_28_; lean_object* v_res_29_; 
v_sz_boxed_27_ = lean_unbox_usize(v_sz_24_);
lean_dec(v_sz_24_);
v_i_boxed_28_ = lean_unbox_usize(v_i_25_);
lean_dec(v_i_25_);
v_res_29_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_boxed_27_, v_i_boxed_28_, v_bs_26_);
return v_res_29_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanLibConfig_default___closed__5(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = l_Lake_LeanLib_leanArtsFacet;
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_mk_empty_array_with_capacity(v___x_41_);
v___x_43_ = lean_array_push(v___x_42_, v___x_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default(lean_object* v_name_44_){
_start:
{
lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; size_t v_sz_52_; size_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___f_45_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_46_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_47_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_48_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_49_);
v___x_51_ = lean_array_push(v___x_50_, v_name_44_);
v_sz_52_ = lean_array_size(v___x_51_);
v___x_53_ = ((size_t)0ULL);
lean_inc_ref(v___x_51_);
v___x_54_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_52_, v___x_53_, v___x_51_);
v___x_55_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__4));
v___x_56_ = 0;
v___x_57_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__5, &l_Lake_instInhabitedLeanLibConfig_default___closed__5_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__5);
v___x_58_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_58_, 0, v___x_47_);
lean_ctor_set(v___x_58_, 1, v___x_48_);
lean_ctor_set(v___x_58_, 2, v___x_51_);
lean_ctor_set(v___x_58_, 3, v___x_54_);
lean_ctor_set(v___x_58_, 4, v___x_55_);
lean_ctor_set(v___x_58_, 5, v___x_46_);
lean_ctor_set(v___x_58_, 6, v___x_46_);
lean_ctor_set(v___x_58_, 7, v___x_57_);
lean_ctor_set(v___x_58_, 8, v___f_45_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*9, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*9 + 1, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*9 + 2, v___x_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig(lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lake_instInhabitedLeanLibConfig_default(v_a_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0(lean_object* v_cfg_61_){
_start:
{
lean_object* v_srcDir_62_; 
v_srcDir_62_ = lean_ctor_get(v_cfg_61_, 1);
lean_inc_ref(v_srcDir_62_);
return v_srcDir_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lake_LeanLibConfig_srcDir___proj___lam__0(v_cfg_63_);
lean_dec_ref(v_cfg_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__1(lean_object* v_val_65_, lean_object* v_cfg_66_){
_start:
{
lean_object* v_toLeanConfig_67_; lean_object* v_roots_68_; lean_object* v_globs_69_; lean_object* v_libName_70_; uint8_t v_libPrefixOnWindows_71_; lean_object* v_needs_72_; lean_object* v_extraDepTargets_73_; uint8_t v_precompileModules_74_; lean_object* v_defaultFacets_75_; lean_object* v_nativeFacets_76_; uint8_t v_allowImportAll_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_toLeanConfig_67_ = lean_ctor_get(v_cfg_66_, 0);
v_roots_68_ = lean_ctor_get(v_cfg_66_, 2);
v_globs_69_ = lean_ctor_get(v_cfg_66_, 3);
v_libName_70_ = lean_ctor_get(v_cfg_66_, 4);
v_libPrefixOnWindows_71_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*9);
v_needs_72_ = lean_ctor_get(v_cfg_66_, 5);
v_extraDepTargets_73_ = lean_ctor_get(v_cfg_66_, 6);
v_precompileModules_74_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*9 + 1);
v_defaultFacets_75_ = lean_ctor_get(v_cfg_66_, 7);
v_nativeFacets_76_ = lean_ctor_get(v_cfg_66_, 8);
v_allowImportAll_77_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*9 + 2);
v_isSharedCheck_84_ = !lean_is_exclusive(v_cfg_66_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v_cfg_66_, 1);
lean_dec(v_unused_85_);
v___x_79_ = v_cfg_66_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_nativeFacets_76_);
lean_inc(v_defaultFacets_75_);
lean_inc(v_extraDepTargets_73_);
lean_inc(v_needs_72_);
lean_inc(v_libName_70_);
lean_inc(v_globs_69_);
lean_inc(v_roots_68_);
lean_inc(v_toLeanConfig_67_);
lean_dec(v_cfg_66_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v_val_65_);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_toLeanConfig_67_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_val_65_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_roots_68_);
lean_ctor_set(v_reuseFailAlloc_83_, 3, v_globs_69_);
lean_ctor_set(v_reuseFailAlloc_83_, 4, v_libName_70_);
lean_ctor_set(v_reuseFailAlloc_83_, 5, v_needs_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 6, v_extraDepTargets_73_);
lean_ctor_set(v_reuseFailAlloc_83_, 7, v_defaultFacets_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 8, v_nativeFacets_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_83_, sizeof(void*)*9, v_libPrefixOnWindows_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_83_, sizeof(void*)*9 + 1, v_precompileModules_74_);
lean_ctor_set_uint8(v_reuseFailAlloc_83_, sizeof(void*)*9 + 2, v_allowImportAll_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__2(lean_object* v_f_86_, lean_object* v_cfg_87_){
_start:
{
lean_object* v_toLeanConfig_88_; lean_object* v_srcDir_89_; lean_object* v_roots_90_; lean_object* v_globs_91_; lean_object* v_libName_92_; uint8_t v_libPrefixOnWindows_93_; lean_object* v_needs_94_; lean_object* v_extraDepTargets_95_; uint8_t v_precompileModules_96_; lean_object* v_defaultFacets_97_; lean_object* v_nativeFacets_98_; uint8_t v_allowImportAll_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_toLeanConfig_88_ = lean_ctor_get(v_cfg_87_, 0);
v_srcDir_89_ = lean_ctor_get(v_cfg_87_, 1);
v_roots_90_ = lean_ctor_get(v_cfg_87_, 2);
v_globs_91_ = lean_ctor_get(v_cfg_87_, 3);
v_libName_92_ = lean_ctor_get(v_cfg_87_, 4);
v_libPrefixOnWindows_93_ = lean_ctor_get_uint8(v_cfg_87_, sizeof(void*)*9);
v_needs_94_ = lean_ctor_get(v_cfg_87_, 5);
v_extraDepTargets_95_ = lean_ctor_get(v_cfg_87_, 6);
v_precompileModules_96_ = lean_ctor_get_uint8(v_cfg_87_, sizeof(void*)*9 + 1);
v_defaultFacets_97_ = lean_ctor_get(v_cfg_87_, 7);
v_nativeFacets_98_ = lean_ctor_get(v_cfg_87_, 8);
v_allowImportAll_99_ = lean_ctor_get_uint8(v_cfg_87_, sizeof(void*)*9 + 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_cfg_87_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v_cfg_87_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_nativeFacets_98_);
lean_inc(v_defaultFacets_97_);
lean_inc(v_extraDepTargets_95_);
lean_inc(v_needs_94_);
lean_inc(v_libName_92_);
lean_inc(v_globs_91_);
lean_inc(v_roots_90_);
lean_inc(v_srcDir_89_);
lean_inc(v_toLeanConfig_88_);
lean_dec(v_cfg_87_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_apply_1(v_f_86_, v_srcDir_89_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_toLeanConfig_88_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_roots_90_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_globs_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_libName_92_);
lean_ctor_set(v_reuseFailAlloc_106_, 5, v_needs_94_);
lean_ctor_set(v_reuseFailAlloc_106_, 6, v_extraDepTargets_95_);
lean_ctor_set(v_reuseFailAlloc_106_, 7, v_defaultFacets_97_);
lean_ctor_set(v_reuseFailAlloc_106_, 8, v_nativeFacets_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*9, v_libPrefixOnWindows_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*9 + 1, v_precompileModules_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*9 + 2, v_allowImportAll_99_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3(lean_object* v_x_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lake_LeanLibConfig_srcDir___proj___lam__3(v_x_110_);
lean_dec_ref(v_x_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object* v_name_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___closed__4));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object* v_name_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_123_);
lean_dec(v_name_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object* v_name_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object* v_name_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_127_);
lean_dec(v_name_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object* v_cfg_129_){
_start:
{
lean_object* v_roots_130_; 
v_roots_130_ = lean_ctor_get(v_cfg_129_, 2);
lean_inc_ref(v_roots_130_);
return v_roots_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object* v_cfg_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_131_);
lean_dec_ref(v_cfg_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object* v_val_133_, lean_object* v_cfg_134_){
_start:
{
lean_object* v_toLeanConfig_135_; lean_object* v_srcDir_136_; lean_object* v_globs_137_; lean_object* v_libName_138_; uint8_t v_libPrefixOnWindows_139_; lean_object* v_needs_140_; lean_object* v_extraDepTargets_141_; uint8_t v_precompileModules_142_; lean_object* v_defaultFacets_143_; lean_object* v_nativeFacets_144_; uint8_t v_allowImportAll_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_toLeanConfig_135_ = lean_ctor_get(v_cfg_134_, 0);
v_srcDir_136_ = lean_ctor_get(v_cfg_134_, 1);
v_globs_137_ = lean_ctor_get(v_cfg_134_, 3);
v_libName_138_ = lean_ctor_get(v_cfg_134_, 4);
v_libPrefixOnWindows_139_ = lean_ctor_get_uint8(v_cfg_134_, sizeof(void*)*9);
v_needs_140_ = lean_ctor_get(v_cfg_134_, 5);
v_extraDepTargets_141_ = lean_ctor_get(v_cfg_134_, 6);
v_precompileModules_142_ = lean_ctor_get_uint8(v_cfg_134_, sizeof(void*)*9 + 1);
v_defaultFacets_143_ = lean_ctor_get(v_cfg_134_, 7);
v_nativeFacets_144_ = lean_ctor_get(v_cfg_134_, 8);
v_allowImportAll_145_ = lean_ctor_get_uint8(v_cfg_134_, sizeof(void*)*9 + 2);
v_isSharedCheck_152_ = !lean_is_exclusive(v_cfg_134_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v_cfg_134_, 2);
lean_dec(v_unused_153_);
v___x_147_ = v_cfg_134_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_nativeFacets_144_);
lean_inc(v_defaultFacets_143_);
lean_inc(v_extraDepTargets_141_);
lean_inc(v_needs_140_);
lean_inc(v_libName_138_);
lean_inc(v_globs_137_);
lean_inc(v_srcDir_136_);
lean_inc(v_toLeanConfig_135_);
lean_dec(v_cfg_134_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 2, v_val_133_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_toLeanConfig_135_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_srcDir_136_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_val_133_);
lean_ctor_set(v_reuseFailAlloc_151_, 3, v_globs_137_);
lean_ctor_set(v_reuseFailAlloc_151_, 4, v_libName_138_);
lean_ctor_set(v_reuseFailAlloc_151_, 5, v_needs_140_);
lean_ctor_set(v_reuseFailAlloc_151_, 6, v_extraDepTargets_141_);
lean_ctor_set(v_reuseFailAlloc_151_, 7, v_defaultFacets_143_);
lean_ctor_set(v_reuseFailAlloc_151_, 8, v_nativeFacets_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_151_, sizeof(void*)*9, v_libPrefixOnWindows_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_151_, sizeof(void*)*9 + 1, v_precompileModules_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_151_, sizeof(void*)*9 + 2, v_allowImportAll_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object* v_f_154_, lean_object* v_cfg_155_){
_start:
{
lean_object* v_toLeanConfig_156_; lean_object* v_srcDir_157_; lean_object* v_roots_158_; lean_object* v_globs_159_; lean_object* v_libName_160_; uint8_t v_libPrefixOnWindows_161_; lean_object* v_needs_162_; lean_object* v_extraDepTargets_163_; uint8_t v_precompileModules_164_; lean_object* v_defaultFacets_165_; lean_object* v_nativeFacets_166_; uint8_t v_allowImportAll_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_toLeanConfig_156_ = lean_ctor_get(v_cfg_155_, 0);
v_srcDir_157_ = lean_ctor_get(v_cfg_155_, 1);
v_roots_158_ = lean_ctor_get(v_cfg_155_, 2);
v_globs_159_ = lean_ctor_get(v_cfg_155_, 3);
v_libName_160_ = lean_ctor_get(v_cfg_155_, 4);
v_libPrefixOnWindows_161_ = lean_ctor_get_uint8(v_cfg_155_, sizeof(void*)*9);
v_needs_162_ = lean_ctor_get(v_cfg_155_, 5);
v_extraDepTargets_163_ = lean_ctor_get(v_cfg_155_, 6);
v_precompileModules_164_ = lean_ctor_get_uint8(v_cfg_155_, sizeof(void*)*9 + 1);
v_defaultFacets_165_ = lean_ctor_get(v_cfg_155_, 7);
v_nativeFacets_166_ = lean_ctor_get(v_cfg_155_, 8);
v_allowImportAll_167_ = lean_ctor_get_uint8(v_cfg_155_, sizeof(void*)*9 + 2);
v_isSharedCheck_175_ = !lean_is_exclusive(v_cfg_155_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_cfg_155_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_nativeFacets_166_);
lean_inc(v_defaultFacets_165_);
lean_inc(v_extraDepTargets_163_);
lean_inc(v_needs_162_);
lean_inc(v_libName_160_);
lean_inc(v_globs_159_);
lean_inc(v_roots_158_);
lean_inc(v_srcDir_157_);
lean_inc(v_toLeanConfig_156_);
lean_dec(v_cfg_155_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_apply_1(v_f_154_, v_roots_158_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 2, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_toLeanConfig_156_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_srcDir_157_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v_globs_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v_libName_160_);
lean_ctor_set(v_reuseFailAlloc_174_, 5, v_needs_162_);
lean_ctor_set(v_reuseFailAlloc_174_, 6, v_extraDepTargets_163_);
lean_ctor_set(v_reuseFailAlloc_174_, 7, v_defaultFacets_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 8, v_nativeFacets_166_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*9, v_libPrefixOnWindows_161_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*9 + 1, v_precompileModules_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*9 + 2, v_allowImportAll_167_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object* v_name_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_mk_empty_array_with_capacity(v___x_178_);
v___x_180_ = lean_array_push(v___x_179_, v_name_176_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object* v_name_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_181_, v_x_182_);
lean_dec_ref(v_x_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object* v_name_187_){
_start:
{
lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_192_; 
v___f_188_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__0));
v___f_189_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__1));
v___f_190_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__2));
v___f_191_ = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_roots___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_191_, 0, v_name_187_);
v___x_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_192_, 0, v___f_188_);
lean_ctor_set(v___x_192_, 1, v___f_189_);
lean_ctor_set(v___x_192_, 2, v___f_190_);
lean_ctor_set(v___x_192_, 3, v___f_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object* v_name_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lake_LeanLibConfig_roots___proj(v_name_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0(lean_object* v_cfg_195_){
_start:
{
lean_object* v_globs_196_; 
v_globs_196_ = lean_ctor_get(v_cfg_195_, 3);
lean_inc_ref(v_globs_196_);
return v_globs_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0___boxed(lean_object* v_cfg_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lake_LeanLibConfig_globs___proj___lam__0(v_cfg_197_);
lean_dec_ref(v_cfg_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__1(lean_object* v_val_199_, lean_object* v_cfg_200_){
_start:
{
lean_object* v_toLeanConfig_201_; lean_object* v_srcDir_202_; lean_object* v_roots_203_; lean_object* v_libName_204_; uint8_t v_libPrefixOnWindows_205_; lean_object* v_needs_206_; lean_object* v_extraDepTargets_207_; uint8_t v_precompileModules_208_; lean_object* v_defaultFacets_209_; lean_object* v_nativeFacets_210_; uint8_t v_allowImportAll_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_toLeanConfig_201_ = lean_ctor_get(v_cfg_200_, 0);
v_srcDir_202_ = lean_ctor_get(v_cfg_200_, 1);
v_roots_203_ = lean_ctor_get(v_cfg_200_, 2);
v_libName_204_ = lean_ctor_get(v_cfg_200_, 4);
v_libPrefixOnWindows_205_ = lean_ctor_get_uint8(v_cfg_200_, sizeof(void*)*9);
v_needs_206_ = lean_ctor_get(v_cfg_200_, 5);
v_extraDepTargets_207_ = lean_ctor_get(v_cfg_200_, 6);
v_precompileModules_208_ = lean_ctor_get_uint8(v_cfg_200_, sizeof(void*)*9 + 1);
v_defaultFacets_209_ = lean_ctor_get(v_cfg_200_, 7);
v_nativeFacets_210_ = lean_ctor_get(v_cfg_200_, 8);
v_allowImportAll_211_ = lean_ctor_get_uint8(v_cfg_200_, sizeof(void*)*9 + 2);
v_isSharedCheck_218_ = !lean_is_exclusive(v_cfg_200_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_cfg_200_, 3);
lean_dec(v_unused_219_);
v___x_213_ = v_cfg_200_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_nativeFacets_210_);
lean_inc(v_defaultFacets_209_);
lean_inc(v_extraDepTargets_207_);
lean_inc(v_needs_206_);
lean_inc(v_libName_204_);
lean_inc(v_roots_203_);
lean_inc(v_srcDir_202_);
lean_inc(v_toLeanConfig_201_);
lean_dec(v_cfg_200_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v_val_199_);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_toLeanConfig_201_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_srcDir_202_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_roots_203_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_val_199_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_libName_204_);
lean_ctor_set(v_reuseFailAlloc_217_, 5, v_needs_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 6, v_extraDepTargets_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 7, v_defaultFacets_209_);
lean_ctor_set(v_reuseFailAlloc_217_, 8, v_nativeFacets_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9, v_libPrefixOnWindows_205_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9 + 1, v_precompileModules_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9 + 2, v_allowImportAll_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__2(lean_object* v_f_220_, lean_object* v_cfg_221_){
_start:
{
lean_object* v_toLeanConfig_222_; lean_object* v_srcDir_223_; lean_object* v_roots_224_; lean_object* v_globs_225_; lean_object* v_libName_226_; uint8_t v_libPrefixOnWindows_227_; lean_object* v_needs_228_; lean_object* v_extraDepTargets_229_; uint8_t v_precompileModules_230_; lean_object* v_defaultFacets_231_; lean_object* v_nativeFacets_232_; uint8_t v_allowImportAll_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_toLeanConfig_222_ = lean_ctor_get(v_cfg_221_, 0);
v_srcDir_223_ = lean_ctor_get(v_cfg_221_, 1);
v_roots_224_ = lean_ctor_get(v_cfg_221_, 2);
v_globs_225_ = lean_ctor_get(v_cfg_221_, 3);
v_libName_226_ = lean_ctor_get(v_cfg_221_, 4);
v_libPrefixOnWindows_227_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9);
v_needs_228_ = lean_ctor_get(v_cfg_221_, 5);
v_extraDepTargets_229_ = lean_ctor_get(v_cfg_221_, 6);
v_precompileModules_230_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9 + 1);
v_defaultFacets_231_ = lean_ctor_get(v_cfg_221_, 7);
v_nativeFacets_232_ = lean_ctor_get(v_cfg_221_, 8);
v_allowImportAll_233_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9 + 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_cfg_221_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v_cfg_221_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_nativeFacets_232_);
lean_inc(v_defaultFacets_231_);
lean_inc(v_extraDepTargets_229_);
lean_inc(v_needs_228_);
lean_inc(v_libName_226_);
lean_inc(v_globs_225_);
lean_inc(v_roots_224_);
lean_inc(v_srcDir_223_);
lean_inc(v_toLeanConfig_222_);
lean_dec(v_cfg_221_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_apply_1(v_f_220_, v_globs_225_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 3, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_toLeanConfig_222_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_srcDir_223_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_roots_224_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_libName_226_);
lean_ctor_set(v_reuseFailAlloc_240_, 5, v_needs_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 6, v_extraDepTargets_229_);
lean_ctor_set(v_reuseFailAlloc_240_, 7, v_defaultFacets_231_);
lean_ctor_set(v_reuseFailAlloc_240_, 8, v_nativeFacets_232_);
lean_ctor_set_uint8(v_reuseFailAlloc_240_, sizeof(void*)*9, v_libPrefixOnWindows_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_240_, sizeof(void*)*9 + 1, v_precompileModules_230_);
lean_ctor_set_uint8(v_reuseFailAlloc_240_, sizeof(void*)*9 + 2, v_allowImportAll_233_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__3(lean_object* v_x_242_){
_start:
{
lean_object* v_roots_243_; size_t v_sz_244_; size_t v___x_245_; lean_object* v___x_246_; 
v_roots_243_ = lean_ctor_get(v_x_242_, 2);
lean_inc_ref(v_roots_243_);
lean_dec_ref(v_x_242_);
v_sz_244_ = lean_array_size(v_roots_243_);
v___x_245_ = ((size_t)0ULL);
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_244_, v___x_245_, v_roots_243_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object* v_name_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = ((lean_object*)(l_Lake_LeanLibConfig_globs___proj___closed__4));
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object* v_name_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_LeanLibConfig_globs___proj(v_name_258_);
lean_dec(v_name_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object* v_name_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lake_LeanLibConfig_globs___proj(v_name_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object* v_name_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_262_);
lean_dec(v_name_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0(lean_object* v_cfg_264_){
_start:
{
lean_object* v_libName_265_; 
v_libName_265_ = lean_ctor_get(v_cfg_264_, 4);
lean_inc_ref(v_libName_265_);
return v_libName_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0___boxed(lean_object* v_cfg_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lake_LeanLibConfig_libName___proj___lam__0(v_cfg_266_);
lean_dec_ref(v_cfg_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__1(lean_object* v_val_268_, lean_object* v_cfg_269_){
_start:
{
lean_object* v_toLeanConfig_270_; lean_object* v_srcDir_271_; lean_object* v_roots_272_; lean_object* v_globs_273_; uint8_t v_libPrefixOnWindows_274_; lean_object* v_needs_275_; lean_object* v_extraDepTargets_276_; uint8_t v_precompileModules_277_; lean_object* v_defaultFacets_278_; lean_object* v_nativeFacets_279_; uint8_t v_allowImportAll_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_toLeanConfig_270_ = lean_ctor_get(v_cfg_269_, 0);
v_srcDir_271_ = lean_ctor_get(v_cfg_269_, 1);
v_roots_272_ = lean_ctor_get(v_cfg_269_, 2);
v_globs_273_ = lean_ctor_get(v_cfg_269_, 3);
v_libPrefixOnWindows_274_ = lean_ctor_get_uint8(v_cfg_269_, sizeof(void*)*9);
v_needs_275_ = lean_ctor_get(v_cfg_269_, 5);
v_extraDepTargets_276_ = lean_ctor_get(v_cfg_269_, 6);
v_precompileModules_277_ = lean_ctor_get_uint8(v_cfg_269_, sizeof(void*)*9 + 1);
v_defaultFacets_278_ = lean_ctor_get(v_cfg_269_, 7);
v_nativeFacets_279_ = lean_ctor_get(v_cfg_269_, 8);
v_allowImportAll_280_ = lean_ctor_get_uint8(v_cfg_269_, sizeof(void*)*9 + 2);
v_isSharedCheck_287_ = !lean_is_exclusive(v_cfg_269_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_cfg_269_, 4);
lean_dec(v_unused_288_);
v___x_282_ = v_cfg_269_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_nativeFacets_279_);
lean_inc(v_defaultFacets_278_);
lean_inc(v_extraDepTargets_276_);
lean_inc(v_needs_275_);
lean_inc(v_globs_273_);
lean_inc(v_roots_272_);
lean_inc(v_srcDir_271_);
lean_inc(v_toLeanConfig_270_);
lean_dec(v_cfg_269_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_val_268_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_toLeanConfig_270_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_srcDir_271_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_roots_272_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_globs_273_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_val_268_);
lean_ctor_set(v_reuseFailAlloc_286_, 5, v_needs_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 6, v_extraDepTargets_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 7, v_defaultFacets_278_);
lean_ctor_set(v_reuseFailAlloc_286_, 8, v_nativeFacets_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*9, v_libPrefixOnWindows_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*9 + 1, v_precompileModules_277_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*9 + 2, v_allowImportAll_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__2(lean_object* v_f_289_, lean_object* v_cfg_290_){
_start:
{
lean_object* v_toLeanConfig_291_; lean_object* v_srcDir_292_; lean_object* v_roots_293_; lean_object* v_globs_294_; lean_object* v_libName_295_; uint8_t v_libPrefixOnWindows_296_; lean_object* v_needs_297_; lean_object* v_extraDepTargets_298_; uint8_t v_precompileModules_299_; lean_object* v_defaultFacets_300_; lean_object* v_nativeFacets_301_; uint8_t v_allowImportAll_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_310_; 
v_toLeanConfig_291_ = lean_ctor_get(v_cfg_290_, 0);
v_srcDir_292_ = lean_ctor_get(v_cfg_290_, 1);
v_roots_293_ = lean_ctor_get(v_cfg_290_, 2);
v_globs_294_ = lean_ctor_get(v_cfg_290_, 3);
v_libName_295_ = lean_ctor_get(v_cfg_290_, 4);
v_libPrefixOnWindows_296_ = lean_ctor_get_uint8(v_cfg_290_, sizeof(void*)*9);
v_needs_297_ = lean_ctor_get(v_cfg_290_, 5);
v_extraDepTargets_298_ = lean_ctor_get(v_cfg_290_, 6);
v_precompileModules_299_ = lean_ctor_get_uint8(v_cfg_290_, sizeof(void*)*9 + 1);
v_defaultFacets_300_ = lean_ctor_get(v_cfg_290_, 7);
v_nativeFacets_301_ = lean_ctor_get(v_cfg_290_, 8);
v_allowImportAll_302_ = lean_ctor_get_uint8(v_cfg_290_, sizeof(void*)*9 + 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v_cfg_290_);
if (v_isSharedCheck_310_ == 0)
{
v___x_304_ = v_cfg_290_;
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_nativeFacets_301_);
lean_inc(v_defaultFacets_300_);
lean_inc(v_extraDepTargets_298_);
lean_inc(v_needs_297_);
lean_inc(v_libName_295_);
lean_inc(v_globs_294_);
lean_inc(v_roots_293_);
lean_inc(v_srcDir_292_);
lean_inc(v_toLeanConfig_291_);
lean_dec(v_cfg_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_apply_1(v_f_289_, v_libName_295_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_toLeanConfig_291_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_srcDir_292_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_roots_293_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_globs_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_309_, 5, v_needs_297_);
lean_ctor_set(v_reuseFailAlloc_309_, 6, v_extraDepTargets_298_);
lean_ctor_set(v_reuseFailAlloc_309_, 7, v_defaultFacets_300_);
lean_ctor_set(v_reuseFailAlloc_309_, 8, v_nativeFacets_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_309_, sizeof(void*)*9, v_libPrefixOnWindows_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_309_, sizeof(void*)*9 + 1, v_precompileModules_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_309_, sizeof(void*)*9 + 2, v_allowImportAll_302_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3(lean_object* v_x_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__4));
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3___boxed(lean_object* v_x_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lake_LeanLibConfig_libName___proj___lam__3(v_x_313_);
lean_dec_ref(v_x_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object* v_name_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_Lake_LeanLibConfig_libName___proj___closed__4));
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object* v_name_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lake_LeanLibConfig_libName___proj(v_name_326_);
lean_dec(v_name_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object* v_name_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lake_LeanLibConfig_libName___proj(v_name_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object* v_name_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_330_);
lean_dec(v_name_330_);
return v_res_331_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_332_){
_start:
{
uint8_t v_libPrefixOnWindows_333_; 
v_libPrefixOnWindows_333_ = lean_ctor_get_uint8(v_cfg_332_, sizeof(void*)*9);
return v_libPrefixOnWindows_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(v_cfg_334_);
lean_dec_ref(v_cfg_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_337_, lean_object* v_cfg_338_){
_start:
{
lean_object* v_toLeanConfig_339_; lean_object* v_srcDir_340_; lean_object* v_roots_341_; lean_object* v_globs_342_; lean_object* v_libName_343_; lean_object* v_needs_344_; lean_object* v_extraDepTargets_345_; uint8_t v_precompileModules_346_; lean_object* v_defaultFacets_347_; lean_object* v_nativeFacets_348_; uint8_t v_allowImportAll_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_toLeanConfig_339_ = lean_ctor_get(v_cfg_338_, 0);
v_srcDir_340_ = lean_ctor_get(v_cfg_338_, 1);
v_roots_341_ = lean_ctor_get(v_cfg_338_, 2);
v_globs_342_ = lean_ctor_get(v_cfg_338_, 3);
v_libName_343_ = lean_ctor_get(v_cfg_338_, 4);
v_needs_344_ = lean_ctor_get(v_cfg_338_, 5);
v_extraDepTargets_345_ = lean_ctor_get(v_cfg_338_, 6);
v_precompileModules_346_ = lean_ctor_get_uint8(v_cfg_338_, sizeof(void*)*9 + 1);
v_defaultFacets_347_ = lean_ctor_get(v_cfg_338_, 7);
v_nativeFacets_348_ = lean_ctor_get(v_cfg_338_, 8);
v_allowImportAll_349_ = lean_ctor_get_uint8(v_cfg_338_, sizeof(void*)*9 + 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_cfg_338_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v_cfg_338_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_nativeFacets_348_);
lean_inc(v_defaultFacets_347_);
lean_inc(v_extraDepTargets_345_);
lean_inc(v_needs_344_);
lean_inc(v_libName_343_);
lean_inc(v_globs_342_);
lean_inc(v_roots_341_);
lean_inc(v_srcDir_340_);
lean_inc(v_toLeanConfig_339_);
lean_dec(v_cfg_338_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_toLeanConfig_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_srcDir_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_roots_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_globs_342_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_libName_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_needs_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_extraDepTargets_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_defaultFacets_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v_nativeFacets_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*9 + 1, v_precompileModules_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*9 + 2, v_allowImportAll_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*9, v_val_337_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_357_, lean_object* v_cfg_358_){
_start:
{
uint8_t v_val_71__boxed_359_; lean_object* v_res_360_; 
v_val_71__boxed_359_ = lean_unbox(v_val_357_);
v_res_360_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(v_val_71__boxed_359_, v_cfg_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_361_, lean_object* v_cfg_362_){
_start:
{
lean_object* v_toLeanConfig_363_; lean_object* v_srcDir_364_; lean_object* v_roots_365_; lean_object* v_globs_366_; lean_object* v_libName_367_; uint8_t v_libPrefixOnWindows_368_; lean_object* v_needs_369_; lean_object* v_extraDepTargets_370_; uint8_t v_precompileModules_371_; lean_object* v_defaultFacets_372_; lean_object* v_nativeFacets_373_; uint8_t v_allowImportAll_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_384_; 
v_toLeanConfig_363_ = lean_ctor_get(v_cfg_362_, 0);
v_srcDir_364_ = lean_ctor_get(v_cfg_362_, 1);
v_roots_365_ = lean_ctor_get(v_cfg_362_, 2);
v_globs_366_ = lean_ctor_get(v_cfg_362_, 3);
v_libName_367_ = lean_ctor_get(v_cfg_362_, 4);
v_libPrefixOnWindows_368_ = lean_ctor_get_uint8(v_cfg_362_, sizeof(void*)*9);
v_needs_369_ = lean_ctor_get(v_cfg_362_, 5);
v_extraDepTargets_370_ = lean_ctor_get(v_cfg_362_, 6);
v_precompileModules_371_ = lean_ctor_get_uint8(v_cfg_362_, sizeof(void*)*9 + 1);
v_defaultFacets_372_ = lean_ctor_get(v_cfg_362_, 7);
v_nativeFacets_373_ = lean_ctor_get(v_cfg_362_, 8);
v_allowImportAll_374_ = lean_ctor_get_uint8(v_cfg_362_, sizeof(void*)*9 + 2);
v_isSharedCheck_384_ = !lean_is_exclusive(v_cfg_362_);
if (v_isSharedCheck_384_ == 0)
{
v___x_376_ = v_cfg_362_;
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_nativeFacets_373_);
lean_inc(v_defaultFacets_372_);
lean_inc(v_extraDepTargets_370_);
lean_inc(v_needs_369_);
lean_inc(v_libName_367_);
lean_inc(v_globs_366_);
lean_inc(v_roots_365_);
lean_inc(v_srcDir_364_);
lean_inc(v_toLeanConfig_363_);
lean_dec(v_cfg_362_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = lean_box(v_libPrefixOnWindows_368_);
v___x_379_ = lean_apply_1(v_f_361_, v___x_378_);
if (v_isShared_377_ == 0)
{
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_toLeanConfig_363_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_srcDir_364_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_roots_365_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_globs_366_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_libName_367_);
lean_ctor_set(v_reuseFailAlloc_383_, 5, v_needs_369_);
lean_ctor_set(v_reuseFailAlloc_383_, 6, v_extraDepTargets_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 7, v_defaultFacets_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 8, v_nativeFacets_373_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_unbox(v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*9, v___x_382_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*9 + 1, v_precompileModules_371_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*9 + 2, v_allowImportAll_374_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(lean_object* v_x_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(v_x_387_);
lean_dec_ref(v_x_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object* v_name_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4));
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object* v_name_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_401_);
lean_dec(v_name_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object* v_name_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_name_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_405_);
lean_dec(v_name_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0(lean_object* v_cfg_407_){
_start:
{
lean_object* v_needs_408_; 
v_needs_408_ = lean_ctor_get(v_cfg_407_, 5);
lean_inc_ref(v_needs_408_);
return v_needs_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0___boxed(lean_object* v_cfg_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_LeanLibConfig_needs___proj___lam__0(v_cfg_409_);
lean_dec_ref(v_cfg_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__1(lean_object* v_val_411_, lean_object* v_cfg_412_){
_start:
{
lean_object* v_toLeanConfig_413_; lean_object* v_srcDir_414_; lean_object* v_roots_415_; lean_object* v_globs_416_; lean_object* v_libName_417_; uint8_t v_libPrefixOnWindows_418_; lean_object* v_extraDepTargets_419_; uint8_t v_precompileModules_420_; lean_object* v_defaultFacets_421_; lean_object* v_nativeFacets_422_; uint8_t v_allowImportAll_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_toLeanConfig_413_ = lean_ctor_get(v_cfg_412_, 0);
v_srcDir_414_ = lean_ctor_get(v_cfg_412_, 1);
v_roots_415_ = lean_ctor_get(v_cfg_412_, 2);
v_globs_416_ = lean_ctor_get(v_cfg_412_, 3);
v_libName_417_ = lean_ctor_get(v_cfg_412_, 4);
v_libPrefixOnWindows_418_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*9);
v_extraDepTargets_419_ = lean_ctor_get(v_cfg_412_, 6);
v_precompileModules_420_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*9 + 1);
v_defaultFacets_421_ = lean_ctor_get(v_cfg_412_, 7);
v_nativeFacets_422_ = lean_ctor_get(v_cfg_412_, 8);
v_allowImportAll_423_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*9 + 2);
v_isSharedCheck_430_ = !lean_is_exclusive(v_cfg_412_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_cfg_412_, 5);
lean_dec(v_unused_431_);
v___x_425_ = v_cfg_412_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_nativeFacets_422_);
lean_inc(v_defaultFacets_421_);
lean_inc(v_extraDepTargets_419_);
lean_inc(v_libName_417_);
lean_inc(v_globs_416_);
lean_inc(v_roots_415_);
lean_inc(v_srcDir_414_);
lean_inc(v_toLeanConfig_413_);
lean_dec(v_cfg_412_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 5, v_val_411_);
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_toLeanConfig_413_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_srcDir_414_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_roots_415_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_globs_416_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_libName_417_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v_val_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v_extraDepTargets_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v_defaultFacets_421_);
lean_ctor_set(v_reuseFailAlloc_429_, 8, v_nativeFacets_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*9, v_libPrefixOnWindows_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*9 + 1, v_precompileModules_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*9 + 2, v_allowImportAll_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__2(lean_object* v_f_432_, lean_object* v_cfg_433_){
_start:
{
lean_object* v_toLeanConfig_434_; lean_object* v_srcDir_435_; lean_object* v_roots_436_; lean_object* v_globs_437_; lean_object* v_libName_438_; uint8_t v_libPrefixOnWindows_439_; lean_object* v_needs_440_; lean_object* v_extraDepTargets_441_; uint8_t v_precompileModules_442_; lean_object* v_defaultFacets_443_; lean_object* v_nativeFacets_444_; uint8_t v_allowImportAll_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_toLeanConfig_434_ = lean_ctor_get(v_cfg_433_, 0);
v_srcDir_435_ = lean_ctor_get(v_cfg_433_, 1);
v_roots_436_ = lean_ctor_get(v_cfg_433_, 2);
v_globs_437_ = lean_ctor_get(v_cfg_433_, 3);
v_libName_438_ = lean_ctor_get(v_cfg_433_, 4);
v_libPrefixOnWindows_439_ = lean_ctor_get_uint8(v_cfg_433_, sizeof(void*)*9);
v_needs_440_ = lean_ctor_get(v_cfg_433_, 5);
v_extraDepTargets_441_ = lean_ctor_get(v_cfg_433_, 6);
v_precompileModules_442_ = lean_ctor_get_uint8(v_cfg_433_, sizeof(void*)*9 + 1);
v_defaultFacets_443_ = lean_ctor_get(v_cfg_433_, 7);
v_nativeFacets_444_ = lean_ctor_get(v_cfg_433_, 8);
v_allowImportAll_445_ = lean_ctor_get_uint8(v_cfg_433_, sizeof(void*)*9 + 2);
v_isSharedCheck_453_ = !lean_is_exclusive(v_cfg_433_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v_cfg_433_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_nativeFacets_444_);
lean_inc(v_defaultFacets_443_);
lean_inc(v_extraDepTargets_441_);
lean_inc(v_needs_440_);
lean_inc(v_libName_438_);
lean_inc(v_globs_437_);
lean_inc(v_roots_436_);
lean_inc(v_srcDir_435_);
lean_inc(v_toLeanConfig_434_);
lean_dec(v_cfg_433_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_apply_1(v_f_432_, v_needs_440_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 5, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_toLeanConfig_434_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_srcDir_435_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_roots_436_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_globs_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_libName_438_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_extraDepTargets_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_defaultFacets_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_nativeFacets_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*9, v_libPrefixOnWindows_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*9 + 1, v_precompileModules_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*9 + 2, v_allowImportAll_445_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3(lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___lam__3___closed__0));
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3___boxed(lean_object* v_x_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lake_LeanLibConfig_needs___proj___lam__3(v_x_458_);
lean_dec_ref(v_x_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object* v_name_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___closed__4));
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object* v_name_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lake_LeanLibConfig_needs___proj(v_name_471_);
lean_dec(v_name_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object* v_name_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lake_LeanLibConfig_needs___proj(v_name_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object* v_name_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_475_);
lean_dec(v_name_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_477_){
_start:
{
lean_object* v_extraDepTargets_478_; 
v_extraDepTargets_478_ = lean_ctor_get(v_cfg_477_, 6);
lean_inc_ref(v_extraDepTargets_478_);
return v_extraDepTargets_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(v_cfg_479_);
lean_dec_ref(v_cfg_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1(lean_object* v_val_481_, lean_object* v_cfg_482_){
_start:
{
lean_object* v_toLeanConfig_483_; lean_object* v_srcDir_484_; lean_object* v_roots_485_; lean_object* v_globs_486_; lean_object* v_libName_487_; uint8_t v_libPrefixOnWindows_488_; lean_object* v_needs_489_; uint8_t v_precompileModules_490_; lean_object* v_defaultFacets_491_; lean_object* v_nativeFacets_492_; uint8_t v_allowImportAll_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_toLeanConfig_483_ = lean_ctor_get(v_cfg_482_, 0);
v_srcDir_484_ = lean_ctor_get(v_cfg_482_, 1);
v_roots_485_ = lean_ctor_get(v_cfg_482_, 2);
v_globs_486_ = lean_ctor_get(v_cfg_482_, 3);
v_libName_487_ = lean_ctor_get(v_cfg_482_, 4);
v_libPrefixOnWindows_488_ = lean_ctor_get_uint8(v_cfg_482_, sizeof(void*)*9);
v_needs_489_ = lean_ctor_get(v_cfg_482_, 5);
v_precompileModules_490_ = lean_ctor_get_uint8(v_cfg_482_, sizeof(void*)*9 + 1);
v_defaultFacets_491_ = lean_ctor_get(v_cfg_482_, 7);
v_nativeFacets_492_ = lean_ctor_get(v_cfg_482_, 8);
v_allowImportAll_493_ = lean_ctor_get_uint8(v_cfg_482_, sizeof(void*)*9 + 2);
v_isSharedCheck_500_ = !lean_is_exclusive(v_cfg_482_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v_cfg_482_, 6);
lean_dec(v_unused_501_);
v___x_495_ = v_cfg_482_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_nativeFacets_492_);
lean_inc(v_defaultFacets_491_);
lean_inc(v_needs_489_);
lean_inc(v_libName_487_);
lean_inc(v_globs_486_);
lean_inc(v_roots_485_);
lean_inc(v_srcDir_484_);
lean_inc(v_toLeanConfig_483_);
lean_dec(v_cfg_482_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 6, v_val_481_);
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_toLeanConfig_483_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_srcDir_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_roots_485_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_globs_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_libName_487_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_needs_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v_val_481_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v_defaultFacets_491_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_nativeFacets_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*9, v_libPrefixOnWindows_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*9 + 1, v_precompileModules_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*9 + 2, v_allowImportAll_493_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2(lean_object* v_f_502_, lean_object* v_cfg_503_){
_start:
{
lean_object* v_toLeanConfig_504_; lean_object* v_srcDir_505_; lean_object* v_roots_506_; lean_object* v_globs_507_; lean_object* v_libName_508_; uint8_t v_libPrefixOnWindows_509_; lean_object* v_needs_510_; lean_object* v_extraDepTargets_511_; uint8_t v_precompileModules_512_; lean_object* v_defaultFacets_513_; lean_object* v_nativeFacets_514_; uint8_t v_allowImportAll_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_toLeanConfig_504_ = lean_ctor_get(v_cfg_503_, 0);
v_srcDir_505_ = lean_ctor_get(v_cfg_503_, 1);
v_roots_506_ = lean_ctor_get(v_cfg_503_, 2);
v_globs_507_ = lean_ctor_get(v_cfg_503_, 3);
v_libName_508_ = lean_ctor_get(v_cfg_503_, 4);
v_libPrefixOnWindows_509_ = lean_ctor_get_uint8(v_cfg_503_, sizeof(void*)*9);
v_needs_510_ = lean_ctor_get(v_cfg_503_, 5);
v_extraDepTargets_511_ = lean_ctor_get(v_cfg_503_, 6);
v_precompileModules_512_ = lean_ctor_get_uint8(v_cfg_503_, sizeof(void*)*9 + 1);
v_defaultFacets_513_ = lean_ctor_get(v_cfg_503_, 7);
v_nativeFacets_514_ = lean_ctor_get(v_cfg_503_, 8);
v_allowImportAll_515_ = lean_ctor_get_uint8(v_cfg_503_, sizeof(void*)*9 + 2);
v_isSharedCheck_523_ = !lean_is_exclusive(v_cfg_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v_cfg_503_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_nativeFacets_514_);
lean_inc(v_defaultFacets_513_);
lean_inc(v_extraDepTargets_511_);
lean_inc(v_needs_510_);
lean_inc(v_libName_508_);
lean_inc(v_globs_507_);
lean_inc(v_roots_506_);
lean_inc(v_srcDir_505_);
lean_inc(v_toLeanConfig_504_);
lean_dec(v_cfg_503_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_apply_1(v_f_502_, v_extraDepTargets_511_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 6, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_toLeanConfig_504_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_srcDir_505_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_roots_506_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_globs_507_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_libName_508_);
lean_ctor_set(v_reuseFailAlloc_522_, 5, v_needs_510_);
lean_ctor_set(v_reuseFailAlloc_522_, 6, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_522_, 7, v_defaultFacets_513_);
lean_ctor_set(v_reuseFailAlloc_522_, 8, v_nativeFacets_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_522_, sizeof(void*)*9, v_libPrefixOnWindows_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_522_, sizeof(void*)*9 + 1, v_precompileModules_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_522_, sizeof(void*)*9 + 2, v_allowImportAll_515_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(v_x_528_);
lean_dec_ref(v_x_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object* v_name_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4));
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object* v_name_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_541_);
lean_dec(v_name_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object* v_name_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object* v_name_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_545_);
lean_dec(v_name_545_);
return v_res_546_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___lam__0(lean_object* v_cfg_547_){
_start:
{
uint8_t v_precompileModules_548_; 
v_precompileModules_548_ = lean_ctor_get_uint8(v_cfg_547_, sizeof(void*)*9 + 1);
return v_precompileModules_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__0(v_cfg_549_);
lean_dec_ref(v_cfg_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1(uint8_t v_val_552_, lean_object* v_cfg_553_){
_start:
{
lean_object* v_toLeanConfig_554_; lean_object* v_srcDir_555_; lean_object* v_roots_556_; lean_object* v_globs_557_; lean_object* v_libName_558_; uint8_t v_libPrefixOnWindows_559_; lean_object* v_needs_560_; lean_object* v_extraDepTargets_561_; lean_object* v_defaultFacets_562_; lean_object* v_nativeFacets_563_; uint8_t v_allowImportAll_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_toLeanConfig_554_ = lean_ctor_get(v_cfg_553_, 0);
v_srcDir_555_ = lean_ctor_get(v_cfg_553_, 1);
v_roots_556_ = lean_ctor_get(v_cfg_553_, 2);
v_globs_557_ = lean_ctor_get(v_cfg_553_, 3);
v_libName_558_ = lean_ctor_get(v_cfg_553_, 4);
v_libPrefixOnWindows_559_ = lean_ctor_get_uint8(v_cfg_553_, sizeof(void*)*9);
v_needs_560_ = lean_ctor_get(v_cfg_553_, 5);
v_extraDepTargets_561_ = lean_ctor_get(v_cfg_553_, 6);
v_defaultFacets_562_ = lean_ctor_get(v_cfg_553_, 7);
v_nativeFacets_563_ = lean_ctor_get(v_cfg_553_, 8);
v_allowImportAll_564_ = lean_ctor_get_uint8(v_cfg_553_, sizeof(void*)*9 + 2);
v_isSharedCheck_571_ = !lean_is_exclusive(v_cfg_553_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v_cfg_553_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_nativeFacets_563_);
lean_inc(v_defaultFacets_562_);
lean_inc(v_extraDepTargets_561_);
lean_inc(v_needs_560_);
lean_inc(v_libName_558_);
lean_inc(v_globs_557_);
lean_inc(v_roots_556_);
lean_inc(v_srcDir_555_);
lean_inc(v_toLeanConfig_554_);
lean_dec(v_cfg_553_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_toLeanConfig_554_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_srcDir_555_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_roots_556_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_globs_557_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_libName_558_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_needs_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_extraDepTargets_561_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_defaultFacets_562_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v_nativeFacets_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*9, v_libPrefixOnWindows_559_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*9 + 2, v_allowImportAll_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*9 + 1, v_val_552_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_572_, lean_object* v_cfg_573_){
_start:
{
uint8_t v_val_71__boxed_574_; lean_object* v_res_575_; 
v_val_71__boxed_574_ = lean_unbox(v_val_572_);
v_res_575_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__1(v_val_71__boxed_574_, v_cfg_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__2(lean_object* v_f_576_, lean_object* v_cfg_577_){
_start:
{
lean_object* v_toLeanConfig_578_; lean_object* v_srcDir_579_; lean_object* v_roots_580_; lean_object* v_globs_581_; lean_object* v_libName_582_; uint8_t v_libPrefixOnWindows_583_; lean_object* v_needs_584_; lean_object* v_extraDepTargets_585_; uint8_t v_precompileModules_586_; lean_object* v_defaultFacets_587_; lean_object* v_nativeFacets_588_; uint8_t v_allowImportAll_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_599_; 
v_toLeanConfig_578_ = lean_ctor_get(v_cfg_577_, 0);
v_srcDir_579_ = lean_ctor_get(v_cfg_577_, 1);
v_roots_580_ = lean_ctor_get(v_cfg_577_, 2);
v_globs_581_ = lean_ctor_get(v_cfg_577_, 3);
v_libName_582_ = lean_ctor_get(v_cfg_577_, 4);
v_libPrefixOnWindows_583_ = lean_ctor_get_uint8(v_cfg_577_, sizeof(void*)*9);
v_needs_584_ = lean_ctor_get(v_cfg_577_, 5);
v_extraDepTargets_585_ = lean_ctor_get(v_cfg_577_, 6);
v_precompileModules_586_ = lean_ctor_get_uint8(v_cfg_577_, sizeof(void*)*9 + 1);
v_defaultFacets_587_ = lean_ctor_get(v_cfg_577_, 7);
v_nativeFacets_588_ = lean_ctor_get(v_cfg_577_, 8);
v_allowImportAll_589_ = lean_ctor_get_uint8(v_cfg_577_, sizeof(void*)*9 + 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_cfg_577_);
if (v_isSharedCheck_599_ == 0)
{
v___x_591_ = v_cfg_577_;
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_nativeFacets_588_);
lean_inc(v_defaultFacets_587_);
lean_inc(v_extraDepTargets_585_);
lean_inc(v_needs_584_);
lean_inc(v_libName_582_);
lean_inc(v_globs_581_);
lean_inc(v_roots_580_);
lean_inc(v_srcDir_579_);
lean_inc(v_toLeanConfig_578_);
lean_dec(v_cfg_577_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_593_ = lean_box(v_precompileModules_586_);
v___x_594_ = lean_apply_1(v_f_576_, v___x_593_);
if (v_isShared_592_ == 0)
{
v___x_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_toLeanConfig_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_srcDir_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_roots_580_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_globs_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_libName_582_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_needs_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_extraDepTargets_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_defaultFacets_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_nativeFacets_588_);
lean_ctor_set_uint8(v_reuseFailAlloc_598_, sizeof(void*)*9, v_libPrefixOnWindows_583_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
uint8_t v___x_597_; 
v___x_597_ = lean_unbox(v___x_594_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*9 + 1, v___x_597_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*9 + 2, v_allowImportAll_589_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object* v_name_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileModules___proj___closed__3));
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object* v_name_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_610_);
lean_dec(v_name_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object* v_name_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object* v_name_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_614_);
lean_dec(v_name_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(lean_object* v_cfg_616_){
_start:
{
lean_object* v_defaultFacets_617_; 
v_defaultFacets_617_ = lean_ctor_get(v_cfg_616_, 7);
lean_inc_ref(v_defaultFacets_617_);
return v_defaultFacets_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed(lean_object* v_cfg_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(v_cfg_618_);
lean_dec_ref(v_cfg_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__1(lean_object* v_val_620_, lean_object* v_cfg_621_){
_start:
{
lean_object* v_toLeanConfig_622_; lean_object* v_srcDir_623_; lean_object* v_roots_624_; lean_object* v_globs_625_; lean_object* v_libName_626_; uint8_t v_libPrefixOnWindows_627_; lean_object* v_needs_628_; lean_object* v_extraDepTargets_629_; uint8_t v_precompileModules_630_; lean_object* v_nativeFacets_631_; uint8_t v_allowImportAll_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_toLeanConfig_622_ = lean_ctor_get(v_cfg_621_, 0);
v_srcDir_623_ = lean_ctor_get(v_cfg_621_, 1);
v_roots_624_ = lean_ctor_get(v_cfg_621_, 2);
v_globs_625_ = lean_ctor_get(v_cfg_621_, 3);
v_libName_626_ = lean_ctor_get(v_cfg_621_, 4);
v_libPrefixOnWindows_627_ = lean_ctor_get_uint8(v_cfg_621_, sizeof(void*)*9);
v_needs_628_ = lean_ctor_get(v_cfg_621_, 5);
v_extraDepTargets_629_ = lean_ctor_get(v_cfg_621_, 6);
v_precompileModules_630_ = lean_ctor_get_uint8(v_cfg_621_, sizeof(void*)*9 + 1);
v_nativeFacets_631_ = lean_ctor_get(v_cfg_621_, 8);
v_allowImportAll_632_ = lean_ctor_get_uint8(v_cfg_621_, sizeof(void*)*9 + 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_cfg_621_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v_cfg_621_, 7);
lean_dec(v_unused_640_);
v___x_634_ = v_cfg_621_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_nativeFacets_631_);
lean_inc(v_extraDepTargets_629_);
lean_inc(v_needs_628_);
lean_inc(v_libName_626_);
lean_inc(v_globs_625_);
lean_inc(v_roots_624_);
lean_inc(v_srcDir_623_);
lean_inc(v_toLeanConfig_622_);
lean_dec(v_cfg_621_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 7, v_val_620_);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_toLeanConfig_622_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_srcDir_623_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_roots_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_globs_625_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_libName_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v_needs_628_);
lean_ctor_set(v_reuseFailAlloc_638_, 6, v_extraDepTargets_629_);
lean_ctor_set(v_reuseFailAlloc_638_, 7, v_val_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 8, v_nativeFacets_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_638_, sizeof(void*)*9, v_libPrefixOnWindows_627_);
lean_ctor_set_uint8(v_reuseFailAlloc_638_, sizeof(void*)*9 + 1, v_precompileModules_630_);
lean_ctor_set_uint8(v_reuseFailAlloc_638_, sizeof(void*)*9 + 2, v_allowImportAll_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__2(lean_object* v_f_641_, lean_object* v_cfg_642_){
_start:
{
lean_object* v_toLeanConfig_643_; lean_object* v_srcDir_644_; lean_object* v_roots_645_; lean_object* v_globs_646_; lean_object* v_libName_647_; uint8_t v_libPrefixOnWindows_648_; lean_object* v_needs_649_; lean_object* v_extraDepTargets_650_; uint8_t v_precompileModules_651_; lean_object* v_defaultFacets_652_; lean_object* v_nativeFacets_653_; uint8_t v_allowImportAll_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
v_toLeanConfig_643_ = lean_ctor_get(v_cfg_642_, 0);
v_srcDir_644_ = lean_ctor_get(v_cfg_642_, 1);
v_roots_645_ = lean_ctor_get(v_cfg_642_, 2);
v_globs_646_ = lean_ctor_get(v_cfg_642_, 3);
v_libName_647_ = lean_ctor_get(v_cfg_642_, 4);
v_libPrefixOnWindows_648_ = lean_ctor_get_uint8(v_cfg_642_, sizeof(void*)*9);
v_needs_649_ = lean_ctor_get(v_cfg_642_, 5);
v_extraDepTargets_650_ = lean_ctor_get(v_cfg_642_, 6);
v_precompileModules_651_ = lean_ctor_get_uint8(v_cfg_642_, sizeof(void*)*9 + 1);
v_defaultFacets_652_ = lean_ctor_get(v_cfg_642_, 7);
v_nativeFacets_653_ = lean_ctor_get(v_cfg_642_, 8);
v_allowImportAll_654_ = lean_ctor_get_uint8(v_cfg_642_, sizeof(void*)*9 + 2);
v_isSharedCheck_662_ = !lean_is_exclusive(v_cfg_642_);
if (v_isSharedCheck_662_ == 0)
{
v___x_656_ = v_cfg_642_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_nativeFacets_653_);
lean_inc(v_defaultFacets_652_);
lean_inc(v_extraDepTargets_650_);
lean_inc(v_needs_649_);
lean_inc(v_libName_647_);
lean_inc(v_globs_646_);
lean_inc(v_roots_645_);
lean_inc(v_srcDir_644_);
lean_inc(v_toLeanConfig_643_);
lean_dec(v_cfg_642_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = lean_apply_1(v_f_641_, v_defaultFacets_652_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 7, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_toLeanConfig_643_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_srcDir_644_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_roots_645_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_globs_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_libName_647_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v_needs_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 6, v_extraDepTargets_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 7, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_661_, 8, v_nativeFacets_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*9, v_libPrefixOnWindows_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*9 + 1, v_precompileModules_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*9 + 2, v_allowImportAll_654_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_mk_empty_array_with_capacity(v___x_664_);
lean_dec_ref(v___x_665_);
v___x_666_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__5, &l_Lake_instInhabitedLeanLibConfig_default___closed__5_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__5);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed(lean_object* v_x_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(v_x_667_);
lean_dec_ref(v_x_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object* v_name_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = ((lean_object*)(l_Lake_LeanLibConfig_defaultFacets___proj___closed__4));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object* v_name_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_680_);
lean_dec(v_name_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object* v_name_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object* v_name_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_684_);
lean_dec(v_name_684_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(lean_object* v_cfg_686_, uint8_t v___y_687_){
_start:
{
lean_object* v_nativeFacets_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_nativeFacets_688_ = lean_ctor_get(v_cfg_686_, 8);
lean_inc_ref(v_nativeFacets_688_);
lean_dec_ref(v_cfg_686_);
v___x_689_ = lean_box(v___y_687_);
v___x_690_ = lean_apply_1(v_nativeFacets_688_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed(lean_object* v_cfg_691_, lean_object* v___y_692_){
_start:
{
uint8_t v___y_147__boxed_693_; lean_object* v_res_694_; 
v___y_147__boxed_693_ = lean_unbox(v___y_692_);
v_res_694_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(v_cfg_691_, v___y_147__boxed_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__1(lean_object* v_val_695_, lean_object* v_cfg_696_){
_start:
{
lean_object* v_toLeanConfig_697_; lean_object* v_srcDir_698_; lean_object* v_roots_699_; lean_object* v_globs_700_; lean_object* v_libName_701_; uint8_t v_libPrefixOnWindows_702_; lean_object* v_needs_703_; lean_object* v_extraDepTargets_704_; uint8_t v_precompileModules_705_; lean_object* v_defaultFacets_706_; uint8_t v_allowImportAll_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_toLeanConfig_697_ = lean_ctor_get(v_cfg_696_, 0);
v_srcDir_698_ = lean_ctor_get(v_cfg_696_, 1);
v_roots_699_ = lean_ctor_get(v_cfg_696_, 2);
v_globs_700_ = lean_ctor_get(v_cfg_696_, 3);
v_libName_701_ = lean_ctor_get(v_cfg_696_, 4);
v_libPrefixOnWindows_702_ = lean_ctor_get_uint8(v_cfg_696_, sizeof(void*)*9);
v_needs_703_ = lean_ctor_get(v_cfg_696_, 5);
v_extraDepTargets_704_ = lean_ctor_get(v_cfg_696_, 6);
v_precompileModules_705_ = lean_ctor_get_uint8(v_cfg_696_, sizeof(void*)*9 + 1);
v_defaultFacets_706_ = lean_ctor_get(v_cfg_696_, 7);
v_allowImportAll_707_ = lean_ctor_get_uint8(v_cfg_696_, sizeof(void*)*9 + 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_cfg_696_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_cfg_696_, 8);
lean_dec(v_unused_715_);
v___x_709_ = v_cfg_696_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_defaultFacets_706_);
lean_inc(v_extraDepTargets_704_);
lean_inc(v_needs_703_);
lean_inc(v_libName_701_);
lean_inc(v_globs_700_);
lean_inc(v_roots_699_);
lean_inc(v_srcDir_698_);
lean_inc(v_toLeanConfig_697_);
lean_dec(v_cfg_696_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 8, v_val_695_);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_toLeanConfig_697_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_srcDir_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_roots_699_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_globs_700_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_libName_701_);
lean_ctor_set(v_reuseFailAlloc_713_, 5, v_needs_703_);
lean_ctor_set(v_reuseFailAlloc_713_, 6, v_extraDepTargets_704_);
lean_ctor_set(v_reuseFailAlloc_713_, 7, v_defaultFacets_706_);
lean_ctor_set(v_reuseFailAlloc_713_, 8, v_val_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*9, v_libPrefixOnWindows_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*9 + 1, v_precompileModules_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*9 + 2, v_allowImportAll_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__2(lean_object* v_f_716_, lean_object* v_cfg_717_){
_start:
{
lean_object* v_toLeanConfig_718_; lean_object* v_srcDir_719_; lean_object* v_roots_720_; lean_object* v_globs_721_; lean_object* v_libName_722_; uint8_t v_libPrefixOnWindows_723_; lean_object* v_needs_724_; lean_object* v_extraDepTargets_725_; uint8_t v_precompileModules_726_; lean_object* v_defaultFacets_727_; lean_object* v_nativeFacets_728_; uint8_t v_allowImportAll_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
v_toLeanConfig_718_ = lean_ctor_get(v_cfg_717_, 0);
v_srcDir_719_ = lean_ctor_get(v_cfg_717_, 1);
v_roots_720_ = lean_ctor_get(v_cfg_717_, 2);
v_globs_721_ = lean_ctor_get(v_cfg_717_, 3);
v_libName_722_ = lean_ctor_get(v_cfg_717_, 4);
v_libPrefixOnWindows_723_ = lean_ctor_get_uint8(v_cfg_717_, sizeof(void*)*9);
v_needs_724_ = lean_ctor_get(v_cfg_717_, 5);
v_extraDepTargets_725_ = lean_ctor_get(v_cfg_717_, 6);
v_precompileModules_726_ = lean_ctor_get_uint8(v_cfg_717_, sizeof(void*)*9 + 1);
v_defaultFacets_727_ = lean_ctor_get(v_cfg_717_, 7);
v_nativeFacets_728_ = lean_ctor_get(v_cfg_717_, 8);
v_allowImportAll_729_ = lean_ctor_get_uint8(v_cfg_717_, sizeof(void*)*9 + 2);
v_isSharedCheck_737_ = !lean_is_exclusive(v_cfg_717_);
if (v_isSharedCheck_737_ == 0)
{
v___x_731_ = v_cfg_717_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_nativeFacets_728_);
lean_inc(v_defaultFacets_727_);
lean_inc(v_extraDepTargets_725_);
lean_inc(v_needs_724_);
lean_inc(v_libName_722_);
lean_inc(v_globs_721_);
lean_inc(v_roots_720_);
lean_inc(v_srcDir_719_);
lean_inc(v_toLeanConfig_718_);
lean_dec(v_cfg_717_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = lean_apply_1(v_f_716_, v_nativeFacets_728_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 8, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_toLeanConfig_718_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_srcDir_719_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_roots_720_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_globs_721_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_libName_722_);
lean_ctor_set(v_reuseFailAlloc_736_, 5, v_needs_724_);
lean_ctor_set(v_reuseFailAlloc_736_, 6, v_extraDepTargets_725_);
lean_ctor_set(v_reuseFailAlloc_736_, 7, v_defaultFacets_727_);
lean_ctor_set(v_reuseFailAlloc_736_, 8, v___x_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_736_, sizeof(void*)*9, v_libPrefixOnWindows_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_736_, sizeof(void*)*9 + 1, v_precompileModules_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_736_, sizeof(void*)*9 + 2, v_allowImportAll_729_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(lean_object* v_x_738_, uint8_t v___y_739_){
_start:
{
lean_object* v___y_741_; 
if (v___y_739_ == 0)
{
lean_object* v___x_745_; 
v___x_745_ = l_Lake_Module_oFacet;
v___y_741_ = v___x_745_;
goto v___jp_740_;
}
else
{
lean_object* v___x_746_; 
v___x_746_ = l_Lake_Module_oExportFacet;
v___y_741_ = v___x_746_;
goto v___jp_740_;
}
v___jp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_mk_empty_array_with_capacity(v___x_742_);
lean_inc(v___y_741_);
v___x_744_ = lean_array_push(v___x_743_, v___y_741_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed(lean_object* v_x_747_, lean_object* v___y_748_){
_start:
{
uint8_t v___y_197__boxed_749_; lean_object* v_res_750_; 
v___y_197__boxed_749_ = lean_unbox(v___y_748_);
v_res_750_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(v_x_747_, v___y_197__boxed_749_);
lean_dec_ref(v_x_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object* v_name_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Lake_LeanLibConfig_nativeFacets___proj___closed__4));
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object* v_name_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_762_);
lean_dec(v_name_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object* v_name_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object* v_name_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_766_);
lean_dec(v_name_766_);
return v_res_767_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_768_){
_start:
{
uint8_t v_allowImportAll_769_; 
v_allowImportAll_769_ = lean_ctor_get_uint8(v_cfg_768_, sizeof(void*)*9 + 2);
return v_allowImportAll_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(v_cfg_770_);
lean_dec_ref(v_cfg_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(uint8_t v_val_773_, lean_object* v_cfg_774_){
_start:
{
lean_object* v_toLeanConfig_775_; lean_object* v_srcDir_776_; lean_object* v_roots_777_; lean_object* v_globs_778_; lean_object* v_libName_779_; uint8_t v_libPrefixOnWindows_780_; lean_object* v_needs_781_; lean_object* v_extraDepTargets_782_; uint8_t v_precompileModules_783_; lean_object* v_defaultFacets_784_; lean_object* v_nativeFacets_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_toLeanConfig_775_ = lean_ctor_get(v_cfg_774_, 0);
v_srcDir_776_ = lean_ctor_get(v_cfg_774_, 1);
v_roots_777_ = lean_ctor_get(v_cfg_774_, 2);
v_globs_778_ = lean_ctor_get(v_cfg_774_, 3);
v_libName_779_ = lean_ctor_get(v_cfg_774_, 4);
v_libPrefixOnWindows_780_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*9);
v_needs_781_ = lean_ctor_get(v_cfg_774_, 5);
v_extraDepTargets_782_ = lean_ctor_get(v_cfg_774_, 6);
v_precompileModules_783_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*9 + 1);
v_defaultFacets_784_ = lean_ctor_get(v_cfg_774_, 7);
v_nativeFacets_785_ = lean_ctor_get(v_cfg_774_, 8);
v_isSharedCheck_792_ = !lean_is_exclusive(v_cfg_774_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v_cfg_774_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_nativeFacets_785_);
lean_inc(v_defaultFacets_784_);
lean_inc(v_extraDepTargets_782_);
lean_inc(v_needs_781_);
lean_inc(v_libName_779_);
lean_inc(v_globs_778_);
lean_inc(v_roots_777_);
lean_inc(v_srcDir_776_);
lean_inc(v_toLeanConfig_775_);
lean_dec(v_cfg_774_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_toLeanConfig_775_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_srcDir_776_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_roots_777_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_globs_778_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_libName_779_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v_needs_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_extraDepTargets_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v_defaultFacets_784_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_nativeFacets_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*9, v_libPrefixOnWindows_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*9 + 1, v_precompileModules_783_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*9 + 2, v_val_773_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_793_, lean_object* v_cfg_794_){
_start:
{
uint8_t v_val_71__boxed_795_; lean_object* v_res_796_; 
v_val_71__boxed_795_ = lean_unbox(v_val_793_);
v_res_796_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(v_val_71__boxed_795_, v_cfg_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__2(lean_object* v_f_797_, lean_object* v_cfg_798_){
_start:
{
lean_object* v_toLeanConfig_799_; lean_object* v_srcDir_800_; lean_object* v_roots_801_; lean_object* v_globs_802_; lean_object* v_libName_803_; uint8_t v_libPrefixOnWindows_804_; lean_object* v_needs_805_; lean_object* v_extraDepTargets_806_; uint8_t v_precompileModules_807_; lean_object* v_defaultFacets_808_; lean_object* v_nativeFacets_809_; uint8_t v_allowImportAll_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_820_; 
v_toLeanConfig_799_ = lean_ctor_get(v_cfg_798_, 0);
v_srcDir_800_ = lean_ctor_get(v_cfg_798_, 1);
v_roots_801_ = lean_ctor_get(v_cfg_798_, 2);
v_globs_802_ = lean_ctor_get(v_cfg_798_, 3);
v_libName_803_ = lean_ctor_get(v_cfg_798_, 4);
v_libPrefixOnWindows_804_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9);
v_needs_805_ = lean_ctor_get(v_cfg_798_, 5);
v_extraDepTargets_806_ = lean_ctor_get(v_cfg_798_, 6);
v_precompileModules_807_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9 + 1);
v_defaultFacets_808_ = lean_ctor_get(v_cfg_798_, 7);
v_nativeFacets_809_ = lean_ctor_get(v_cfg_798_, 8);
v_allowImportAll_810_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9 + 2);
v_isSharedCheck_820_ = !lean_is_exclusive(v_cfg_798_);
if (v_isSharedCheck_820_ == 0)
{
v___x_812_ = v_cfg_798_;
v_isShared_813_ = v_isSharedCheck_820_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_nativeFacets_809_);
lean_inc(v_defaultFacets_808_);
lean_inc(v_extraDepTargets_806_);
lean_inc(v_needs_805_);
lean_inc(v_libName_803_);
lean_inc(v_globs_802_);
lean_inc(v_roots_801_);
lean_inc(v_srcDir_800_);
lean_inc(v_toLeanConfig_799_);
lean_dec(v_cfg_798_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_820_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_814_ = lean_box(v_allowImportAll_810_);
v___x_815_ = lean_apply_1(v_f_797_, v___x_814_);
if (v_isShared_813_ == 0)
{
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_toLeanConfig_799_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_srcDir_800_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_roots_801_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_globs_802_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_libName_803_);
lean_ctor_set(v_reuseFailAlloc_819_, 5, v_needs_805_);
lean_ctor_set(v_reuseFailAlloc_819_, 6, v_extraDepTargets_806_);
lean_ctor_set(v_reuseFailAlloc_819_, 7, v_defaultFacets_808_);
lean_ctor_set(v_reuseFailAlloc_819_, 8, v_nativeFacets_809_);
lean_ctor_set_uint8(v_reuseFailAlloc_819_, sizeof(void*)*9, v_libPrefixOnWindows_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_819_, sizeof(void*)*9 + 1, v_precompileModules_807_);
v___x_817_ = v_reuseFailAlloc_819_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
uint8_t v___x_818_; 
v___x_818_ = lean_unbox(v___x_815_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*9 + 2, v___x_818_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object* v_name_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = ((lean_object*)(l_Lake_LeanLibConfig_allowImportAll___proj___closed__3));
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object* v_name_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_831_);
lean_dec(v_name_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object* v_name_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object* v_name_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_835_);
lean_dec(v_name_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_837_){
_start:
{
lean_object* v_toLeanConfig_838_; 
v_toLeanConfig_838_ = lean_ctor_get(v_cfg_837_, 0);
lean_inc_ref(v_toLeanConfig_838_);
return v_toLeanConfig_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(v_cfg_839_);
lean_dec_ref(v_cfg_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1(lean_object* v_val_841_, lean_object* v_cfg_842_){
_start:
{
lean_object* v_srcDir_843_; lean_object* v_roots_844_; lean_object* v_globs_845_; lean_object* v_libName_846_; uint8_t v_libPrefixOnWindows_847_; lean_object* v_needs_848_; lean_object* v_extraDepTargets_849_; uint8_t v_precompileModules_850_; lean_object* v_defaultFacets_851_; lean_object* v_nativeFacets_852_; uint8_t v_allowImportAll_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_srcDir_843_ = lean_ctor_get(v_cfg_842_, 1);
v_roots_844_ = lean_ctor_get(v_cfg_842_, 2);
v_globs_845_ = lean_ctor_get(v_cfg_842_, 3);
v_libName_846_ = lean_ctor_get(v_cfg_842_, 4);
v_libPrefixOnWindows_847_ = lean_ctor_get_uint8(v_cfg_842_, sizeof(void*)*9);
v_needs_848_ = lean_ctor_get(v_cfg_842_, 5);
v_extraDepTargets_849_ = lean_ctor_get(v_cfg_842_, 6);
v_precompileModules_850_ = lean_ctor_get_uint8(v_cfg_842_, sizeof(void*)*9 + 1);
v_defaultFacets_851_ = lean_ctor_get(v_cfg_842_, 7);
v_nativeFacets_852_ = lean_ctor_get(v_cfg_842_, 8);
v_allowImportAll_853_ = lean_ctor_get_uint8(v_cfg_842_, sizeof(void*)*9 + 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_cfg_842_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_cfg_842_, 0);
lean_dec(v_unused_861_);
v___x_855_ = v_cfg_842_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_nativeFacets_852_);
lean_inc(v_defaultFacets_851_);
lean_inc(v_extraDepTargets_849_);
lean_inc(v_needs_848_);
lean_inc(v_libName_846_);
lean_inc(v_globs_845_);
lean_inc(v_roots_844_);
lean_inc(v_srcDir_843_);
lean_dec(v_cfg_842_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_val_841_);
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_val_841_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_srcDir_843_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_roots_844_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_globs_845_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_libName_846_);
lean_ctor_set(v_reuseFailAlloc_859_, 5, v_needs_848_);
lean_ctor_set(v_reuseFailAlloc_859_, 6, v_extraDepTargets_849_);
lean_ctor_set(v_reuseFailAlloc_859_, 7, v_defaultFacets_851_);
lean_ctor_set(v_reuseFailAlloc_859_, 8, v_nativeFacets_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*9, v_libPrefixOnWindows_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*9 + 1, v_precompileModules_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*9 + 2, v_allowImportAll_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2(lean_object* v_f_862_, lean_object* v_cfg_863_){
_start:
{
lean_object* v_toLeanConfig_864_; lean_object* v_srcDir_865_; lean_object* v_roots_866_; lean_object* v_globs_867_; lean_object* v_libName_868_; uint8_t v_libPrefixOnWindows_869_; lean_object* v_needs_870_; lean_object* v_extraDepTargets_871_; uint8_t v_precompileModules_872_; lean_object* v_defaultFacets_873_; lean_object* v_nativeFacets_874_; uint8_t v_allowImportAll_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_toLeanConfig_864_ = lean_ctor_get(v_cfg_863_, 0);
v_srcDir_865_ = lean_ctor_get(v_cfg_863_, 1);
v_roots_866_ = lean_ctor_get(v_cfg_863_, 2);
v_globs_867_ = lean_ctor_get(v_cfg_863_, 3);
v_libName_868_ = lean_ctor_get(v_cfg_863_, 4);
v_libPrefixOnWindows_869_ = lean_ctor_get_uint8(v_cfg_863_, sizeof(void*)*9);
v_needs_870_ = lean_ctor_get(v_cfg_863_, 5);
v_extraDepTargets_871_ = lean_ctor_get(v_cfg_863_, 6);
v_precompileModules_872_ = lean_ctor_get_uint8(v_cfg_863_, sizeof(void*)*9 + 1);
v_defaultFacets_873_ = lean_ctor_get(v_cfg_863_, 7);
v_nativeFacets_874_ = lean_ctor_get(v_cfg_863_, 8);
v_allowImportAll_875_ = lean_ctor_get_uint8(v_cfg_863_, sizeof(void*)*9 + 2);
v_isSharedCheck_883_ = !lean_is_exclusive(v_cfg_863_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v_cfg_863_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_nativeFacets_874_);
lean_inc(v_defaultFacets_873_);
lean_inc(v_extraDepTargets_871_);
lean_inc(v_needs_870_);
lean_inc(v_libName_868_);
lean_inc(v_globs_867_);
lean_inc(v_roots_866_);
lean_inc(v_srcDir_865_);
lean_inc(v_toLeanConfig_864_);
lean_dec(v_cfg_863_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_apply_1(v_f_862_, v_toLeanConfig_864_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_srcDir_865_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_roots_866_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_globs_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_libName_868_);
lean_ctor_set(v_reuseFailAlloc_882_, 5, v_needs_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 6, v_extraDepTargets_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 7, v_defaultFacets_873_);
lean_ctor_set(v_reuseFailAlloc_882_, 8, v_nativeFacets_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_882_, sizeof(void*)*9, v_libPrefixOnWindows_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_882_, sizeof(void*)*9 + 1, v_precompileModules_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_882_, sizeof(void*)*9 + 2, v_allowImportAll_875_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(v_x_886_);
lean_dec_ref(v_x_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object* v_name_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4));
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object* v_name_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_899_);
lean_dec(v_name_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(lean_object* v_name_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_name_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(v_name_903_);
lean_dec(v_name_903_);
return v_res_904_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__3));
v___x_915_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__0));
v___x_916_ = lean_array_push(v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__7));
v___x_925_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__4, &l_Lake_LeanLibConfig___fields___closed__4_once, _init_l_Lake_LeanLibConfig___fields___closed__4);
v___x_926_ = lean_array_push(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__11));
v___x_935_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__8, &l_Lake_LeanLibConfig___fields___closed__8_once, _init_l_Lake_LeanLibConfig___fields___closed__8);
v___x_936_ = lean_array_push(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__15));
v___x_945_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__12, &l_Lake_LeanLibConfig___fields___closed__12_once, _init_l_Lake_LeanLibConfig___fields___closed__12);
v___x_946_ = lean_array_push(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__19));
v___x_955_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__16, &l_Lake_LeanLibConfig___fields___closed__16_once, _init_l_Lake_LeanLibConfig___fields___closed__16);
v___x_956_ = lean_array_push(v___x_955_, v___x_954_);
return v___x_956_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__23));
v___x_965_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__20, &l_Lake_LeanLibConfig___fields___closed__20_once, _init_l_Lake_LeanLibConfig___fields___closed__20);
v___x_966_ = lean_array_push(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__27));
v___x_975_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__24, &l_Lake_LeanLibConfig___fields___closed__24_once, _init_l_Lake_LeanLibConfig___fields___closed__24);
v___x_976_ = lean_array_push(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__31));
v___x_985_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__28, &l_Lake_LeanLibConfig___fields___closed__28_once, _init_l_Lake_LeanLibConfig___fields___closed__28);
v___x_986_ = lean_array_push(v___x_985_, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__35));
v___x_995_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__32, &l_Lake_LeanLibConfig___fields___closed__32_once, _init_l_Lake_LeanLibConfig___fields___closed__32);
v___x_996_ = lean_array_push(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__39));
v___x_1005_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__36, &l_Lake_LeanLibConfig___fields___closed__36_once, _init_l_Lake_LeanLibConfig___fields___closed__36);
v___x_1006_ = lean_array_push(v___x_1005_, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__43));
v___x_1015_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__40, &l_Lake_LeanLibConfig___fields___closed__40_once, _init_l_Lake_LeanLibConfig___fields___closed__40);
v___x_1016_ = lean_array_push(v___x_1015_, v___x_1014_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = l_Lake_LeanConfig___fields;
v___x_1018_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__44, &l_Lake_LeanLibConfig___fields___closed__44_once, _init_l_Lake_LeanLibConfig___fields___closed__44);
v___x_1019_ = l_Array_append___redArg(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__49(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__48));
v___x_1028_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__45, &l_Lake_LeanLibConfig___fields___closed__45_once, _init_l_Lake_LeanLibConfig___fields___closed__45);
v___x_1029_ = lean_array_push(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields(void){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__49, &l_Lake_LeanLibConfig___fields___closed__49_once, _init_l_Lake_LeanLibConfig___fields___closed__49);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields(lean_object* v_name_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lake_LeanLibConfig___fields;
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___boxed(lean_object* v_name_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lake_LeanLibConfig_instConfigFields(v_name_1033_);
lean_dec(v_name_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo___lam__0(lean_object* v_x1_1035_, lean_object* v_x2_1036_){
_start:
{
lean_object* v_name_1037_; lean_object* v___x_1038_; 
v_name_1037_ = lean_ctor_get(v_x2_1036_, 0);
lean_inc(v_name_1037_);
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1037_, v_x2_1036_, v_x1_1035_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = l_Lake_LeanLibConfig___fields;
v___x_1040_ = lean_array_get_size(v___x_1039_);
return v___x_1040_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_nat_dec_lt(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1065_ = lean_nat_dec_le(v___x_1064_, v___x_1064_);
return v___x_1065_;
}
}
static size_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_1066_; size_t v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1067_ = lean_usize_of_nat(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1068_ = lean_box(1);
v___x_1069_ = lean_usize_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__14, &l_Lake_LeanLibConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14);
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = l_Lake_LeanLibConfig___fields;
v___f_1072_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__12));
v___x_1073_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1073_, v___f_1072_, v___x_1071_, v___x_1070_, v___x_1069_, v___x_1068_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___y_1077_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1075_ = l_Lake_LeanLibConfig___fields;
v___x_1080_ = lean_box(1);
v___x_1081_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__11, &l_Lake_LeanLibConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11);
if (v___x_1081_ == 0)
{
v___y_1077_ = v___x_1080_;
goto v___jp_1076_;
}
else
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__13, &l_Lake_LeanLibConfig_instConfigInfo___closed__13_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13);
if (v___x_1082_ == 0)
{
if (v___x_1081_ == 0)
{
v___y_1077_ = v___x_1080_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1077_ = v___x_1083_;
goto v___jp_1076_;
}
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1077_ = v___x_1084_;
goto v___jp_1076_;
}
}
v___jp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_1077_);
v___x_1079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1075_);
lean_ctor_set(v___x_1079_, 1, v___y_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__0(lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection(lean_object* v_name_1088_){
_start:
{
lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; size_t v_sz_1098_; size_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___f_1089_ = ((lean_object*)(l_Lake_LeanLibConfig_instEmptyCollection___closed__0));
v___f_1090_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_1091_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_1092_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_1093_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_mk_empty_array_with_capacity(v___x_1094_);
v___x_1096_ = lean_array_push(v___x_1095_, v_name_1088_);
v___x_1097_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v_sz_1098_ = lean_array_size(v___x_1096_);
v___x_1099_ = ((size_t)0ULL);
lean_inc_ref(v___x_1096_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1097_, v___f_1089_, v_sz_1098_, v___x_1099_, v___x_1096_);
v___x_1101_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__4));
v___x_1102_ = 0;
v___x_1103_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__5, &l_Lake_instInhabitedLeanLibConfig_default___closed__5_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__5);
v___x_1104_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_1104_, 0, v___x_1092_);
lean_ctor_set(v___x_1104_, 1, v___x_1093_);
lean_ctor_set(v___x_1104_, 2, v___x_1096_);
lean_ctor_set(v___x_1104_, 3, v___x_1100_);
lean_ctor_set(v___x_1104_, 4, v___x_1101_);
lean_ctor_set(v___x_1104_, 5, v___x_1091_);
lean_ctor_set(v___x_1104_, 6, v___x_1091_);
lean_ctor_set(v___x_1104_, 7, v___x_1103_);
lean_ctor_set(v___x_1104_, 8, v___f_1090_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*9, v___x_1102_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*9 + 1, v___x_1102_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*9 + 2, v___x_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg(lean_object* v_n_1105_){
_start:
{
lean_inc(v_n_1105_);
return v_n_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg___boxed(lean_object* v_n_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lake_LeanLibConfig_name___redArg(v_n_1106_);
lean_dec(v_n_1106_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name(lean_object* v_n_1108_, lean_object* v_x_1109_){
_start:
{
lean_inc(v_n_1108_);
return v_n_1108_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___boxed(lean_object* v_n_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lake_LeanLibConfig_name(v_n_1110_, v_x_1111_);
lean_dec_ref(v_x_1111_);
lean_dec(v_n_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(lean_object* v_mod_1113_, lean_object* v_as_1114_, size_t v_i_1115_, size_t v_stop_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_usize_dec_eq(v_i_1115_, v_stop_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_array_uget_borrowed(v_as_1114_, v_i_1115_);
v___x_1119_ = l_Lake_Glob_matches(v_mod_1113_, v___x_1118_);
if (v___x_1119_ == 0)
{
size_t v___x_1120_; size_t v___x_1121_; 
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1115_, v___x_1120_);
v_i_1115_ = v___x_1121_;
goto _start;
}
else
{
return v___x_1119_;
}
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = 0;
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(lean_object* v_mod_1124_, lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_stop_1127_){
_start:
{
size_t v_i_boxed_1128_; size_t v_stop_boxed_1129_; uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_i_boxed_1128_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_stop_boxed_1129_ = lean_unbox_usize(v_stop_1127_);
lean_dec(v_stop_1127_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1124_, v_as_1125_, v_i_boxed_1128_, v_stop_boxed_1129_);
lean_dec_ref(v_as_1125_);
lean_dec(v_mod_1124_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(lean_object* v_mod_1132_, lean_object* v_as_1133_, size_t v_i_1134_, size_t v_stop_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_usize_dec_eq(v_i_1134_, v_stop_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_array_uget_borrowed(v_as_1133_, v_i_1134_);
v___x_1138_ = l_Lean_Name_isPrefixOf(v___x_1137_, v_mod_1132_);
if (v___x_1138_ == 0)
{
size_t v___x_1139_; size_t v___x_1140_; 
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_add(v_i_1134_, v___x_1139_);
v_i_1134_ = v___x_1140_;
goto _start;
}
else
{
return v___x_1138_;
}
}
else
{
uint8_t v___x_1142_; 
v___x_1142_ = 0;
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(lean_object* v_mod_1143_, lean_object* v_as_1144_, lean_object* v_i_1145_, lean_object* v_stop_1146_){
_start:
{
size_t v_i_boxed_1147_; size_t v_stop_boxed_1148_; uint8_t v_res_1149_; lean_object* v_r_1150_; 
v_i_boxed_1147_ = lean_unbox_usize(v_i_1145_);
lean_dec(v_i_1145_);
v_stop_boxed_1148_ = lean_unbox_usize(v_stop_1146_);
lean_dec(v_stop_1146_);
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1143_, v_as_1144_, v_i_boxed_1147_, v_stop_boxed_1148_);
lean_dec_ref(v_as_1144_);
lean_dec(v_mod_1143_);
v_r_1150_ = lean_box(v_res_1149_);
return v_r_1150_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object* v_mod_1151_, lean_object* v_self_1152_){
_start:
{
lean_object* v_roots_1153_; lean_object* v_globs_1154_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_roots_1153_ = lean_ctor_get(v_self_1152_, 2);
v_globs_1154_ = lean_ctor_get(v_self_1152_, 3);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_array_get_size(v_roots_1153_);
v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
goto v___jp_1155_;
}
else
{
if (v___x_1164_ == 0)
{
goto v___jp_1155_;
}
else
{
size_t v___x_1165_; size_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = lean_usize_of_nat(v___x_1163_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1151_, v_roots_1153_, v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
goto v___jp_1155_;
}
else
{
return v___x_1167_;
}
}
}
v___jp_1155_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_array_get_size(v_globs_1154_);
v___x_1158_ = lean_nat_dec_lt(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
return v___x_1158_;
}
else
{
if (v___x_1158_ == 0)
{
return v___x_1158_;
}
else
{
size_t v___x_1159_; size_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = lean_usize_of_nat(v___x_1157_);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1151_, v_globs_1154_, v___x_1159_, v___x_1160_);
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(lean_object* v_mod_1168_, lean_object* v_self_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1168_, v_self_1169_);
lean_dec_ref(v_self_1169_);
lean_dec(v_mod_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object* v_n_1172_, lean_object* v_mod_1173_, lean_object* v_self_1174_){
_start:
{
uint8_t v___x_1175_; 
v___x_1175_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1173_, v_self_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___boxed(lean_object* v_n_1176_, lean_object* v_mod_1177_, lean_object* v_self_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l_Lake_LeanLibConfig_isLocalModule(v_n_1176_, v_mod_1177_, v_self_1178_);
lean_dec_ref(v_self_1178_);
lean_dec(v_mod_1177_);
lean_dec(v_n_1176_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(lean_object* v_mod_1181_, lean_object* v_self_1182_, lean_object* v_as_1183_, size_t v_i_1184_, size_t v_stop_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_eq(v_i_1184_, v_stop_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; uint8_t v___y_1189_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1187_ = 1;
v___x_1193_ = lean_array_uget_borrowed(v_as_1183_, v_i_1184_);
v___x_1194_ = l_Lean_Name_isPrefixOf(v___x_1193_, v_mod_1181_);
if (v___x_1194_ == 0)
{
v___y_1189_ = v___x_1194_;
goto v___jp_1188_;
}
else
{
lean_object* v_globs_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_globs_1195_ = lean_ctor_get(v_self_1182_, 3);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_globs_1195_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
v___y_1189_ = v___x_1186_;
goto v___jp_1188_;
}
else
{
if (v___x_1198_ == 0)
{
v___y_1189_ = v___x_1186_;
goto v___jp_1188_;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_of_nat(v___x_1197_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v___x_1193_, v_globs_1195_, v___x_1199_, v___x_1200_);
v___y_1189_ = v___x_1201_;
goto v___jp_1188_;
}
}
}
v___jp_1188_:
{
if (v___y_1189_ == 0)
{
size_t v___x_1190_; size_t v___x_1191_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1184_, v___x_1190_);
v_i_1184_ = v___x_1191_;
goto _start;
}
else
{
return v___x_1187_;
}
}
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = 0;
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(lean_object* v_mod_1203_, lean_object* v_self_1204_, lean_object* v_as_1205_, lean_object* v_i_1206_, lean_object* v_stop_1207_){
_start:
{
size_t v_i_boxed_1208_; size_t v_stop_boxed_1209_; uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_i_boxed_1208_ = lean_unbox_usize(v_i_1206_);
lean_dec(v_i_1206_);
v_stop_boxed_1209_ = lean_unbox_usize(v_stop_1207_);
lean_dec(v_stop_1207_);
v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1203_, v_self_1204_, v_as_1205_, v_i_boxed_1208_, v_stop_boxed_1209_);
lean_dec_ref(v_as_1205_);
lean_dec_ref(v_self_1204_);
lean_dec(v_mod_1203_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object* v_mod_1212_, lean_object* v_self_1213_){
_start:
{
lean_object* v_roots_1214_; lean_object* v_globs_1215_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_roots_1214_ = lean_ctor_get(v_self_1213_, 2);
v_globs_1215_ = lean_ctor_get(v_self_1213_, 3);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_array_get_size(v_globs_1215_);
v___x_1225_ = lean_nat_dec_lt(v___x_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
goto v___jp_1216_;
}
else
{
if (v___x_1225_ == 0)
{
goto v___jp_1216_;
}
else
{
size_t v___x_1226_; size_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1224_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1212_, v_globs_1215_, v___x_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
goto v___jp_1216_;
}
else
{
return v___x_1228_;
}
}
}
v___jp_1216_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_array_get_size(v_roots_1214_);
v___x_1219_ = lean_nat_dec_lt(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
return v___x_1219_;
}
else
{
if (v___x_1219_ == 0)
{
return v___x_1219_;
}
else
{
size_t v___x_1220_; size_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = ((size_t)0ULL);
v___x_1221_ = lean_usize_of_nat(v___x_1218_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1212_, v_self_1213_, v_roots_1214_, v___x_1220_, v___x_1221_);
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(lean_object* v_mod_1229_, lean_object* v_self_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1229_, v_self_1230_);
lean_dec_ref(v_self_1230_);
lean_dec(v_mod_1229_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object* v_n_1233_, lean_object* v_mod_1234_, lean_object* v_self_1235_){
_start:
{
uint8_t v___x_1236_; 
v___x_1236_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1234_, v_self_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___boxed(lean_object* v_n_1237_, lean_object* v_mod_1238_, lean_object* v_self_1239_){
_start:
{
uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_res_1240_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_1237_, v_mod_1238_, v_self_1239_);
lean_dec_ref(v_self_1239_);
lean_dec(v_mod_1238_);
lean_dec(v_n_1237_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Casing(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Facets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Glob(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanLibConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Casing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Facets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanLibConfig___fields = _init_l_Lake_LeanLibConfig___fields();
lean_mark_persistent(l_Lake_LeanLibConfig___fields);
l_Lake_LeanLibConfig_instConfigInfo = _init_l_Lake_LeanLibConfig_instConfigInfo();
lean_mark_persistent(l_Lake_LeanLibConfig_instConfigInfo);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_LeanLibConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin);
lean_object* initialize_Lake_Util_Casing(uint8_t builtin);
lean_object* initialize_Lake_Build_Facets(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_Glob(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LeanLibConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Casing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Facets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanLibConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_LeanLibConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_LeanLibConfig(builtin);
}
#ifdef __cplusplus
}
#endif
