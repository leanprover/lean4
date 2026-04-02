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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_oFacet;
extern lean_object* l_Lake_Module_oExportFacet;
extern lean_object* l_System_instInhabitedFilePath_default;
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
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
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static const lean_array_object l_Lake_instInhabitedLeanLibConfig_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instInhabitedLeanLibConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedLeanLibConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedLeanLibConfig_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lake_LeanLibConfig_srcDir___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___lam__3___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanLibConfig_globs___proj_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanLibConfig_globs___proj_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0;
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
static const lean_array_object l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value;
static const lean_ctor_object l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_instEmptyCollection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_instEmptyCollection___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instEmptyCollection___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_instEmptyCollection___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_instEmptyCollection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_instEmptyCollection___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_instEmptyCollection___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_instEmptyCollection___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0(uint8_t v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___lam__0___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_54__boxed_6_; lean_object* v_res_7_; 
v_x_54__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_instInhabitedLeanLibConfig_default___lam__0(v_x_54__boxed_6_);
return v_res_7_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanLibConfig_default___closed__2(void){
_start:
{
lean_object* v___f_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___f_10_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_11_ = 0;
v___x_12_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_13_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___lam__0___closed__0));
v___x_14_ = l_System_instInhabitedFilePath_default;
v___x_15_ = l_Lake_instInhabitedLeanConfig_default;
v___x_16_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
lean_ctor_set(v___x_16_, 3, v___x_13_);
lean_ctor_set(v___x_16_, 4, v___x_12_);
lean_ctor_set(v___x_16_, 5, v___x_13_);
lean_ctor_set(v___x_16_, 6, v___x_13_);
lean_ctor_set(v___x_16_, 7, v___x_13_);
lean_ctor_set(v___x_16_, 8, v___f_10_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*9, v___x_11_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*9 + 1, v___x_11_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*9 + 2, v___x_11_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default(lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__2, &l_Lake_instInhabitedLeanLibConfig_default___closed__2_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__2);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___boxed(lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_instInhabitedLeanLibConfig_default(v_a_19_);
lean_dec(v_a_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig(lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lake_instInhabitedLeanLibConfig_default(v_a_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig___boxed(lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_instInhabitedLeanLibConfig(v_a_23_);
lean_dec(v_a_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0(lean_object* v_cfg_25_){
_start:
{
lean_object* v_srcDir_26_; 
v_srcDir_26_ = lean_ctor_get(v_cfg_25_, 1);
lean_inc_ref(v_srcDir_26_);
return v_srcDir_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_LeanLibConfig_srcDir___proj___lam__0(v_cfg_27_);
lean_dec_ref(v_cfg_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__1(lean_object* v_val_29_, lean_object* v_cfg_30_){
_start:
{
lean_object* v_toLeanConfig_31_; lean_object* v_roots_32_; lean_object* v_globs_33_; lean_object* v_libName_34_; uint8_t v_libPrefixOnWindows_35_; lean_object* v_needs_36_; lean_object* v_extraDepTargets_37_; uint8_t v_precompileModules_38_; lean_object* v_defaultFacets_39_; lean_object* v_nativeFacets_40_; uint8_t v_allowImportAll_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_toLeanConfig_31_ = lean_ctor_get(v_cfg_30_, 0);
v_roots_32_ = lean_ctor_get(v_cfg_30_, 2);
v_globs_33_ = lean_ctor_get(v_cfg_30_, 3);
v_libName_34_ = lean_ctor_get(v_cfg_30_, 4);
v_libPrefixOnWindows_35_ = lean_ctor_get_uint8(v_cfg_30_, sizeof(void*)*9);
v_needs_36_ = lean_ctor_get(v_cfg_30_, 5);
v_extraDepTargets_37_ = lean_ctor_get(v_cfg_30_, 6);
v_precompileModules_38_ = lean_ctor_get_uint8(v_cfg_30_, sizeof(void*)*9 + 1);
v_defaultFacets_39_ = lean_ctor_get(v_cfg_30_, 7);
v_nativeFacets_40_ = lean_ctor_get(v_cfg_30_, 8);
v_allowImportAll_41_ = lean_ctor_get_uint8(v_cfg_30_, sizeof(void*)*9 + 2);
v_isSharedCheck_48_ = !lean_is_exclusive(v_cfg_30_);
if (v_isSharedCheck_48_ == 0)
{
lean_object* v_unused_49_; 
v_unused_49_ = lean_ctor_get(v_cfg_30_, 1);
lean_dec(v_unused_49_);
v___x_43_ = v_cfg_30_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_nativeFacets_40_);
lean_inc(v_defaultFacets_39_);
lean_inc(v_extraDepTargets_37_);
lean_inc(v_needs_36_);
lean_inc(v_libName_34_);
lean_inc(v_globs_33_);
lean_inc(v_roots_32_);
lean_inc(v_toLeanConfig_31_);
lean_dec(v_cfg_30_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v_val_29_);
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_toLeanConfig_31_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_val_29_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v_roots_32_);
lean_ctor_set(v_reuseFailAlloc_47_, 3, v_globs_33_);
lean_ctor_set(v_reuseFailAlloc_47_, 4, v_libName_34_);
lean_ctor_set(v_reuseFailAlloc_47_, 5, v_needs_36_);
lean_ctor_set(v_reuseFailAlloc_47_, 6, v_extraDepTargets_37_);
lean_ctor_set(v_reuseFailAlloc_47_, 7, v_defaultFacets_39_);
lean_ctor_set(v_reuseFailAlloc_47_, 8, v_nativeFacets_40_);
lean_ctor_set_uint8(v_reuseFailAlloc_47_, sizeof(void*)*9, v_libPrefixOnWindows_35_);
lean_ctor_set_uint8(v_reuseFailAlloc_47_, sizeof(void*)*9 + 1, v_precompileModules_38_);
lean_ctor_set_uint8(v_reuseFailAlloc_47_, sizeof(void*)*9 + 2, v_allowImportAll_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__2(lean_object* v_f_50_, lean_object* v_cfg_51_){
_start:
{
lean_object* v_toLeanConfig_52_; lean_object* v_srcDir_53_; lean_object* v_roots_54_; lean_object* v_globs_55_; lean_object* v_libName_56_; uint8_t v_libPrefixOnWindows_57_; lean_object* v_needs_58_; lean_object* v_extraDepTargets_59_; uint8_t v_precompileModules_60_; lean_object* v_defaultFacets_61_; lean_object* v_nativeFacets_62_; uint8_t v_allowImportAll_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_71_; 
v_toLeanConfig_52_ = lean_ctor_get(v_cfg_51_, 0);
v_srcDir_53_ = lean_ctor_get(v_cfg_51_, 1);
v_roots_54_ = lean_ctor_get(v_cfg_51_, 2);
v_globs_55_ = lean_ctor_get(v_cfg_51_, 3);
v_libName_56_ = lean_ctor_get(v_cfg_51_, 4);
v_libPrefixOnWindows_57_ = lean_ctor_get_uint8(v_cfg_51_, sizeof(void*)*9);
v_needs_58_ = lean_ctor_get(v_cfg_51_, 5);
v_extraDepTargets_59_ = lean_ctor_get(v_cfg_51_, 6);
v_precompileModules_60_ = lean_ctor_get_uint8(v_cfg_51_, sizeof(void*)*9 + 1);
v_defaultFacets_61_ = lean_ctor_get(v_cfg_51_, 7);
v_nativeFacets_62_ = lean_ctor_get(v_cfg_51_, 8);
v_allowImportAll_63_ = lean_ctor_get_uint8(v_cfg_51_, sizeof(void*)*9 + 2);
v_isSharedCheck_71_ = !lean_is_exclusive(v_cfg_51_);
if (v_isSharedCheck_71_ == 0)
{
v___x_65_ = v_cfg_51_;
v_isShared_66_ = v_isSharedCheck_71_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_nativeFacets_62_);
lean_inc(v_defaultFacets_61_);
lean_inc(v_extraDepTargets_59_);
lean_inc(v_needs_58_);
lean_inc(v_libName_56_);
lean_inc(v_globs_55_);
lean_inc(v_roots_54_);
lean_inc(v_srcDir_53_);
lean_inc(v_toLeanConfig_52_);
lean_dec(v_cfg_51_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_71_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_apply_1(v_f_50_, v_srcDir_53_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_67_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_toLeanConfig_52_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v_roots_54_);
lean_ctor_set(v_reuseFailAlloc_70_, 3, v_globs_55_);
lean_ctor_set(v_reuseFailAlloc_70_, 4, v_libName_56_);
lean_ctor_set(v_reuseFailAlloc_70_, 5, v_needs_58_);
lean_ctor_set(v_reuseFailAlloc_70_, 6, v_extraDepTargets_59_);
lean_ctor_set(v_reuseFailAlloc_70_, 7, v_defaultFacets_61_);
lean_ctor_set(v_reuseFailAlloc_70_, 8, v_nativeFacets_62_);
lean_ctor_set_uint8(v_reuseFailAlloc_70_, sizeof(void*)*9, v_libPrefixOnWindows_57_);
lean_ctor_set_uint8(v_reuseFailAlloc_70_, sizeof(void*)*9 + 1, v_precompileModules_60_);
lean_ctor_set_uint8(v_reuseFailAlloc_70_, sizeof(void*)*9 + 2, v_allowImportAll_63_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3(lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___lam__3___closed__0));
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lake_LeanLibConfig_srcDir___proj___lam__3(v_x_75_);
lean_dec_ref(v_x_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object* v_name_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___closed__4));
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object* v_name_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_88_);
lean_dec(v_name_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object* v_name_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object* v_name_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_92_);
lean_dec(v_name_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object* v_cfg_94_){
_start:
{
lean_object* v_roots_95_; 
v_roots_95_ = lean_ctor_get(v_cfg_94_, 2);
lean_inc_ref(v_roots_95_);
return v_roots_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object* v_cfg_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_96_);
lean_dec_ref(v_cfg_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object* v_val_98_, lean_object* v_cfg_99_){
_start:
{
lean_object* v_toLeanConfig_100_; lean_object* v_srcDir_101_; lean_object* v_globs_102_; lean_object* v_libName_103_; uint8_t v_libPrefixOnWindows_104_; lean_object* v_needs_105_; lean_object* v_extraDepTargets_106_; uint8_t v_precompileModules_107_; lean_object* v_defaultFacets_108_; lean_object* v_nativeFacets_109_; uint8_t v_allowImportAll_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_toLeanConfig_100_ = lean_ctor_get(v_cfg_99_, 0);
v_srcDir_101_ = lean_ctor_get(v_cfg_99_, 1);
v_globs_102_ = lean_ctor_get(v_cfg_99_, 3);
v_libName_103_ = lean_ctor_get(v_cfg_99_, 4);
v_libPrefixOnWindows_104_ = lean_ctor_get_uint8(v_cfg_99_, sizeof(void*)*9);
v_needs_105_ = lean_ctor_get(v_cfg_99_, 5);
v_extraDepTargets_106_ = lean_ctor_get(v_cfg_99_, 6);
v_precompileModules_107_ = lean_ctor_get_uint8(v_cfg_99_, sizeof(void*)*9 + 1);
v_defaultFacets_108_ = lean_ctor_get(v_cfg_99_, 7);
v_nativeFacets_109_ = lean_ctor_get(v_cfg_99_, 8);
v_allowImportAll_110_ = lean_ctor_get_uint8(v_cfg_99_, sizeof(void*)*9 + 2);
v_isSharedCheck_117_ = !lean_is_exclusive(v_cfg_99_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; 
v_unused_118_ = lean_ctor_get(v_cfg_99_, 2);
lean_dec(v_unused_118_);
v___x_112_ = v_cfg_99_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_nativeFacets_109_);
lean_inc(v_defaultFacets_108_);
lean_inc(v_extraDepTargets_106_);
lean_inc(v_needs_105_);
lean_inc(v_libName_103_);
lean_inc(v_globs_102_);
lean_inc(v_srcDir_101_);
lean_inc(v_toLeanConfig_100_);
lean_dec(v_cfg_99_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 2, v_val_98_);
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_toLeanConfig_100_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_srcDir_101_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_val_98_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_globs_102_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_libName_103_);
lean_ctor_set(v_reuseFailAlloc_116_, 5, v_needs_105_);
lean_ctor_set(v_reuseFailAlloc_116_, 6, v_extraDepTargets_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 7, v_defaultFacets_108_);
lean_ctor_set(v_reuseFailAlloc_116_, 8, v_nativeFacets_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*9, v_libPrefixOnWindows_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*9 + 1, v_precompileModules_107_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*9 + 2, v_allowImportAll_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object* v_f_119_, lean_object* v_cfg_120_){
_start:
{
lean_object* v_toLeanConfig_121_; lean_object* v_srcDir_122_; lean_object* v_roots_123_; lean_object* v_globs_124_; lean_object* v_libName_125_; uint8_t v_libPrefixOnWindows_126_; lean_object* v_needs_127_; lean_object* v_extraDepTargets_128_; uint8_t v_precompileModules_129_; lean_object* v_defaultFacets_130_; lean_object* v_nativeFacets_131_; uint8_t v_allowImportAll_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_toLeanConfig_121_ = lean_ctor_get(v_cfg_120_, 0);
v_srcDir_122_ = lean_ctor_get(v_cfg_120_, 1);
v_roots_123_ = lean_ctor_get(v_cfg_120_, 2);
v_globs_124_ = lean_ctor_get(v_cfg_120_, 3);
v_libName_125_ = lean_ctor_get(v_cfg_120_, 4);
v_libPrefixOnWindows_126_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*9);
v_needs_127_ = lean_ctor_get(v_cfg_120_, 5);
v_extraDepTargets_128_ = lean_ctor_get(v_cfg_120_, 6);
v_precompileModules_129_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*9 + 1);
v_defaultFacets_130_ = lean_ctor_get(v_cfg_120_, 7);
v_nativeFacets_131_ = lean_ctor_get(v_cfg_120_, 8);
v_allowImportAll_132_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*9 + 2);
v_isSharedCheck_140_ = !lean_is_exclusive(v_cfg_120_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v_cfg_120_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_nativeFacets_131_);
lean_inc(v_defaultFacets_130_);
lean_inc(v_extraDepTargets_128_);
lean_inc(v_needs_127_);
lean_inc(v_libName_125_);
lean_inc(v_globs_124_);
lean_inc(v_roots_123_);
lean_inc(v_srcDir_122_);
lean_inc(v_toLeanConfig_121_);
lean_dec(v_cfg_120_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_apply_1(v_f_119_, v_roots_123_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 2, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_toLeanConfig_121_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_srcDir_122_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_globs_124_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v_libName_125_);
lean_ctor_set(v_reuseFailAlloc_139_, 5, v_needs_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 6, v_extraDepTargets_128_);
lean_ctor_set(v_reuseFailAlloc_139_, 7, v_defaultFacets_130_);
lean_ctor_set(v_reuseFailAlloc_139_, 8, v_nativeFacets_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*9, v_libPrefixOnWindows_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*9 + 1, v_precompileModules_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*9 + 2, v_allowImportAll_132_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object* v_name_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_array_push(v___x_144_, v_name_141_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object* v_name_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_146_, v_x_147_);
lean_dec_ref(v_x_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object* v_name_152_){
_start:
{
lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_153_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__0));
v___f_154_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__1));
v___f_155_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__2));
v___f_156_ = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_roots___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_156_, 0, v_name_152_);
v___x_157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_157_, 0, v___f_153_);
lean_ctor_set(v___x_157_, 1, v___f_154_);
lean_ctor_set(v___x_157_, 2, v___f_155_);
lean_ctor_set(v___x_157_, 3, v___f_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object* v_name_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lake_LeanLibConfig_roots___proj(v_name_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0(lean_object* v_cfg_160_){
_start:
{
lean_object* v_globs_161_; 
v_globs_161_ = lean_ctor_get(v_cfg_160_, 3);
lean_inc_ref(v_globs_161_);
return v_globs_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0___boxed(lean_object* v_cfg_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lake_LeanLibConfig_globs___proj___lam__0(v_cfg_162_);
lean_dec_ref(v_cfg_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__1(lean_object* v_val_164_, lean_object* v_cfg_165_){
_start:
{
lean_object* v_toLeanConfig_166_; lean_object* v_srcDir_167_; lean_object* v_roots_168_; lean_object* v_libName_169_; uint8_t v_libPrefixOnWindows_170_; lean_object* v_needs_171_; lean_object* v_extraDepTargets_172_; uint8_t v_precompileModules_173_; lean_object* v_defaultFacets_174_; lean_object* v_nativeFacets_175_; uint8_t v_allowImportAll_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_toLeanConfig_166_ = lean_ctor_get(v_cfg_165_, 0);
v_srcDir_167_ = lean_ctor_get(v_cfg_165_, 1);
v_roots_168_ = lean_ctor_get(v_cfg_165_, 2);
v_libName_169_ = lean_ctor_get(v_cfg_165_, 4);
v_libPrefixOnWindows_170_ = lean_ctor_get_uint8(v_cfg_165_, sizeof(void*)*9);
v_needs_171_ = lean_ctor_get(v_cfg_165_, 5);
v_extraDepTargets_172_ = lean_ctor_get(v_cfg_165_, 6);
v_precompileModules_173_ = lean_ctor_get_uint8(v_cfg_165_, sizeof(void*)*9 + 1);
v_defaultFacets_174_ = lean_ctor_get(v_cfg_165_, 7);
v_nativeFacets_175_ = lean_ctor_get(v_cfg_165_, 8);
v_allowImportAll_176_ = lean_ctor_get_uint8(v_cfg_165_, sizeof(void*)*9 + 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v_cfg_165_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_cfg_165_, 3);
lean_dec(v_unused_184_);
v___x_178_ = v_cfg_165_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_nativeFacets_175_);
lean_inc(v_defaultFacets_174_);
lean_inc(v_extraDepTargets_172_);
lean_inc(v_needs_171_);
lean_inc(v_libName_169_);
lean_inc(v_roots_168_);
lean_inc(v_srcDir_167_);
lean_inc(v_toLeanConfig_166_);
lean_dec(v_cfg_165_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 3, v_val_164_);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_toLeanConfig_166_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_srcDir_167_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_roots_168_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_val_164_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_libName_169_);
lean_ctor_set(v_reuseFailAlloc_182_, 5, v_needs_171_);
lean_ctor_set(v_reuseFailAlloc_182_, 6, v_extraDepTargets_172_);
lean_ctor_set(v_reuseFailAlloc_182_, 7, v_defaultFacets_174_);
lean_ctor_set(v_reuseFailAlloc_182_, 8, v_nativeFacets_175_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9, v_libPrefixOnWindows_170_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9 + 1, v_precompileModules_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9 + 2, v_allowImportAll_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__2(lean_object* v_f_185_, lean_object* v_cfg_186_){
_start:
{
lean_object* v_toLeanConfig_187_; lean_object* v_srcDir_188_; lean_object* v_roots_189_; lean_object* v_globs_190_; lean_object* v_libName_191_; uint8_t v_libPrefixOnWindows_192_; lean_object* v_needs_193_; lean_object* v_extraDepTargets_194_; uint8_t v_precompileModules_195_; lean_object* v_defaultFacets_196_; lean_object* v_nativeFacets_197_; uint8_t v_allowImportAll_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
v_toLeanConfig_187_ = lean_ctor_get(v_cfg_186_, 0);
v_srcDir_188_ = lean_ctor_get(v_cfg_186_, 1);
v_roots_189_ = lean_ctor_get(v_cfg_186_, 2);
v_globs_190_ = lean_ctor_get(v_cfg_186_, 3);
v_libName_191_ = lean_ctor_get(v_cfg_186_, 4);
v_libPrefixOnWindows_192_ = lean_ctor_get_uint8(v_cfg_186_, sizeof(void*)*9);
v_needs_193_ = lean_ctor_get(v_cfg_186_, 5);
v_extraDepTargets_194_ = lean_ctor_get(v_cfg_186_, 6);
v_precompileModules_195_ = lean_ctor_get_uint8(v_cfg_186_, sizeof(void*)*9 + 1);
v_defaultFacets_196_ = lean_ctor_get(v_cfg_186_, 7);
v_nativeFacets_197_ = lean_ctor_get(v_cfg_186_, 8);
v_allowImportAll_198_ = lean_ctor_get_uint8(v_cfg_186_, sizeof(void*)*9 + 2);
v_isSharedCheck_206_ = !lean_is_exclusive(v_cfg_186_);
if (v_isSharedCheck_206_ == 0)
{
v___x_200_ = v_cfg_186_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_nativeFacets_197_);
lean_inc(v_defaultFacets_196_);
lean_inc(v_extraDepTargets_194_);
lean_inc(v_needs_193_);
lean_inc(v_libName_191_);
lean_inc(v_globs_190_);
lean_inc(v_roots_189_);
lean_inc(v_srcDir_188_);
lean_inc(v_toLeanConfig_187_);
lean_dec(v_cfg_186_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_apply_1(v_f_185_, v_globs_190_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 3, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_toLeanConfig_187_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_srcDir_188_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_roots_189_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_libName_191_);
lean_ctor_set(v_reuseFailAlloc_205_, 5, v_needs_193_);
lean_ctor_set(v_reuseFailAlloc_205_, 6, v_extraDepTargets_194_);
lean_ctor_set(v_reuseFailAlloc_205_, 7, v_defaultFacets_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 8, v_nativeFacets_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, sizeof(void*)*9, v_libPrefixOnWindows_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, sizeof(void*)*9 + 1, v_precompileModules_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, sizeof(void*)*9 + 2, v_allowImportAll_198_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanLibConfig_globs___proj_spec__0(size_t v_sz_207_, size_t v_i_208_, lean_object* v_bs_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lean_usize_dec_lt(v_i_208_, v_sz_207_);
if (v___x_210_ == 0)
{
return v_bs_209_;
}
else
{
lean_object* v_v_211_; lean_object* v___x_212_; lean_object* v_bs_x27_213_; lean_object* v___x_214_; size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v_v_211_ = lean_array_uget(v_bs_209_, v_i_208_);
v___x_212_ = lean_unsigned_to_nat(0u);
v_bs_x27_213_ = lean_array_uset(v_bs_209_, v_i_208_, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v_v_211_);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_add(v_i_208_, v___x_215_);
v___x_217_ = lean_array_uset(v_bs_x27_213_, v_i_208_, v___x_214_);
v_i_208_ = v___x_216_;
v_bs_209_ = v___x_217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanLibConfig_globs___proj_spec__0___boxed(lean_object* v_sz_219_, lean_object* v_i_220_, lean_object* v_bs_221_){
_start:
{
size_t v_sz_boxed_222_; size_t v_i_boxed_223_; lean_object* v_res_224_; 
v_sz_boxed_222_ = lean_unbox_usize(v_sz_219_);
lean_dec(v_sz_219_);
v_i_boxed_223_ = lean_unbox_usize(v_i_220_);
lean_dec(v_i_220_);
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanLibConfig_globs___proj_spec__0(v_sz_boxed_222_, v_i_boxed_223_, v_bs_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__3(lean_object* v_x_225_){
_start:
{
lean_object* v_roots_226_; size_t v_sz_227_; size_t v___x_228_; lean_object* v___x_229_; 
v_roots_226_ = lean_ctor_get(v_x_225_, 2);
lean_inc_ref(v_roots_226_);
lean_dec_ref(v_x_225_);
v_sz_227_ = lean_array_size(v_roots_226_);
v___x_228_ = ((size_t)0ULL);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanLibConfig_globs___proj_spec__0(v_sz_227_, v___x_228_, v_roots_226_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object* v_name_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = ((lean_object*)(l_Lake_LeanLibConfig_globs___proj___closed__4));
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object* v_name_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lake_LeanLibConfig_globs___proj(v_name_241_);
lean_dec(v_name_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object* v_name_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lake_LeanLibConfig_globs___proj(v_name_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object* v_name_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_245_);
lean_dec(v_name_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0(lean_object* v_cfg_247_){
_start:
{
lean_object* v_libName_248_; 
v_libName_248_ = lean_ctor_get(v_cfg_247_, 4);
lean_inc_ref(v_libName_248_);
return v_libName_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0___boxed(lean_object* v_cfg_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_LeanLibConfig_libName___proj___lam__0(v_cfg_249_);
lean_dec_ref(v_cfg_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__1(lean_object* v_val_251_, lean_object* v_cfg_252_){
_start:
{
lean_object* v_toLeanConfig_253_; lean_object* v_srcDir_254_; lean_object* v_roots_255_; lean_object* v_globs_256_; uint8_t v_libPrefixOnWindows_257_; lean_object* v_needs_258_; lean_object* v_extraDepTargets_259_; uint8_t v_precompileModules_260_; lean_object* v_defaultFacets_261_; lean_object* v_nativeFacets_262_; uint8_t v_allowImportAll_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_toLeanConfig_253_ = lean_ctor_get(v_cfg_252_, 0);
v_srcDir_254_ = lean_ctor_get(v_cfg_252_, 1);
v_roots_255_ = lean_ctor_get(v_cfg_252_, 2);
v_globs_256_ = lean_ctor_get(v_cfg_252_, 3);
v_libPrefixOnWindows_257_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*9);
v_needs_258_ = lean_ctor_get(v_cfg_252_, 5);
v_extraDepTargets_259_ = lean_ctor_get(v_cfg_252_, 6);
v_precompileModules_260_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*9 + 1);
v_defaultFacets_261_ = lean_ctor_get(v_cfg_252_, 7);
v_nativeFacets_262_ = lean_ctor_get(v_cfg_252_, 8);
v_allowImportAll_263_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*9 + 2);
v_isSharedCheck_270_ = !lean_is_exclusive(v_cfg_252_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v_cfg_252_, 4);
lean_dec(v_unused_271_);
v___x_265_ = v_cfg_252_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_nativeFacets_262_);
lean_inc(v_defaultFacets_261_);
lean_inc(v_extraDepTargets_259_);
lean_inc(v_needs_258_);
lean_inc(v_globs_256_);
lean_inc(v_roots_255_);
lean_inc(v_srcDir_254_);
lean_inc(v_toLeanConfig_253_);
lean_dec(v_cfg_252_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 4, v_val_251_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_toLeanConfig_253_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_srcDir_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_roots_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_globs_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_val_251_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_needs_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_extraDepTargets_259_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_defaultFacets_261_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_nativeFacets_262_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*9, v_libPrefixOnWindows_257_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*9 + 1, v_precompileModules_260_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*9 + 2, v_allowImportAll_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__2(lean_object* v_f_272_, lean_object* v_cfg_273_){
_start:
{
lean_object* v_toLeanConfig_274_; lean_object* v_srcDir_275_; lean_object* v_roots_276_; lean_object* v_globs_277_; lean_object* v_libName_278_; uint8_t v_libPrefixOnWindows_279_; lean_object* v_needs_280_; lean_object* v_extraDepTargets_281_; uint8_t v_precompileModules_282_; lean_object* v_defaultFacets_283_; lean_object* v_nativeFacets_284_; uint8_t v_allowImportAll_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_toLeanConfig_274_ = lean_ctor_get(v_cfg_273_, 0);
v_srcDir_275_ = lean_ctor_get(v_cfg_273_, 1);
v_roots_276_ = lean_ctor_get(v_cfg_273_, 2);
v_globs_277_ = lean_ctor_get(v_cfg_273_, 3);
v_libName_278_ = lean_ctor_get(v_cfg_273_, 4);
v_libPrefixOnWindows_279_ = lean_ctor_get_uint8(v_cfg_273_, sizeof(void*)*9);
v_needs_280_ = lean_ctor_get(v_cfg_273_, 5);
v_extraDepTargets_281_ = lean_ctor_get(v_cfg_273_, 6);
v_precompileModules_282_ = lean_ctor_get_uint8(v_cfg_273_, sizeof(void*)*9 + 1);
v_defaultFacets_283_ = lean_ctor_get(v_cfg_273_, 7);
v_nativeFacets_284_ = lean_ctor_get(v_cfg_273_, 8);
v_allowImportAll_285_ = lean_ctor_get_uint8(v_cfg_273_, sizeof(void*)*9 + 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_cfg_273_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v_cfg_273_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_nativeFacets_284_);
lean_inc(v_defaultFacets_283_);
lean_inc(v_extraDepTargets_281_);
lean_inc(v_needs_280_);
lean_inc(v_libName_278_);
lean_inc(v_globs_277_);
lean_inc(v_roots_276_);
lean_inc(v_srcDir_275_);
lean_inc(v_toLeanConfig_274_);
lean_dec(v_cfg_273_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_apply_1(v_f_272_, v_libName_278_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 4, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_toLeanConfig_274_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_srcDir_275_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_roots_276_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_globs_277_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 5, v_needs_280_);
lean_ctor_set(v_reuseFailAlloc_292_, 6, v_extraDepTargets_281_);
lean_ctor_set(v_reuseFailAlloc_292_, 7, v_defaultFacets_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 8, v_nativeFacets_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*9, v_libPrefixOnWindows_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*9 + 1, v_precompileModules_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*9 + 2, v_allowImportAll_285_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3(lean_object* v_x_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lake_LeanLibConfig_libName___proj___lam__3(v_x_296_);
lean_dec_ref(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object* v_name_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Lake_LeanLibConfig_libName___proj___closed__4));
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object* v_name_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lake_LeanLibConfig_libName___proj(v_name_309_);
lean_dec(v_name_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object* v_name_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lake_LeanLibConfig_libName___proj(v_name_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object* v_name_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_313_);
lean_dec(v_name_313_);
return v_res_314_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_315_){
_start:
{
uint8_t v_libPrefixOnWindows_316_; 
v_libPrefixOnWindows_316_ = lean_ctor_get_uint8(v_cfg_315_, sizeof(void*)*9);
return v_libPrefixOnWindows_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(v_cfg_317_);
lean_dec_ref(v_cfg_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_320_, lean_object* v_cfg_321_){
_start:
{
lean_object* v_toLeanConfig_322_; lean_object* v_srcDir_323_; lean_object* v_roots_324_; lean_object* v_globs_325_; lean_object* v_libName_326_; lean_object* v_needs_327_; lean_object* v_extraDepTargets_328_; uint8_t v_precompileModules_329_; lean_object* v_defaultFacets_330_; lean_object* v_nativeFacets_331_; uint8_t v_allowImportAll_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_toLeanConfig_322_ = lean_ctor_get(v_cfg_321_, 0);
v_srcDir_323_ = lean_ctor_get(v_cfg_321_, 1);
v_roots_324_ = lean_ctor_get(v_cfg_321_, 2);
v_globs_325_ = lean_ctor_get(v_cfg_321_, 3);
v_libName_326_ = lean_ctor_get(v_cfg_321_, 4);
v_needs_327_ = lean_ctor_get(v_cfg_321_, 5);
v_extraDepTargets_328_ = lean_ctor_get(v_cfg_321_, 6);
v_precompileModules_329_ = lean_ctor_get_uint8(v_cfg_321_, sizeof(void*)*9 + 1);
v_defaultFacets_330_ = lean_ctor_get(v_cfg_321_, 7);
v_nativeFacets_331_ = lean_ctor_get(v_cfg_321_, 8);
v_allowImportAll_332_ = lean_ctor_get_uint8(v_cfg_321_, sizeof(void*)*9 + 2);
v_isSharedCheck_339_ = !lean_is_exclusive(v_cfg_321_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v_cfg_321_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_nativeFacets_331_);
lean_inc(v_defaultFacets_330_);
lean_inc(v_extraDepTargets_328_);
lean_inc(v_needs_327_);
lean_inc(v_libName_326_);
lean_inc(v_globs_325_);
lean_inc(v_roots_324_);
lean_inc(v_srcDir_323_);
lean_inc(v_toLeanConfig_322_);
lean_dec(v_cfg_321_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_toLeanConfig_322_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_srcDir_323_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_roots_324_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_globs_325_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_libName_326_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v_needs_327_);
lean_ctor_set(v_reuseFailAlloc_338_, 6, v_extraDepTargets_328_);
lean_ctor_set(v_reuseFailAlloc_338_, 7, v_defaultFacets_330_);
lean_ctor_set(v_reuseFailAlloc_338_, 8, v_nativeFacets_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*9 + 1, v_precompileModules_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*9 + 2, v_allowImportAll_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*9, v_val_320_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_340_, lean_object* v_cfg_341_){
_start:
{
uint8_t v_val_71__boxed_342_; lean_object* v_res_343_; 
v_val_71__boxed_342_ = lean_unbox(v_val_340_);
v_res_343_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(v_val_71__boxed_342_, v_cfg_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_344_, lean_object* v_cfg_345_){
_start:
{
lean_object* v_toLeanConfig_346_; lean_object* v_srcDir_347_; lean_object* v_roots_348_; lean_object* v_globs_349_; lean_object* v_libName_350_; uint8_t v_libPrefixOnWindows_351_; lean_object* v_needs_352_; lean_object* v_extraDepTargets_353_; uint8_t v_precompileModules_354_; lean_object* v_defaultFacets_355_; lean_object* v_nativeFacets_356_; uint8_t v_allowImportAll_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
v_toLeanConfig_346_ = lean_ctor_get(v_cfg_345_, 0);
v_srcDir_347_ = lean_ctor_get(v_cfg_345_, 1);
v_roots_348_ = lean_ctor_get(v_cfg_345_, 2);
v_globs_349_ = lean_ctor_get(v_cfg_345_, 3);
v_libName_350_ = lean_ctor_get(v_cfg_345_, 4);
v_libPrefixOnWindows_351_ = lean_ctor_get_uint8(v_cfg_345_, sizeof(void*)*9);
v_needs_352_ = lean_ctor_get(v_cfg_345_, 5);
v_extraDepTargets_353_ = lean_ctor_get(v_cfg_345_, 6);
v_precompileModules_354_ = lean_ctor_get_uint8(v_cfg_345_, sizeof(void*)*9 + 1);
v_defaultFacets_355_ = lean_ctor_get(v_cfg_345_, 7);
v_nativeFacets_356_ = lean_ctor_get(v_cfg_345_, 8);
v_allowImportAll_357_ = lean_ctor_get_uint8(v_cfg_345_, sizeof(void*)*9 + 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_cfg_345_);
if (v_isSharedCheck_367_ == 0)
{
v___x_359_ = v_cfg_345_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_nativeFacets_356_);
lean_inc(v_defaultFacets_355_);
lean_inc(v_extraDepTargets_353_);
lean_inc(v_needs_352_);
lean_inc(v_libName_350_);
lean_inc(v_globs_349_);
lean_inc(v_roots_348_);
lean_inc(v_srcDir_347_);
lean_inc(v_toLeanConfig_346_);
lean_dec(v_cfg_345_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_361_ = lean_box(v_libPrefixOnWindows_351_);
v___x_362_ = lean_apply_1(v_f_344_, v___x_361_);
if (v_isShared_360_ == 0)
{
v___x_364_ = v___x_359_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_toLeanConfig_346_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_srcDir_347_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_roots_348_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_globs_349_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_libName_350_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_needs_352_);
lean_ctor_set(v_reuseFailAlloc_366_, 6, v_extraDepTargets_353_);
lean_ctor_set(v_reuseFailAlloc_366_, 7, v_defaultFacets_355_);
lean_ctor_set(v_reuseFailAlloc_366_, 8, v_nativeFacets_356_);
v___x_364_ = v_reuseFailAlloc_366_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
uint8_t v___x_365_; 
v___x_365_ = lean_unbox(v___x_362_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*9, v___x_365_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*9 + 1, v_precompileModules_354_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*9 + 2, v_allowImportAll_357_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(lean_object* v_x_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed(lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(v_x_370_);
lean_dec_ref(v_x_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object* v_name_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = ((lean_object*)(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4));
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object* v_name_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_384_);
lean_dec(v_name_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object* v_name_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_name_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_388_);
lean_dec(v_name_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0(lean_object* v_cfg_390_){
_start:
{
lean_object* v_needs_391_; 
v_needs_391_ = lean_ctor_get(v_cfg_390_, 5);
lean_inc_ref(v_needs_391_);
return v_needs_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0___boxed(lean_object* v_cfg_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_LeanLibConfig_needs___proj___lam__0(v_cfg_392_);
lean_dec_ref(v_cfg_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__1(lean_object* v_val_394_, lean_object* v_cfg_395_){
_start:
{
lean_object* v_toLeanConfig_396_; lean_object* v_srcDir_397_; lean_object* v_roots_398_; lean_object* v_globs_399_; lean_object* v_libName_400_; uint8_t v_libPrefixOnWindows_401_; lean_object* v_extraDepTargets_402_; uint8_t v_precompileModules_403_; lean_object* v_defaultFacets_404_; lean_object* v_nativeFacets_405_; uint8_t v_allowImportAll_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_toLeanConfig_396_ = lean_ctor_get(v_cfg_395_, 0);
v_srcDir_397_ = lean_ctor_get(v_cfg_395_, 1);
v_roots_398_ = lean_ctor_get(v_cfg_395_, 2);
v_globs_399_ = lean_ctor_get(v_cfg_395_, 3);
v_libName_400_ = lean_ctor_get(v_cfg_395_, 4);
v_libPrefixOnWindows_401_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*9);
v_extraDepTargets_402_ = lean_ctor_get(v_cfg_395_, 6);
v_precompileModules_403_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*9 + 1);
v_defaultFacets_404_ = lean_ctor_get(v_cfg_395_, 7);
v_nativeFacets_405_ = lean_ctor_get(v_cfg_395_, 8);
v_allowImportAll_406_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*9 + 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_cfg_395_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_cfg_395_, 5);
lean_dec(v_unused_414_);
v___x_408_ = v_cfg_395_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_nativeFacets_405_);
lean_inc(v_defaultFacets_404_);
lean_inc(v_extraDepTargets_402_);
lean_inc(v_libName_400_);
lean_inc(v_globs_399_);
lean_inc(v_roots_398_);
lean_inc(v_srcDir_397_);
lean_inc(v_toLeanConfig_396_);
lean_dec(v_cfg_395_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 5, v_val_394_);
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_toLeanConfig_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_srcDir_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_roots_398_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_globs_399_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_libName_400_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_val_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_extraDepTargets_402_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_defaultFacets_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_nativeFacets_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, sizeof(void*)*9, v_libPrefixOnWindows_401_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, sizeof(void*)*9 + 1, v_precompileModules_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, sizeof(void*)*9 + 2, v_allowImportAll_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__2(lean_object* v_f_415_, lean_object* v_cfg_416_){
_start:
{
lean_object* v_toLeanConfig_417_; lean_object* v_srcDir_418_; lean_object* v_roots_419_; lean_object* v_globs_420_; lean_object* v_libName_421_; uint8_t v_libPrefixOnWindows_422_; lean_object* v_needs_423_; lean_object* v_extraDepTargets_424_; uint8_t v_precompileModules_425_; lean_object* v_defaultFacets_426_; lean_object* v_nativeFacets_427_; uint8_t v_allowImportAll_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_toLeanConfig_417_ = lean_ctor_get(v_cfg_416_, 0);
v_srcDir_418_ = lean_ctor_get(v_cfg_416_, 1);
v_roots_419_ = lean_ctor_get(v_cfg_416_, 2);
v_globs_420_ = lean_ctor_get(v_cfg_416_, 3);
v_libName_421_ = lean_ctor_get(v_cfg_416_, 4);
v_libPrefixOnWindows_422_ = lean_ctor_get_uint8(v_cfg_416_, sizeof(void*)*9);
v_needs_423_ = lean_ctor_get(v_cfg_416_, 5);
v_extraDepTargets_424_ = lean_ctor_get(v_cfg_416_, 6);
v_precompileModules_425_ = lean_ctor_get_uint8(v_cfg_416_, sizeof(void*)*9 + 1);
v_defaultFacets_426_ = lean_ctor_get(v_cfg_416_, 7);
v_nativeFacets_427_ = lean_ctor_get(v_cfg_416_, 8);
v_allowImportAll_428_ = lean_ctor_get_uint8(v_cfg_416_, sizeof(void*)*9 + 2);
v_isSharedCheck_436_ = !lean_is_exclusive(v_cfg_416_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v_cfg_416_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_nativeFacets_427_);
lean_inc(v_defaultFacets_426_);
lean_inc(v_extraDepTargets_424_);
lean_inc(v_needs_423_);
lean_inc(v_libName_421_);
lean_inc(v_globs_420_);
lean_inc(v_roots_419_);
lean_inc(v_srcDir_418_);
lean_inc(v_toLeanConfig_417_);
lean_dec(v_cfg_416_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_apply_1(v_f_415_, v_needs_423_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 5, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_toLeanConfig_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_srcDir_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_roots_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_globs_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_libName_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_extraDepTargets_424_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_defaultFacets_426_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_nativeFacets_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9, v_libPrefixOnWindows_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9 + 1, v_precompileModules_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9 + 2, v_allowImportAll_428_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3(lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___lam__3___closed__0));
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3___boxed(lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lake_LeanLibConfig_needs___proj___lam__3(v_x_441_);
lean_dec_ref(v_x_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object* v_name_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___closed__4));
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object* v_name_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lake_LeanLibConfig_needs___proj(v_name_454_);
lean_dec(v_name_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object* v_name_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lake_LeanLibConfig_needs___proj(v_name_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object* v_name_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_458_);
lean_dec(v_name_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_460_){
_start:
{
lean_object* v_extraDepTargets_461_; 
v_extraDepTargets_461_ = lean_ctor_get(v_cfg_460_, 6);
lean_inc_ref(v_extraDepTargets_461_);
return v_extraDepTargets_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(v_cfg_462_);
lean_dec_ref(v_cfg_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1(lean_object* v_val_464_, lean_object* v_cfg_465_){
_start:
{
lean_object* v_toLeanConfig_466_; lean_object* v_srcDir_467_; lean_object* v_roots_468_; lean_object* v_globs_469_; lean_object* v_libName_470_; uint8_t v_libPrefixOnWindows_471_; lean_object* v_needs_472_; uint8_t v_precompileModules_473_; lean_object* v_defaultFacets_474_; lean_object* v_nativeFacets_475_; uint8_t v_allowImportAll_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_toLeanConfig_466_ = lean_ctor_get(v_cfg_465_, 0);
v_srcDir_467_ = lean_ctor_get(v_cfg_465_, 1);
v_roots_468_ = lean_ctor_get(v_cfg_465_, 2);
v_globs_469_ = lean_ctor_get(v_cfg_465_, 3);
v_libName_470_ = lean_ctor_get(v_cfg_465_, 4);
v_libPrefixOnWindows_471_ = lean_ctor_get_uint8(v_cfg_465_, sizeof(void*)*9);
v_needs_472_ = lean_ctor_get(v_cfg_465_, 5);
v_precompileModules_473_ = lean_ctor_get_uint8(v_cfg_465_, sizeof(void*)*9 + 1);
v_defaultFacets_474_ = lean_ctor_get(v_cfg_465_, 7);
v_nativeFacets_475_ = lean_ctor_get(v_cfg_465_, 8);
v_allowImportAll_476_ = lean_ctor_get_uint8(v_cfg_465_, sizeof(void*)*9 + 2);
v_isSharedCheck_483_ = !lean_is_exclusive(v_cfg_465_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_cfg_465_, 6);
lean_dec(v_unused_484_);
v___x_478_ = v_cfg_465_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_nativeFacets_475_);
lean_inc(v_defaultFacets_474_);
lean_inc(v_needs_472_);
lean_inc(v_libName_470_);
lean_inc(v_globs_469_);
lean_inc(v_roots_468_);
lean_inc(v_srcDir_467_);
lean_inc(v_toLeanConfig_466_);
lean_dec(v_cfg_465_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 6, v_val_464_);
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_toLeanConfig_466_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_srcDir_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_roots_468_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_globs_469_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_libName_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_needs_472_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_val_464_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_defaultFacets_474_);
lean_ctor_set(v_reuseFailAlloc_482_, 8, v_nativeFacets_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*9, v_libPrefixOnWindows_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*9 + 1, v_precompileModules_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*9 + 2, v_allowImportAll_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2(lean_object* v_f_485_, lean_object* v_cfg_486_){
_start:
{
lean_object* v_toLeanConfig_487_; lean_object* v_srcDir_488_; lean_object* v_roots_489_; lean_object* v_globs_490_; lean_object* v_libName_491_; uint8_t v_libPrefixOnWindows_492_; lean_object* v_needs_493_; lean_object* v_extraDepTargets_494_; uint8_t v_precompileModules_495_; lean_object* v_defaultFacets_496_; lean_object* v_nativeFacets_497_; uint8_t v_allowImportAll_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_toLeanConfig_487_ = lean_ctor_get(v_cfg_486_, 0);
v_srcDir_488_ = lean_ctor_get(v_cfg_486_, 1);
v_roots_489_ = lean_ctor_get(v_cfg_486_, 2);
v_globs_490_ = lean_ctor_get(v_cfg_486_, 3);
v_libName_491_ = lean_ctor_get(v_cfg_486_, 4);
v_libPrefixOnWindows_492_ = lean_ctor_get_uint8(v_cfg_486_, sizeof(void*)*9);
v_needs_493_ = lean_ctor_get(v_cfg_486_, 5);
v_extraDepTargets_494_ = lean_ctor_get(v_cfg_486_, 6);
v_precompileModules_495_ = lean_ctor_get_uint8(v_cfg_486_, sizeof(void*)*9 + 1);
v_defaultFacets_496_ = lean_ctor_get(v_cfg_486_, 7);
v_nativeFacets_497_ = lean_ctor_get(v_cfg_486_, 8);
v_allowImportAll_498_ = lean_ctor_get_uint8(v_cfg_486_, sizeof(void*)*9 + 2);
v_isSharedCheck_506_ = !lean_is_exclusive(v_cfg_486_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v_cfg_486_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_nativeFacets_497_);
lean_inc(v_defaultFacets_496_);
lean_inc(v_extraDepTargets_494_);
lean_inc(v_needs_493_);
lean_inc(v_libName_491_);
lean_inc(v_globs_490_);
lean_inc(v_roots_489_);
lean_inc(v_srcDir_488_);
lean_inc(v_toLeanConfig_487_);
lean_dec(v_cfg_486_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_apply_1(v_f_485_, v_extraDepTargets_494_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 6, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_toLeanConfig_487_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_srcDir_488_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_roots_489_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_globs_490_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_libName_491_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_needs_493_);
lean_ctor_set(v_reuseFailAlloc_505_, 6, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 7, v_defaultFacets_496_);
lean_ctor_set(v_reuseFailAlloc_505_, 8, v_nativeFacets_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9, v_libPrefixOnWindows_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9 + 1, v_precompileModules_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9 + 2, v_allowImportAll_498_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(lean_object* v_x_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(v_x_511_);
lean_dec_ref(v_x_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object* v_name_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object* v_name_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_524_);
lean_dec(v_name_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object* v_name_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object* v_name_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_528_);
lean_dec(v_name_528_);
return v_res_529_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___lam__0(lean_object* v_cfg_530_){
_start:
{
uint8_t v_precompileModules_531_; 
v_precompileModules_531_ = lean_ctor_get_uint8(v_cfg_530_, sizeof(void*)*9 + 1);
return v_precompileModules_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__0(v_cfg_532_);
lean_dec_ref(v_cfg_532_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1(uint8_t v_val_535_, lean_object* v_cfg_536_){
_start:
{
lean_object* v_toLeanConfig_537_; lean_object* v_srcDir_538_; lean_object* v_roots_539_; lean_object* v_globs_540_; lean_object* v_libName_541_; uint8_t v_libPrefixOnWindows_542_; lean_object* v_needs_543_; lean_object* v_extraDepTargets_544_; lean_object* v_defaultFacets_545_; lean_object* v_nativeFacets_546_; uint8_t v_allowImportAll_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_toLeanConfig_537_ = lean_ctor_get(v_cfg_536_, 0);
v_srcDir_538_ = lean_ctor_get(v_cfg_536_, 1);
v_roots_539_ = lean_ctor_get(v_cfg_536_, 2);
v_globs_540_ = lean_ctor_get(v_cfg_536_, 3);
v_libName_541_ = lean_ctor_get(v_cfg_536_, 4);
v_libPrefixOnWindows_542_ = lean_ctor_get_uint8(v_cfg_536_, sizeof(void*)*9);
v_needs_543_ = lean_ctor_get(v_cfg_536_, 5);
v_extraDepTargets_544_ = lean_ctor_get(v_cfg_536_, 6);
v_defaultFacets_545_ = lean_ctor_get(v_cfg_536_, 7);
v_nativeFacets_546_ = lean_ctor_get(v_cfg_536_, 8);
v_allowImportAll_547_ = lean_ctor_get_uint8(v_cfg_536_, sizeof(void*)*9 + 2);
v_isSharedCheck_554_ = !lean_is_exclusive(v_cfg_536_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v_cfg_536_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_nativeFacets_546_);
lean_inc(v_defaultFacets_545_);
lean_inc(v_extraDepTargets_544_);
lean_inc(v_needs_543_);
lean_inc(v_libName_541_);
lean_inc(v_globs_540_);
lean_inc(v_roots_539_);
lean_inc(v_srcDir_538_);
lean_inc(v_toLeanConfig_537_);
lean_dec(v_cfg_536_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_toLeanConfig_537_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_srcDir_538_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_roots_539_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_globs_540_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_libName_541_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v_needs_543_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_extraDepTargets_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_defaultFacets_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_nativeFacets_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*9, v_libPrefixOnWindows_542_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*9 + 2, v_allowImportAll_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*9 + 1, v_val_535_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_555_, lean_object* v_cfg_556_){
_start:
{
uint8_t v_val_71__boxed_557_; lean_object* v_res_558_; 
v_val_71__boxed_557_ = lean_unbox(v_val_555_);
v_res_558_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__1(v_val_71__boxed_557_, v_cfg_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__2(lean_object* v_f_559_, lean_object* v_cfg_560_){
_start:
{
lean_object* v_toLeanConfig_561_; lean_object* v_srcDir_562_; lean_object* v_roots_563_; lean_object* v_globs_564_; lean_object* v_libName_565_; uint8_t v_libPrefixOnWindows_566_; lean_object* v_needs_567_; lean_object* v_extraDepTargets_568_; uint8_t v_precompileModules_569_; lean_object* v_defaultFacets_570_; lean_object* v_nativeFacets_571_; uint8_t v_allowImportAll_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_582_; 
v_toLeanConfig_561_ = lean_ctor_get(v_cfg_560_, 0);
v_srcDir_562_ = lean_ctor_get(v_cfg_560_, 1);
v_roots_563_ = lean_ctor_get(v_cfg_560_, 2);
v_globs_564_ = lean_ctor_get(v_cfg_560_, 3);
v_libName_565_ = lean_ctor_get(v_cfg_560_, 4);
v_libPrefixOnWindows_566_ = lean_ctor_get_uint8(v_cfg_560_, sizeof(void*)*9);
v_needs_567_ = lean_ctor_get(v_cfg_560_, 5);
v_extraDepTargets_568_ = lean_ctor_get(v_cfg_560_, 6);
v_precompileModules_569_ = lean_ctor_get_uint8(v_cfg_560_, sizeof(void*)*9 + 1);
v_defaultFacets_570_ = lean_ctor_get(v_cfg_560_, 7);
v_nativeFacets_571_ = lean_ctor_get(v_cfg_560_, 8);
v_allowImportAll_572_ = lean_ctor_get_uint8(v_cfg_560_, sizeof(void*)*9 + 2);
v_isSharedCheck_582_ = !lean_is_exclusive(v_cfg_560_);
if (v_isSharedCheck_582_ == 0)
{
v___x_574_ = v_cfg_560_;
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_nativeFacets_571_);
lean_inc(v_defaultFacets_570_);
lean_inc(v_extraDepTargets_568_);
lean_inc(v_needs_567_);
lean_inc(v_libName_565_);
lean_inc(v_globs_564_);
lean_inc(v_roots_563_);
lean_inc(v_srcDir_562_);
lean_inc(v_toLeanConfig_561_);
lean_dec(v_cfg_560_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_576_ = lean_box(v_precompileModules_569_);
v___x_577_ = lean_apply_1(v_f_559_, v___x_576_);
if (v_isShared_575_ == 0)
{
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_toLeanConfig_561_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_srcDir_562_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_roots_563_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_globs_564_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_libName_565_);
lean_ctor_set(v_reuseFailAlloc_581_, 5, v_needs_567_);
lean_ctor_set(v_reuseFailAlloc_581_, 6, v_extraDepTargets_568_);
lean_ctor_set(v_reuseFailAlloc_581_, 7, v_defaultFacets_570_);
lean_ctor_set(v_reuseFailAlloc_581_, 8, v_nativeFacets_571_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*9, v_libPrefixOnWindows_566_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
uint8_t v___x_580_; 
v___x_580_ = lean_unbox(v___x_577_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*9 + 1, v___x_580_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*9 + 2, v_allowImportAll_572_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object* v_name_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileModules___proj___closed__3));
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object* v_name_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_593_);
lean_dec(v_name_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object* v_name_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object* v_name_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_597_);
lean_dec(v_name_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(lean_object* v_cfg_599_){
_start:
{
lean_object* v_defaultFacets_600_; 
v_defaultFacets_600_ = lean_ctor_get(v_cfg_599_, 7);
lean_inc_ref(v_defaultFacets_600_);
return v_defaultFacets_600_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed(lean_object* v_cfg_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(v_cfg_601_);
lean_dec_ref(v_cfg_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__1(lean_object* v_val_603_, lean_object* v_cfg_604_){
_start:
{
lean_object* v_toLeanConfig_605_; lean_object* v_srcDir_606_; lean_object* v_roots_607_; lean_object* v_globs_608_; lean_object* v_libName_609_; uint8_t v_libPrefixOnWindows_610_; lean_object* v_needs_611_; lean_object* v_extraDepTargets_612_; uint8_t v_precompileModules_613_; lean_object* v_nativeFacets_614_; uint8_t v_allowImportAll_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_toLeanConfig_605_ = lean_ctor_get(v_cfg_604_, 0);
v_srcDir_606_ = lean_ctor_get(v_cfg_604_, 1);
v_roots_607_ = lean_ctor_get(v_cfg_604_, 2);
v_globs_608_ = lean_ctor_get(v_cfg_604_, 3);
v_libName_609_ = lean_ctor_get(v_cfg_604_, 4);
v_libPrefixOnWindows_610_ = lean_ctor_get_uint8(v_cfg_604_, sizeof(void*)*9);
v_needs_611_ = lean_ctor_get(v_cfg_604_, 5);
v_extraDepTargets_612_ = lean_ctor_get(v_cfg_604_, 6);
v_precompileModules_613_ = lean_ctor_get_uint8(v_cfg_604_, sizeof(void*)*9 + 1);
v_nativeFacets_614_ = lean_ctor_get(v_cfg_604_, 8);
v_allowImportAll_615_ = lean_ctor_get_uint8(v_cfg_604_, sizeof(void*)*9 + 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_cfg_604_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v_cfg_604_, 7);
lean_dec(v_unused_623_);
v___x_617_ = v_cfg_604_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_nativeFacets_614_);
lean_inc(v_extraDepTargets_612_);
lean_inc(v_needs_611_);
lean_inc(v_libName_609_);
lean_inc(v_globs_608_);
lean_inc(v_roots_607_);
lean_inc(v_srcDir_606_);
lean_inc(v_toLeanConfig_605_);
lean_dec(v_cfg_604_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 7, v_val_603_);
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_toLeanConfig_605_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_srcDir_606_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_roots_607_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_globs_608_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_libName_609_);
lean_ctor_set(v_reuseFailAlloc_621_, 5, v_needs_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 6, v_extraDepTargets_612_);
lean_ctor_set(v_reuseFailAlloc_621_, 7, v_val_603_);
lean_ctor_set(v_reuseFailAlloc_621_, 8, v_nativeFacets_614_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*9, v_libPrefixOnWindows_610_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*9 + 1, v_precompileModules_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*9 + 2, v_allowImportAll_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__2(lean_object* v_f_624_, lean_object* v_cfg_625_){
_start:
{
lean_object* v_toLeanConfig_626_; lean_object* v_srcDir_627_; lean_object* v_roots_628_; lean_object* v_globs_629_; lean_object* v_libName_630_; uint8_t v_libPrefixOnWindows_631_; lean_object* v_needs_632_; lean_object* v_extraDepTargets_633_; uint8_t v_precompileModules_634_; lean_object* v_defaultFacets_635_; lean_object* v_nativeFacets_636_; uint8_t v_allowImportAll_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_toLeanConfig_626_ = lean_ctor_get(v_cfg_625_, 0);
v_srcDir_627_ = lean_ctor_get(v_cfg_625_, 1);
v_roots_628_ = lean_ctor_get(v_cfg_625_, 2);
v_globs_629_ = lean_ctor_get(v_cfg_625_, 3);
v_libName_630_ = lean_ctor_get(v_cfg_625_, 4);
v_libPrefixOnWindows_631_ = lean_ctor_get_uint8(v_cfg_625_, sizeof(void*)*9);
v_needs_632_ = lean_ctor_get(v_cfg_625_, 5);
v_extraDepTargets_633_ = lean_ctor_get(v_cfg_625_, 6);
v_precompileModules_634_ = lean_ctor_get_uint8(v_cfg_625_, sizeof(void*)*9 + 1);
v_defaultFacets_635_ = lean_ctor_get(v_cfg_625_, 7);
v_nativeFacets_636_ = lean_ctor_get(v_cfg_625_, 8);
v_allowImportAll_637_ = lean_ctor_get_uint8(v_cfg_625_, sizeof(void*)*9 + 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_cfg_625_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v_cfg_625_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_nativeFacets_636_);
lean_inc(v_defaultFacets_635_);
lean_inc(v_extraDepTargets_633_);
lean_inc(v_needs_632_);
lean_inc(v_libName_630_);
lean_inc(v_globs_629_);
lean_inc(v_roots_628_);
lean_inc(v_srcDir_627_);
lean_inc(v_toLeanConfig_626_);
lean_dec(v_cfg_625_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_apply_1(v_f_624_, v_defaultFacets_635_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 7, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_toLeanConfig_626_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_srcDir_627_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_roots_628_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_globs_629_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_libName_630_);
lean_ctor_set(v_reuseFailAlloc_644_, 5, v_needs_632_);
lean_ctor_set(v_reuseFailAlloc_644_, 6, v_extraDepTargets_633_);
lean_ctor_set(v_reuseFailAlloc_644_, 7, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_644_, 8, v_nativeFacets_636_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*9, v_libPrefixOnWindows_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*9 + 1, v_precompileModules_634_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*9 + 2, v_allowImportAll_637_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
static lean_object* _init_l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = l_Lake_LeanLib_leanArtsFacet;
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_array_push(v___x_648_, v___x_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed(lean_object* v_x_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(v_x_652_);
lean_dec_ref(v_x_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object* v_name_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = ((lean_object*)(l_Lake_LeanLibConfig_defaultFacets___proj___closed__4));
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object* v_name_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_665_);
lean_dec(v_name_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object* v_name_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object* v_name_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_669_);
lean_dec(v_name_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(lean_object* v_cfg_671_, uint8_t v___y_672_){
_start:
{
lean_object* v_nativeFacets_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_nativeFacets_673_ = lean_ctor_get(v_cfg_671_, 8);
lean_inc_ref(v_nativeFacets_673_);
lean_dec_ref(v_cfg_671_);
v___x_674_ = lean_box(v___y_672_);
v___x_675_ = lean_apply_1(v_nativeFacets_673_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed(lean_object* v_cfg_676_, lean_object* v___y_677_){
_start:
{
uint8_t v___y_147__boxed_678_; lean_object* v_res_679_; 
v___y_147__boxed_678_ = lean_unbox(v___y_677_);
v_res_679_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(v_cfg_676_, v___y_147__boxed_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__1(lean_object* v_val_680_, lean_object* v_cfg_681_){
_start:
{
lean_object* v_toLeanConfig_682_; lean_object* v_srcDir_683_; lean_object* v_roots_684_; lean_object* v_globs_685_; lean_object* v_libName_686_; uint8_t v_libPrefixOnWindows_687_; lean_object* v_needs_688_; lean_object* v_extraDepTargets_689_; uint8_t v_precompileModules_690_; lean_object* v_defaultFacets_691_; uint8_t v_allowImportAll_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_toLeanConfig_682_ = lean_ctor_get(v_cfg_681_, 0);
v_srcDir_683_ = lean_ctor_get(v_cfg_681_, 1);
v_roots_684_ = lean_ctor_get(v_cfg_681_, 2);
v_globs_685_ = lean_ctor_get(v_cfg_681_, 3);
v_libName_686_ = lean_ctor_get(v_cfg_681_, 4);
v_libPrefixOnWindows_687_ = lean_ctor_get_uint8(v_cfg_681_, sizeof(void*)*9);
v_needs_688_ = lean_ctor_get(v_cfg_681_, 5);
v_extraDepTargets_689_ = lean_ctor_get(v_cfg_681_, 6);
v_precompileModules_690_ = lean_ctor_get_uint8(v_cfg_681_, sizeof(void*)*9 + 1);
v_defaultFacets_691_ = lean_ctor_get(v_cfg_681_, 7);
v_allowImportAll_692_ = lean_ctor_get_uint8(v_cfg_681_, sizeof(void*)*9 + 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_cfg_681_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_cfg_681_, 8);
lean_dec(v_unused_700_);
v___x_694_ = v_cfg_681_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_defaultFacets_691_);
lean_inc(v_extraDepTargets_689_);
lean_inc(v_needs_688_);
lean_inc(v_libName_686_);
lean_inc(v_globs_685_);
lean_inc(v_roots_684_);
lean_inc(v_srcDir_683_);
lean_inc(v_toLeanConfig_682_);
lean_dec(v_cfg_681_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 8, v_val_680_);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_toLeanConfig_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_srcDir_683_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_roots_684_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_globs_685_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_libName_686_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_needs_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_extraDepTargets_689_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_defaultFacets_691_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_val_680_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*9, v_libPrefixOnWindows_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*9 + 1, v_precompileModules_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*9 + 2, v_allowImportAll_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__2(lean_object* v_f_701_, lean_object* v_cfg_702_){
_start:
{
lean_object* v_toLeanConfig_703_; lean_object* v_srcDir_704_; lean_object* v_roots_705_; lean_object* v_globs_706_; lean_object* v_libName_707_; uint8_t v_libPrefixOnWindows_708_; lean_object* v_needs_709_; lean_object* v_extraDepTargets_710_; uint8_t v_precompileModules_711_; lean_object* v_defaultFacets_712_; lean_object* v_nativeFacets_713_; uint8_t v_allowImportAll_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_toLeanConfig_703_ = lean_ctor_get(v_cfg_702_, 0);
v_srcDir_704_ = lean_ctor_get(v_cfg_702_, 1);
v_roots_705_ = lean_ctor_get(v_cfg_702_, 2);
v_globs_706_ = lean_ctor_get(v_cfg_702_, 3);
v_libName_707_ = lean_ctor_get(v_cfg_702_, 4);
v_libPrefixOnWindows_708_ = lean_ctor_get_uint8(v_cfg_702_, sizeof(void*)*9);
v_needs_709_ = lean_ctor_get(v_cfg_702_, 5);
v_extraDepTargets_710_ = lean_ctor_get(v_cfg_702_, 6);
v_precompileModules_711_ = lean_ctor_get_uint8(v_cfg_702_, sizeof(void*)*9 + 1);
v_defaultFacets_712_ = lean_ctor_get(v_cfg_702_, 7);
v_nativeFacets_713_ = lean_ctor_get(v_cfg_702_, 8);
v_allowImportAll_714_ = lean_ctor_get_uint8(v_cfg_702_, sizeof(void*)*9 + 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_cfg_702_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v_cfg_702_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_nativeFacets_713_);
lean_inc(v_defaultFacets_712_);
lean_inc(v_extraDepTargets_710_);
lean_inc(v_needs_709_);
lean_inc(v_libName_707_);
lean_inc(v_globs_706_);
lean_inc(v_roots_705_);
lean_inc(v_srcDir_704_);
lean_inc(v_toLeanConfig_703_);
lean_dec(v_cfg_702_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_apply_1(v_f_701_, v_nativeFacets_713_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 8, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_toLeanConfig_703_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_srcDir_704_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_roots_705_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_globs_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_libName_707_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_needs_709_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_extraDepTargets_710_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v_defaultFacets_712_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v___x_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*9, v_libPrefixOnWindows_708_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*9 + 1, v_precompileModules_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*9 + 2, v_allowImportAll_714_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(lean_object* v_x_723_, uint8_t v___y_724_){
_start:
{
lean_object* v___y_726_; 
if (v___y_724_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = l_Lake_Module_oFacet;
v___y_726_ = v___x_730_;
goto v___jp_725_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = l_Lake_Module_oExportFacet;
v___y_726_ = v___x_731_;
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
lean_inc(v___y_726_);
v___x_729_ = lean_array_push(v___x_728_, v___y_726_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed(lean_object* v_x_732_, lean_object* v___y_733_){
_start:
{
uint8_t v___y_197__boxed_734_; lean_object* v_res_735_; 
v___y_197__boxed_734_ = lean_unbox(v___y_733_);
v_res_735_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(v_x_732_, v___y_197__boxed_734_);
lean_dec_ref(v_x_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object* v_name_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l_Lake_LeanLibConfig_nativeFacets___proj___closed__4));
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object* v_name_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_747_);
lean_dec(v_name_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object* v_name_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object* v_name_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_751_);
lean_dec(v_name_751_);
return v_res_752_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_753_){
_start:
{
uint8_t v_allowImportAll_754_; 
v_allowImportAll_754_ = lean_ctor_get_uint8(v_cfg_753_, sizeof(void*)*9 + 2);
return v_allowImportAll_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(v_cfg_755_);
lean_dec_ref(v_cfg_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(uint8_t v_val_758_, lean_object* v_cfg_759_){
_start:
{
lean_object* v_toLeanConfig_760_; lean_object* v_srcDir_761_; lean_object* v_roots_762_; lean_object* v_globs_763_; lean_object* v_libName_764_; uint8_t v_libPrefixOnWindows_765_; lean_object* v_needs_766_; lean_object* v_extraDepTargets_767_; uint8_t v_precompileModules_768_; lean_object* v_defaultFacets_769_; lean_object* v_nativeFacets_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_toLeanConfig_760_ = lean_ctor_get(v_cfg_759_, 0);
v_srcDir_761_ = lean_ctor_get(v_cfg_759_, 1);
v_roots_762_ = lean_ctor_get(v_cfg_759_, 2);
v_globs_763_ = lean_ctor_get(v_cfg_759_, 3);
v_libName_764_ = lean_ctor_get(v_cfg_759_, 4);
v_libPrefixOnWindows_765_ = lean_ctor_get_uint8(v_cfg_759_, sizeof(void*)*9);
v_needs_766_ = lean_ctor_get(v_cfg_759_, 5);
v_extraDepTargets_767_ = lean_ctor_get(v_cfg_759_, 6);
v_precompileModules_768_ = lean_ctor_get_uint8(v_cfg_759_, sizeof(void*)*9 + 1);
v_defaultFacets_769_ = lean_ctor_get(v_cfg_759_, 7);
v_nativeFacets_770_ = lean_ctor_get(v_cfg_759_, 8);
v_isSharedCheck_777_ = !lean_is_exclusive(v_cfg_759_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v_cfg_759_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_nativeFacets_770_);
lean_inc(v_defaultFacets_769_);
lean_inc(v_extraDepTargets_767_);
lean_inc(v_needs_766_);
lean_inc(v_libName_764_);
lean_inc(v_globs_763_);
lean_inc(v_roots_762_);
lean_inc(v_srcDir_761_);
lean_inc(v_toLeanConfig_760_);
lean_dec(v_cfg_759_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_toLeanConfig_760_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_srcDir_761_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_roots_762_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_globs_763_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_libName_764_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v_needs_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_extraDepTargets_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_defaultFacets_769_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v_nativeFacets_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, sizeof(void*)*9, v_libPrefixOnWindows_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, sizeof(void*)*9 + 1, v_precompileModules_768_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*9 + 2, v_val_758_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_778_, lean_object* v_cfg_779_){
_start:
{
uint8_t v_val_71__boxed_780_; lean_object* v_res_781_; 
v_val_71__boxed_780_ = lean_unbox(v_val_778_);
v_res_781_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(v_val_71__boxed_780_, v_cfg_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__2(lean_object* v_f_782_, lean_object* v_cfg_783_){
_start:
{
lean_object* v_toLeanConfig_784_; lean_object* v_srcDir_785_; lean_object* v_roots_786_; lean_object* v_globs_787_; lean_object* v_libName_788_; uint8_t v_libPrefixOnWindows_789_; lean_object* v_needs_790_; lean_object* v_extraDepTargets_791_; uint8_t v_precompileModules_792_; lean_object* v_defaultFacets_793_; lean_object* v_nativeFacets_794_; uint8_t v_allowImportAll_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_805_; 
v_toLeanConfig_784_ = lean_ctor_get(v_cfg_783_, 0);
v_srcDir_785_ = lean_ctor_get(v_cfg_783_, 1);
v_roots_786_ = lean_ctor_get(v_cfg_783_, 2);
v_globs_787_ = lean_ctor_get(v_cfg_783_, 3);
v_libName_788_ = lean_ctor_get(v_cfg_783_, 4);
v_libPrefixOnWindows_789_ = lean_ctor_get_uint8(v_cfg_783_, sizeof(void*)*9);
v_needs_790_ = lean_ctor_get(v_cfg_783_, 5);
v_extraDepTargets_791_ = lean_ctor_get(v_cfg_783_, 6);
v_precompileModules_792_ = lean_ctor_get_uint8(v_cfg_783_, sizeof(void*)*9 + 1);
v_defaultFacets_793_ = lean_ctor_get(v_cfg_783_, 7);
v_nativeFacets_794_ = lean_ctor_get(v_cfg_783_, 8);
v_allowImportAll_795_ = lean_ctor_get_uint8(v_cfg_783_, sizeof(void*)*9 + 2);
v_isSharedCheck_805_ = !lean_is_exclusive(v_cfg_783_);
if (v_isSharedCheck_805_ == 0)
{
v___x_797_ = v_cfg_783_;
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_nativeFacets_794_);
lean_inc(v_defaultFacets_793_);
lean_inc(v_extraDepTargets_791_);
lean_inc(v_needs_790_);
lean_inc(v_libName_788_);
lean_inc(v_globs_787_);
lean_inc(v_roots_786_);
lean_inc(v_srcDir_785_);
lean_inc(v_toLeanConfig_784_);
lean_dec(v_cfg_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_799_ = lean_box(v_allowImportAll_795_);
v___x_800_ = lean_apply_1(v_f_782_, v___x_799_);
if (v_isShared_798_ == 0)
{
v___x_802_ = v___x_797_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_toLeanConfig_784_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_srcDir_785_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_roots_786_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_globs_787_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_libName_788_);
lean_ctor_set(v_reuseFailAlloc_804_, 5, v_needs_790_);
lean_ctor_set(v_reuseFailAlloc_804_, 6, v_extraDepTargets_791_);
lean_ctor_set(v_reuseFailAlloc_804_, 7, v_defaultFacets_793_);
lean_ctor_set(v_reuseFailAlloc_804_, 8, v_nativeFacets_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*9, v_libPrefixOnWindows_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*9 + 1, v_precompileModules_792_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
uint8_t v___x_803_; 
v___x_803_ = lean_unbox(v___x_800_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*9 + 2, v___x_803_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object* v_name_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = ((lean_object*)(l_Lake_LeanLibConfig_allowImportAll___proj___closed__3));
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object* v_name_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_816_);
lean_dec(v_name_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object* v_name_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object* v_name_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_820_);
lean_dec(v_name_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_822_){
_start:
{
lean_object* v_toLeanConfig_823_; 
v_toLeanConfig_823_ = lean_ctor_get(v_cfg_822_, 0);
lean_inc_ref(v_toLeanConfig_823_);
return v_toLeanConfig_823_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(v_cfg_824_);
lean_dec_ref(v_cfg_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1(lean_object* v_val_826_, lean_object* v_cfg_827_){
_start:
{
lean_object* v_srcDir_828_; lean_object* v_roots_829_; lean_object* v_globs_830_; lean_object* v_libName_831_; uint8_t v_libPrefixOnWindows_832_; lean_object* v_needs_833_; lean_object* v_extraDepTargets_834_; uint8_t v_precompileModules_835_; lean_object* v_defaultFacets_836_; lean_object* v_nativeFacets_837_; uint8_t v_allowImportAll_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_srcDir_828_ = lean_ctor_get(v_cfg_827_, 1);
v_roots_829_ = lean_ctor_get(v_cfg_827_, 2);
v_globs_830_ = lean_ctor_get(v_cfg_827_, 3);
v_libName_831_ = lean_ctor_get(v_cfg_827_, 4);
v_libPrefixOnWindows_832_ = lean_ctor_get_uint8(v_cfg_827_, sizeof(void*)*9);
v_needs_833_ = lean_ctor_get(v_cfg_827_, 5);
v_extraDepTargets_834_ = lean_ctor_get(v_cfg_827_, 6);
v_precompileModules_835_ = lean_ctor_get_uint8(v_cfg_827_, sizeof(void*)*9 + 1);
v_defaultFacets_836_ = lean_ctor_get(v_cfg_827_, 7);
v_nativeFacets_837_ = lean_ctor_get(v_cfg_827_, 8);
v_allowImportAll_838_ = lean_ctor_get_uint8(v_cfg_827_, sizeof(void*)*9 + 2);
v_isSharedCheck_845_ = !lean_is_exclusive(v_cfg_827_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_cfg_827_, 0);
lean_dec(v_unused_846_);
v___x_840_ = v_cfg_827_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_nativeFacets_837_);
lean_inc(v_defaultFacets_836_);
lean_inc(v_extraDepTargets_834_);
lean_inc(v_needs_833_);
lean_inc(v_libName_831_);
lean_inc(v_globs_830_);
lean_inc(v_roots_829_);
lean_inc(v_srcDir_828_);
lean_dec(v_cfg_827_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_val_826_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_val_826_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_srcDir_828_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_roots_829_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_globs_830_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_libName_831_);
lean_ctor_set(v_reuseFailAlloc_844_, 5, v_needs_833_);
lean_ctor_set(v_reuseFailAlloc_844_, 6, v_extraDepTargets_834_);
lean_ctor_set(v_reuseFailAlloc_844_, 7, v_defaultFacets_836_);
lean_ctor_set(v_reuseFailAlloc_844_, 8, v_nativeFacets_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*9, v_libPrefixOnWindows_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*9 + 1, v_precompileModules_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*9 + 2, v_allowImportAll_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2(lean_object* v_f_847_, lean_object* v_cfg_848_){
_start:
{
lean_object* v_toLeanConfig_849_; lean_object* v_srcDir_850_; lean_object* v_roots_851_; lean_object* v_globs_852_; lean_object* v_libName_853_; uint8_t v_libPrefixOnWindows_854_; lean_object* v_needs_855_; lean_object* v_extraDepTargets_856_; uint8_t v_precompileModules_857_; lean_object* v_defaultFacets_858_; lean_object* v_nativeFacets_859_; uint8_t v_allowImportAll_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
v_toLeanConfig_849_ = lean_ctor_get(v_cfg_848_, 0);
v_srcDir_850_ = lean_ctor_get(v_cfg_848_, 1);
v_roots_851_ = lean_ctor_get(v_cfg_848_, 2);
v_globs_852_ = lean_ctor_get(v_cfg_848_, 3);
v_libName_853_ = lean_ctor_get(v_cfg_848_, 4);
v_libPrefixOnWindows_854_ = lean_ctor_get_uint8(v_cfg_848_, sizeof(void*)*9);
v_needs_855_ = lean_ctor_get(v_cfg_848_, 5);
v_extraDepTargets_856_ = lean_ctor_get(v_cfg_848_, 6);
v_precompileModules_857_ = lean_ctor_get_uint8(v_cfg_848_, sizeof(void*)*9 + 1);
v_defaultFacets_858_ = lean_ctor_get(v_cfg_848_, 7);
v_nativeFacets_859_ = lean_ctor_get(v_cfg_848_, 8);
v_allowImportAll_860_ = lean_ctor_get_uint8(v_cfg_848_, sizeof(void*)*9 + 2);
v_isSharedCheck_868_ = !lean_is_exclusive(v_cfg_848_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v_cfg_848_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_nativeFacets_859_);
lean_inc(v_defaultFacets_858_);
lean_inc(v_extraDepTargets_856_);
lean_inc(v_needs_855_);
lean_inc(v_libName_853_);
lean_inc(v_globs_852_);
lean_inc(v_roots_851_);
lean_inc(v_srcDir_850_);
lean_inc(v_toLeanConfig_849_);
lean_dec(v_cfg_848_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_apply_1(v_f_847_, v_toLeanConfig_849_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_srcDir_850_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_roots_851_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_globs_852_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_libName_853_);
lean_ctor_set(v_reuseFailAlloc_867_, 5, v_needs_855_);
lean_ctor_set(v_reuseFailAlloc_867_, 6, v_extraDepTargets_856_);
lean_ctor_set(v_reuseFailAlloc_867_, 7, v_defaultFacets_858_);
lean_ctor_set(v_reuseFailAlloc_867_, 8, v_nativeFacets_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*9, v_libPrefixOnWindows_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*9 + 1, v_precompileModules_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*9 + 2, v_allowImportAll_860_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1));
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(v_x_878_);
lean_dec_ref(v_x_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object* v_name_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4));
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object* v_name_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_891_);
lean_dec(v_name_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(lean_object* v_name_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_name_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(v_name_895_);
lean_dec(v_name_895_);
return v_res_896_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__3));
v___x_907_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__0));
v___x_908_ = lean_array_push(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__7));
v___x_917_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__4, &l_Lake_LeanLibConfig___fields___closed__4_once, _init_l_Lake_LeanLibConfig___fields___closed__4);
v___x_918_ = lean_array_push(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__11));
v___x_927_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__8, &l_Lake_LeanLibConfig___fields___closed__8_once, _init_l_Lake_LeanLibConfig___fields___closed__8);
v___x_928_ = lean_array_push(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__15));
v___x_937_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__12, &l_Lake_LeanLibConfig___fields___closed__12_once, _init_l_Lake_LeanLibConfig___fields___closed__12);
v___x_938_ = lean_array_push(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__19));
v___x_947_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__16, &l_Lake_LeanLibConfig___fields___closed__16_once, _init_l_Lake_LeanLibConfig___fields___closed__16);
v___x_948_ = lean_array_push(v___x_947_, v___x_946_);
return v___x_948_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__23));
v___x_957_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__20, &l_Lake_LeanLibConfig___fields___closed__20_once, _init_l_Lake_LeanLibConfig___fields___closed__20);
v___x_958_ = lean_array_push(v___x_957_, v___x_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__27));
v___x_967_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__24, &l_Lake_LeanLibConfig___fields___closed__24_once, _init_l_Lake_LeanLibConfig___fields___closed__24);
v___x_968_ = lean_array_push(v___x_967_, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__31));
v___x_977_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__28, &l_Lake_LeanLibConfig___fields___closed__28_once, _init_l_Lake_LeanLibConfig___fields___closed__28);
v___x_978_ = lean_array_push(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__35));
v___x_987_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__32, &l_Lake_LeanLibConfig___fields___closed__32_once, _init_l_Lake_LeanLibConfig___fields___closed__32);
v___x_988_ = lean_array_push(v___x_987_, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__39));
v___x_997_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__36, &l_Lake_LeanLibConfig___fields___closed__36_once, _init_l_Lake_LeanLibConfig___fields___closed__36);
v___x_998_ = lean_array_push(v___x_997_, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__43));
v___x_1007_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__40, &l_Lake_LeanLibConfig___fields___closed__40_once, _init_l_Lake_LeanLibConfig___fields___closed__40);
v___x_1008_ = lean_array_push(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = l_Lake_LeanConfig___fields;
v___x_1010_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__44, &l_Lake_LeanLibConfig___fields___closed__44_once, _init_l_Lake_LeanLibConfig___fields___closed__44);
v___x_1011_ = l_Array_append___redArg(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__49(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__48));
v___x_1020_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__45, &l_Lake_LeanLibConfig___fields___closed__45_once, _init_l_Lake_LeanLibConfig___fields___closed__45);
v___x_1021_ = lean_array_push(v___x_1020_, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__49, &l_Lake_LeanLibConfig___fields___closed__49_once, _init_l_Lake_LeanLibConfig___fields___closed__49);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields(lean_object* v_name_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lake_LeanLibConfig___fields;
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___boxed(lean_object* v_name_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lake_LeanLibConfig_instConfigFields(v_name_1025_);
lean_dec(v_name_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo___lam__0(lean_object* v_x1_1027_, lean_object* v_x2_1028_){
_start:
{
lean_object* v_name_1029_; lean_object* v___x_1030_; 
v_name_1029_ = lean_ctor_get(v_x2_1028_, 0);
lean_inc(v_name_1029_);
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1029_, v_x2_1028_, v_x1_1027_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l_Lake_LeanLibConfig___fields;
v___x_1032_ = lean_array_get_size(v___x_1031_);
return v___x_1032_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_nat_dec_lt(v___x_1053_, v___x_1052_);
return v___x_1054_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1057_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
return v___x_1057_;
}
}
static size_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_1058_; size_t v___x_1059_; 
v___x_1058_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1059_ = lean_usize_of_nat(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1060_ = lean_box(1);
v___x_1061_ = lean_usize_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__14, &l_Lake_LeanLibConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14);
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = l_Lake_LeanLibConfig___fields;
v___f_1064_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__12));
v___x_1065_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1065_, v___f_1064_, v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1067_ = l_Lake_LeanLibConfig___fields;
v___x_1072_ = lean_box(1);
v___x_1073_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__11, &l_Lake_LeanLibConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11);
if (v___x_1073_ == 0)
{
v___y_1069_ = v___x_1072_;
goto v___jp_1068_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__13, &l_Lake_LeanLibConfig_instConfigInfo___closed__13_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13);
if (v___x_1074_ == 0)
{
if (v___x_1073_ == 0)
{
v___y_1069_ = v___x_1072_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1069_ = v___x_1075_;
goto v___jp_1068_;
}
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1069_ = v___x_1076_;
goto v___jp_1068_;
}
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_1069_);
v___x_1071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1067_);
lean_ctor_set(v___x_1071_, 1, v___y_1069_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__0(lean_object* v_x_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__1(uint8_t v_shouldExport_1079_){
_start:
{
lean_object* v___y_1081_; 
if (v_shouldExport_1079_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lake_Module_oFacet;
v___y_1081_ = v___x_1085_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lake_Module_oExportFacet;
v___y_1081_ = v___x_1086_;
goto v___jp_1080_;
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = lean_mk_empty_array_with_capacity(v___x_1082_);
lean_inc(v___y_1081_);
v___x_1084_ = lean_array_push(v___x_1083_, v___y_1081_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__1___boxed(lean_object* v_shouldExport_1087_){
_start:
{
uint8_t v_shouldExport_boxed_1088_; lean_object* v_res_1089_; 
v_shouldExport_boxed_1088_ = lean_unbox(v_shouldExport_1087_);
v_res_1089_ = l_Lake_LeanLibConfig_instEmptyCollection___lam__1(v_shouldExport_boxed_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection(lean_object* v_name_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; size_t v_sz_1102_; size_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___f_1093_ = ((lean_object*)(l_Lake_LeanLibConfig_instEmptyCollection___closed__0));
v___f_1094_ = ((lean_object*)(l_Lake_LeanLibConfig_instEmptyCollection___closed__1));
v___x_1095_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_1096_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_1097_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___lam__3___closed__0));
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_mk_empty_array_with_capacity(v___x_1098_);
v___x_1100_ = lean_array_push(v___x_1099_, v_name_1092_);
v___x_1101_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v_sz_1102_ = lean_array_size(v___x_1100_);
v___x_1103_ = ((size_t)0ULL);
lean_inc_ref(v___x_1100_);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1101_, v___f_1093_, v_sz_1102_, v___x_1103_, v___x_1100_);
v___x_1105_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_1106_ = 0;
v___x_1107_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___closed__0);
v___x_1108_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_1108_, 0, v___x_1096_);
lean_ctor_set(v___x_1108_, 1, v___x_1097_);
lean_ctor_set(v___x_1108_, 2, v___x_1100_);
lean_ctor_set(v___x_1108_, 3, v___x_1104_);
lean_ctor_set(v___x_1108_, 4, v___x_1105_);
lean_ctor_set(v___x_1108_, 5, v___x_1095_);
lean_ctor_set(v___x_1108_, 6, v___x_1095_);
lean_ctor_set(v___x_1108_, 7, v___x_1107_);
lean_ctor_set(v___x_1108_, 8, v___f_1094_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*9, v___x_1106_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*9 + 1, v___x_1106_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*9 + 2, v___x_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg(lean_object* v_n_1109_){
_start:
{
lean_inc(v_n_1109_);
return v_n_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg___boxed(lean_object* v_n_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lake_LeanLibConfig_name___redArg(v_n_1110_);
lean_dec(v_n_1110_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name(lean_object* v_n_1112_, lean_object* v_x_1113_){
_start:
{
lean_inc(v_n_1112_);
return v_n_1112_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___boxed(lean_object* v_n_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lake_LeanLibConfig_name(v_n_1114_, v_x_1115_);
lean_dec_ref(v_x_1115_);
lean_dec(v_n_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(lean_object* v_mod_1117_, lean_object* v_as_1118_, size_t v_i_1119_, size_t v_stop_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_eq(v_i_1119_, v_stop_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_array_uget_borrowed(v_as_1118_, v_i_1119_);
v___x_1123_ = l_Lake_Glob_matches(v_mod_1117_, v___x_1122_);
if (v___x_1123_ == 0)
{
size_t v___x_1124_; size_t v___x_1125_; 
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1119_, v___x_1124_);
v_i_1119_ = v___x_1125_;
goto _start;
}
else
{
return v___x_1123_;
}
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = 0;
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(lean_object* v_mod_1128_, lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_stop_1131_){
_start:
{
size_t v_i_boxed_1132_; size_t v_stop_boxed_1133_; uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_i_boxed_1132_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_stop_boxed_1133_ = lean_unbox_usize(v_stop_1131_);
lean_dec(v_stop_1131_);
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1128_, v_as_1129_, v_i_boxed_1132_, v_stop_boxed_1133_);
lean_dec_ref(v_as_1129_);
lean_dec(v_mod_1128_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(lean_object* v_mod_1136_, lean_object* v_as_1137_, size_t v_i_1138_, size_t v_stop_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_eq(v_i_1138_, v_stop_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_array_uget_borrowed(v_as_1137_, v_i_1138_);
v___x_1142_ = l_Lean_Name_isPrefixOf(v___x_1141_, v_mod_1136_);
if (v___x_1142_ == 0)
{
size_t v___x_1143_; size_t v___x_1144_; 
v___x_1143_ = ((size_t)1ULL);
v___x_1144_ = lean_usize_add(v_i_1138_, v___x_1143_);
v_i_1138_ = v___x_1144_;
goto _start;
}
else
{
return v___x_1142_;
}
}
else
{
uint8_t v___x_1146_; 
v___x_1146_ = 0;
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(lean_object* v_mod_1147_, lean_object* v_as_1148_, lean_object* v_i_1149_, lean_object* v_stop_1150_){
_start:
{
size_t v_i_boxed_1151_; size_t v_stop_boxed_1152_; uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_i_boxed_1151_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_stop_boxed_1152_ = lean_unbox_usize(v_stop_1150_);
lean_dec(v_stop_1150_);
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1147_, v_as_1148_, v_i_boxed_1151_, v_stop_boxed_1152_);
lean_dec_ref(v_as_1148_);
lean_dec(v_mod_1147_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object* v_mod_1155_, lean_object* v_self_1156_){
_start:
{
lean_object* v_roots_1157_; lean_object* v_globs_1158_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_roots_1157_ = lean_ctor_get(v_self_1156_, 2);
v_globs_1158_ = lean_ctor_get(v_self_1156_, 3);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_array_get_size(v_roots_1157_);
v___x_1168_ = lean_nat_dec_lt(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
goto v___jp_1159_;
}
else
{
if (v___x_1168_ == 0)
{
goto v___jp_1159_;
}
else
{
size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = lean_usize_of_nat(v___x_1167_);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1155_, v_roots_1157_, v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
goto v___jp_1159_;
}
else
{
return v___x_1171_;
}
}
}
v___jp_1159_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_array_get_size(v_globs_1158_);
v___x_1162_ = lean_nat_dec_lt(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
return v___x_1162_;
}
else
{
if (v___x_1162_ == 0)
{
return v___x_1162_;
}
else
{
size_t v___x_1163_; size_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = ((size_t)0ULL);
v___x_1164_ = lean_usize_of_nat(v___x_1161_);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1155_, v_globs_1158_, v___x_1163_, v___x_1164_);
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(lean_object* v_mod_1172_, lean_object* v_self_1173_){
_start:
{
uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_res_1174_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1172_, v_self_1173_);
lean_dec_ref(v_self_1173_);
lean_dec(v_mod_1172_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object* v_n_1176_, lean_object* v_mod_1177_, lean_object* v_self_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1177_, v_self_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___boxed(lean_object* v_n_1180_, lean_object* v_mod_1181_, lean_object* v_self_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Lake_LeanLibConfig_isLocalModule(v_n_1180_, v_mod_1181_, v_self_1182_);
lean_dec_ref(v_self_1182_);
lean_dec(v_mod_1181_);
lean_dec(v_n_1180_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(lean_object* v_mod_1185_, lean_object* v_self_1186_, lean_object* v_as_1187_, size_t v_i_1188_, size_t v_stop_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_eq(v_i_1188_, v_stop_1189_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; uint8_t v___y_1193_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1191_ = 1;
v___x_1197_ = lean_array_uget_borrowed(v_as_1187_, v_i_1188_);
v___x_1198_ = l_Lean_Name_isPrefixOf(v___x_1197_, v_mod_1185_);
if (v___x_1198_ == 0)
{
v___y_1193_ = v___x_1198_;
goto v___jp_1192_;
}
else
{
lean_object* v_globs_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_globs_1199_ = lean_ctor_get(v_self_1186_, 3);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_array_get_size(v_globs_1199_);
v___x_1202_ = lean_nat_dec_lt(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
v___y_1193_ = v___x_1190_;
goto v___jp_1192_;
}
else
{
if (v___x_1202_ == 0)
{
v___y_1193_ = v___x_1190_;
goto v___jp_1192_;
}
else
{
size_t v___x_1203_; size_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = lean_usize_of_nat(v___x_1201_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v___x_1197_, v_globs_1199_, v___x_1203_, v___x_1204_);
v___y_1193_ = v___x_1205_;
goto v___jp_1192_;
}
}
}
v___jp_1192_:
{
if (v___y_1193_ == 0)
{
size_t v___x_1194_; size_t v___x_1195_; 
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1188_, v___x_1194_);
v_i_1188_ = v___x_1195_;
goto _start;
}
else
{
return v___x_1191_;
}
}
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = 0;
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(lean_object* v_mod_1207_, lean_object* v_self_1208_, lean_object* v_as_1209_, lean_object* v_i_1210_, lean_object* v_stop_1211_){
_start:
{
size_t v_i_boxed_1212_; size_t v_stop_boxed_1213_; uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_i_boxed_1212_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_stop_boxed_1213_ = lean_unbox_usize(v_stop_1211_);
lean_dec(v_stop_1211_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1207_, v_self_1208_, v_as_1209_, v_i_boxed_1212_, v_stop_boxed_1213_);
lean_dec_ref(v_as_1209_);
lean_dec_ref(v_self_1208_);
lean_dec(v_mod_1207_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object* v_mod_1216_, lean_object* v_self_1217_){
_start:
{
lean_object* v_roots_1218_; lean_object* v_globs_1219_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_roots_1218_ = lean_ctor_get(v_self_1217_, 2);
v_globs_1219_ = lean_ctor_get(v_self_1217_, 3);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_array_get_size(v_globs_1219_);
v___x_1229_ = lean_nat_dec_lt(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
goto v___jp_1220_;
}
else
{
if (v___x_1229_ == 0)
{
goto v___jp_1220_;
}
else
{
size_t v___x_1230_; size_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = ((size_t)0ULL);
v___x_1231_ = lean_usize_of_nat(v___x_1228_);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1216_, v_globs_1219_, v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
goto v___jp_1220_;
}
else
{
return v___x_1232_;
}
}
}
v___jp_1220_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_array_get_size(v_roots_1218_);
v___x_1223_ = lean_nat_dec_lt(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
return v___x_1223_;
}
else
{
if (v___x_1223_ == 0)
{
return v___x_1223_;
}
else
{
size_t v___x_1224_; size_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = ((size_t)0ULL);
v___x_1225_ = lean_usize_of_nat(v___x_1222_);
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1216_, v_self_1217_, v_roots_1218_, v___x_1224_, v___x_1225_);
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(lean_object* v_mod_1233_, lean_object* v_self_1234_){
_start:
{
uint8_t v_res_1235_; lean_object* v_r_1236_; 
v_res_1235_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1233_, v_self_1234_);
lean_dec_ref(v_self_1234_);
lean_dec(v_mod_1233_);
v_r_1236_ = lean_box(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object* v_n_1237_, lean_object* v_mod_1238_, lean_object* v_self_1239_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1238_, v_self_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___boxed(lean_object* v_n_1241_, lean_object* v_mod_1242_, lean_object* v_self_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_1241_, v_mod_1242_, v_self_1243_);
lean_dec_ref(v_self_1243_);
lean_dec(v_mod_1242_);
lean_dec(v_n_1241_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
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
