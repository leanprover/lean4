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
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_oFacet;
extern lean_object* l_Lake_Module_oExportFacet;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instInhabitedLeanLibConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedLeanLibConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__1_value;
static const lean_string_object l_Lake_instInhabitedLeanLibConfig_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__2_value;
static const lean_array_object l_Lake_instInhabitedLeanLibConfig_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedLeanLibConfig_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedLeanLibConfig_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanLibConfig_default___closed__4;
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
static lean_object* _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = l_Lake_LeanLib_leanArtsFacet;
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
v___x_38_ = lean_array_push(v___x_37_, v___x_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default(lean_object* v_name_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; size_t v_sz_46_; size_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___f_40_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_41_ = l_Lake_instInhabitedLeanConfig_default;
v___x_42_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_45_ = lean_array_push(v___x_44_, v_name_39_);
v_sz_46_ = lean_array_size(v___x_45_);
v___x_47_ = ((size_t)0ULL);
lean_inc_ref(v___x_45_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_46_, v___x_47_, v___x_45_);
v___x_49_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_50_ = 0;
v___x_51_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
v___x_52_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
v___x_53_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_53_, 0, v___x_41_);
lean_ctor_set(v___x_53_, 1, v___x_42_);
lean_ctor_set(v___x_53_, 2, v___x_45_);
lean_ctor_set(v___x_53_, 3, v___x_48_);
lean_ctor_set(v___x_53_, 4, v___x_49_);
lean_ctor_set(v___x_53_, 5, v___x_51_);
lean_ctor_set(v___x_53_, 6, v___x_51_);
lean_ctor_set(v___x_53_, 7, v___x_52_);
lean_ctor_set(v___x_53_, 8, v___f_40_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*9, v___x_50_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*9 + 1, v___x_50_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*9 + 2, v___x_50_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig(lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lake_instInhabitedLeanLibConfig_default(v_a_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0(lean_object* v_cfg_56_){
_start:
{
lean_object* v_srcDir_57_; 
v_srcDir_57_ = lean_ctor_get(v_cfg_56_, 1);
lean_inc_ref(v_srcDir_57_);
return v_srcDir_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_LeanLibConfig_srcDir___proj___lam__0(v_cfg_58_);
lean_dec_ref(v_cfg_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__1(lean_object* v_val_60_, lean_object* v_cfg_61_){
_start:
{
lean_object* v_toLeanConfig_62_; lean_object* v_roots_63_; lean_object* v_globs_64_; lean_object* v_libName_65_; uint8_t v_libPrefixOnWindows_66_; lean_object* v_needs_67_; lean_object* v_extraDepTargets_68_; uint8_t v_precompileModules_69_; lean_object* v_defaultFacets_70_; lean_object* v_nativeFacets_71_; uint8_t v_allowImportAll_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_toLeanConfig_62_ = lean_ctor_get(v_cfg_61_, 0);
v_roots_63_ = lean_ctor_get(v_cfg_61_, 2);
v_globs_64_ = lean_ctor_get(v_cfg_61_, 3);
v_libName_65_ = lean_ctor_get(v_cfg_61_, 4);
v_libPrefixOnWindows_66_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9);
v_needs_67_ = lean_ctor_get(v_cfg_61_, 5);
v_extraDepTargets_68_ = lean_ctor_get(v_cfg_61_, 6);
v_precompileModules_69_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9 + 1);
v_defaultFacets_70_ = lean_ctor_get(v_cfg_61_, 7);
v_nativeFacets_71_ = lean_ctor_get(v_cfg_61_, 8);
v_allowImportAll_72_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9 + 2);
v_isSharedCheck_79_ = !lean_is_exclusive(v_cfg_61_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_cfg_61_, 1);
lean_dec(v_unused_80_);
v___x_74_ = v_cfg_61_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_nativeFacets_71_);
lean_inc(v_defaultFacets_70_);
lean_inc(v_extraDepTargets_68_);
lean_inc(v_needs_67_);
lean_inc(v_libName_65_);
lean_inc(v_globs_64_);
lean_inc(v_roots_63_);
lean_inc(v_toLeanConfig_62_);
lean_dec(v_cfg_61_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v_val_60_);
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_toLeanConfig_62_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_val_60_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v_roots_63_);
lean_ctor_set(v_reuseFailAlloc_78_, 3, v_globs_64_);
lean_ctor_set(v_reuseFailAlloc_78_, 4, v_libName_65_);
lean_ctor_set(v_reuseFailAlloc_78_, 5, v_needs_67_);
lean_ctor_set(v_reuseFailAlloc_78_, 6, v_extraDepTargets_68_);
lean_ctor_set(v_reuseFailAlloc_78_, 7, v_defaultFacets_70_);
lean_ctor_set(v_reuseFailAlloc_78_, 8, v_nativeFacets_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_78_, sizeof(void*)*9, v_libPrefixOnWindows_66_);
lean_ctor_set_uint8(v_reuseFailAlloc_78_, sizeof(void*)*9 + 1, v_precompileModules_69_);
lean_ctor_set_uint8(v_reuseFailAlloc_78_, sizeof(void*)*9 + 2, v_allowImportAll_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__2(lean_object* v_f_81_, lean_object* v_cfg_82_){
_start:
{
lean_object* v_toLeanConfig_83_; lean_object* v_srcDir_84_; lean_object* v_roots_85_; lean_object* v_globs_86_; lean_object* v_libName_87_; uint8_t v_libPrefixOnWindows_88_; lean_object* v_needs_89_; lean_object* v_extraDepTargets_90_; uint8_t v_precompileModules_91_; lean_object* v_defaultFacets_92_; lean_object* v_nativeFacets_93_; uint8_t v_allowImportAll_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_102_; 
v_toLeanConfig_83_ = lean_ctor_get(v_cfg_82_, 0);
v_srcDir_84_ = lean_ctor_get(v_cfg_82_, 1);
v_roots_85_ = lean_ctor_get(v_cfg_82_, 2);
v_globs_86_ = lean_ctor_get(v_cfg_82_, 3);
v_libName_87_ = lean_ctor_get(v_cfg_82_, 4);
v_libPrefixOnWindows_88_ = lean_ctor_get_uint8(v_cfg_82_, sizeof(void*)*9);
v_needs_89_ = lean_ctor_get(v_cfg_82_, 5);
v_extraDepTargets_90_ = lean_ctor_get(v_cfg_82_, 6);
v_precompileModules_91_ = lean_ctor_get_uint8(v_cfg_82_, sizeof(void*)*9 + 1);
v_defaultFacets_92_ = lean_ctor_get(v_cfg_82_, 7);
v_nativeFacets_93_ = lean_ctor_get(v_cfg_82_, 8);
v_allowImportAll_94_ = lean_ctor_get_uint8(v_cfg_82_, sizeof(void*)*9 + 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_cfg_82_);
if (v_isSharedCheck_102_ == 0)
{
v___x_96_ = v_cfg_82_;
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_nativeFacets_93_);
lean_inc(v_defaultFacets_92_);
lean_inc(v_extraDepTargets_90_);
lean_inc(v_needs_89_);
lean_inc(v_libName_87_);
lean_inc(v_globs_86_);
lean_inc(v_roots_85_);
lean_inc(v_srcDir_84_);
lean_inc(v_toLeanConfig_83_);
lean_dec(v_cfg_82_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_apply_1(v_f_81_, v_srcDir_84_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_98_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_toLeanConfig_83_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_roots_85_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_globs_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v_libName_87_);
lean_ctor_set(v_reuseFailAlloc_101_, 5, v_needs_89_);
lean_ctor_set(v_reuseFailAlloc_101_, 6, v_extraDepTargets_90_);
lean_ctor_set(v_reuseFailAlloc_101_, 7, v_defaultFacets_92_);
lean_ctor_set(v_reuseFailAlloc_101_, 8, v_nativeFacets_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*9, v_libPrefixOnWindows_88_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*9 + 1, v_precompileModules_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*9 + 2, v_allowImportAll_94_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3(lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lake_LeanLibConfig_srcDir___proj___lam__3(v_x_105_);
lean_dec_ref(v_x_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object* v_name_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___closed__4));
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object* v_name_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_118_);
lean_dec(v_name_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object* v_name_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object* v_name_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_122_);
lean_dec(v_name_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object* v_cfg_124_){
_start:
{
lean_object* v_roots_125_; 
v_roots_125_ = lean_ctor_get(v_cfg_124_, 2);
lean_inc_ref(v_roots_125_);
return v_roots_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object* v_cfg_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_126_);
lean_dec_ref(v_cfg_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object* v_val_128_, lean_object* v_cfg_129_){
_start:
{
lean_object* v_toLeanConfig_130_; lean_object* v_srcDir_131_; lean_object* v_globs_132_; lean_object* v_libName_133_; uint8_t v_libPrefixOnWindows_134_; lean_object* v_needs_135_; lean_object* v_extraDepTargets_136_; uint8_t v_precompileModules_137_; lean_object* v_defaultFacets_138_; lean_object* v_nativeFacets_139_; uint8_t v_allowImportAll_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_toLeanConfig_130_ = lean_ctor_get(v_cfg_129_, 0);
v_srcDir_131_ = lean_ctor_get(v_cfg_129_, 1);
v_globs_132_ = lean_ctor_get(v_cfg_129_, 3);
v_libName_133_ = lean_ctor_get(v_cfg_129_, 4);
v_libPrefixOnWindows_134_ = lean_ctor_get_uint8(v_cfg_129_, sizeof(void*)*9);
v_needs_135_ = lean_ctor_get(v_cfg_129_, 5);
v_extraDepTargets_136_ = lean_ctor_get(v_cfg_129_, 6);
v_precompileModules_137_ = lean_ctor_get_uint8(v_cfg_129_, sizeof(void*)*9 + 1);
v_defaultFacets_138_ = lean_ctor_get(v_cfg_129_, 7);
v_nativeFacets_139_ = lean_ctor_get(v_cfg_129_, 8);
v_allowImportAll_140_ = lean_ctor_get_uint8(v_cfg_129_, sizeof(void*)*9 + 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_cfg_129_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v_cfg_129_, 2);
lean_dec(v_unused_148_);
v___x_142_ = v_cfg_129_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_nativeFacets_139_);
lean_inc(v_defaultFacets_138_);
lean_inc(v_extraDepTargets_136_);
lean_inc(v_needs_135_);
lean_inc(v_libName_133_);
lean_inc(v_globs_132_);
lean_inc(v_srcDir_131_);
lean_inc(v_toLeanConfig_130_);
lean_dec(v_cfg_129_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 2, v_val_128_);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_toLeanConfig_130_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_srcDir_131_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_val_128_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_globs_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_libName_133_);
lean_ctor_set(v_reuseFailAlloc_146_, 5, v_needs_135_);
lean_ctor_set(v_reuseFailAlloc_146_, 6, v_extraDepTargets_136_);
lean_ctor_set(v_reuseFailAlloc_146_, 7, v_defaultFacets_138_);
lean_ctor_set(v_reuseFailAlloc_146_, 8, v_nativeFacets_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_146_, sizeof(void*)*9, v_libPrefixOnWindows_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_146_, sizeof(void*)*9 + 1, v_precompileModules_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_146_, sizeof(void*)*9 + 2, v_allowImportAll_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object* v_f_149_, lean_object* v_cfg_150_){
_start:
{
lean_object* v_toLeanConfig_151_; lean_object* v_srcDir_152_; lean_object* v_roots_153_; lean_object* v_globs_154_; lean_object* v_libName_155_; uint8_t v_libPrefixOnWindows_156_; lean_object* v_needs_157_; lean_object* v_extraDepTargets_158_; uint8_t v_precompileModules_159_; lean_object* v_defaultFacets_160_; lean_object* v_nativeFacets_161_; uint8_t v_allowImportAll_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_170_; 
v_toLeanConfig_151_ = lean_ctor_get(v_cfg_150_, 0);
v_srcDir_152_ = lean_ctor_get(v_cfg_150_, 1);
v_roots_153_ = lean_ctor_get(v_cfg_150_, 2);
v_globs_154_ = lean_ctor_get(v_cfg_150_, 3);
v_libName_155_ = lean_ctor_get(v_cfg_150_, 4);
v_libPrefixOnWindows_156_ = lean_ctor_get_uint8(v_cfg_150_, sizeof(void*)*9);
v_needs_157_ = lean_ctor_get(v_cfg_150_, 5);
v_extraDepTargets_158_ = lean_ctor_get(v_cfg_150_, 6);
v_precompileModules_159_ = lean_ctor_get_uint8(v_cfg_150_, sizeof(void*)*9 + 1);
v_defaultFacets_160_ = lean_ctor_get(v_cfg_150_, 7);
v_nativeFacets_161_ = lean_ctor_get(v_cfg_150_, 8);
v_allowImportAll_162_ = lean_ctor_get_uint8(v_cfg_150_, sizeof(void*)*9 + 2);
v_isSharedCheck_170_ = !lean_is_exclusive(v_cfg_150_);
if (v_isSharedCheck_170_ == 0)
{
v___x_164_ = v_cfg_150_;
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_nativeFacets_161_);
lean_inc(v_defaultFacets_160_);
lean_inc(v_extraDepTargets_158_);
lean_inc(v_needs_157_);
lean_inc(v_libName_155_);
lean_inc(v_globs_154_);
lean_inc(v_roots_153_);
lean_inc(v_srcDir_152_);
lean_inc(v_toLeanConfig_151_);
lean_dec(v_cfg_150_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_apply_1(v_f_149_, v_roots_153_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 2, v___x_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_toLeanConfig_151_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_srcDir_152_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_globs_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_libName_155_);
lean_ctor_set(v_reuseFailAlloc_169_, 5, v_needs_157_);
lean_ctor_set(v_reuseFailAlloc_169_, 6, v_extraDepTargets_158_);
lean_ctor_set(v_reuseFailAlloc_169_, 7, v_defaultFacets_160_);
lean_ctor_set(v_reuseFailAlloc_169_, 8, v_nativeFacets_161_);
lean_ctor_set_uint8(v_reuseFailAlloc_169_, sizeof(void*)*9, v_libPrefixOnWindows_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_169_, sizeof(void*)*9 + 1, v_precompileModules_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_169_, sizeof(void*)*9 + 2, v_allowImportAll_162_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object* v_name_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_array_push(v___x_174_, v_name_171_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object* v_name_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_176_, v_x_177_);
lean_dec_ref(v_x_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object* v_name_182_){
_start:
{
lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___x_187_; 
v___f_183_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__0));
v___f_184_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__1));
v___f_185_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__2));
v___f_186_ = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_roots___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_186_, 0, v_name_182_);
v___x_187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_187_, 0, v___f_183_);
lean_ctor_set(v___x_187_, 1, v___f_184_);
lean_ctor_set(v___x_187_, 2, v___f_185_);
lean_ctor_set(v___x_187_, 3, v___f_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object* v_name_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lake_LeanLibConfig_roots___proj(v_name_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0(lean_object* v_cfg_190_){
_start:
{
lean_object* v_globs_191_; 
v_globs_191_ = lean_ctor_get(v_cfg_190_, 3);
lean_inc_ref(v_globs_191_);
return v_globs_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0___boxed(lean_object* v_cfg_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lake_LeanLibConfig_globs___proj___lam__0(v_cfg_192_);
lean_dec_ref(v_cfg_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__1(lean_object* v_val_194_, lean_object* v_cfg_195_){
_start:
{
lean_object* v_toLeanConfig_196_; lean_object* v_srcDir_197_; lean_object* v_roots_198_; lean_object* v_libName_199_; uint8_t v_libPrefixOnWindows_200_; lean_object* v_needs_201_; lean_object* v_extraDepTargets_202_; uint8_t v_precompileModules_203_; lean_object* v_defaultFacets_204_; lean_object* v_nativeFacets_205_; uint8_t v_allowImportAll_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_toLeanConfig_196_ = lean_ctor_get(v_cfg_195_, 0);
v_srcDir_197_ = lean_ctor_get(v_cfg_195_, 1);
v_roots_198_ = lean_ctor_get(v_cfg_195_, 2);
v_libName_199_ = lean_ctor_get(v_cfg_195_, 4);
v_libPrefixOnWindows_200_ = lean_ctor_get_uint8(v_cfg_195_, sizeof(void*)*9);
v_needs_201_ = lean_ctor_get(v_cfg_195_, 5);
v_extraDepTargets_202_ = lean_ctor_get(v_cfg_195_, 6);
v_precompileModules_203_ = lean_ctor_get_uint8(v_cfg_195_, sizeof(void*)*9 + 1);
v_defaultFacets_204_ = lean_ctor_get(v_cfg_195_, 7);
v_nativeFacets_205_ = lean_ctor_get(v_cfg_195_, 8);
v_allowImportAll_206_ = lean_ctor_get_uint8(v_cfg_195_, sizeof(void*)*9 + 2);
v_isSharedCheck_213_ = !lean_is_exclusive(v_cfg_195_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_cfg_195_, 3);
lean_dec(v_unused_214_);
v___x_208_ = v_cfg_195_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_nativeFacets_205_);
lean_inc(v_defaultFacets_204_);
lean_inc(v_extraDepTargets_202_);
lean_inc(v_needs_201_);
lean_inc(v_libName_199_);
lean_inc(v_roots_198_);
lean_inc(v_srcDir_197_);
lean_inc(v_toLeanConfig_196_);
lean_dec(v_cfg_195_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 3, v_val_194_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_toLeanConfig_196_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_srcDir_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_roots_198_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_val_194_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_libName_199_);
lean_ctor_set(v_reuseFailAlloc_212_, 5, v_needs_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 6, v_extraDepTargets_202_);
lean_ctor_set(v_reuseFailAlloc_212_, 7, v_defaultFacets_204_);
lean_ctor_set(v_reuseFailAlloc_212_, 8, v_nativeFacets_205_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*9, v_libPrefixOnWindows_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*9 + 1, v_precompileModules_203_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*9 + 2, v_allowImportAll_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__2(lean_object* v_f_215_, lean_object* v_cfg_216_){
_start:
{
lean_object* v_toLeanConfig_217_; lean_object* v_srcDir_218_; lean_object* v_roots_219_; lean_object* v_globs_220_; lean_object* v_libName_221_; uint8_t v_libPrefixOnWindows_222_; lean_object* v_needs_223_; lean_object* v_extraDepTargets_224_; uint8_t v_precompileModules_225_; lean_object* v_defaultFacets_226_; lean_object* v_nativeFacets_227_; uint8_t v_allowImportAll_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_toLeanConfig_217_ = lean_ctor_get(v_cfg_216_, 0);
v_srcDir_218_ = lean_ctor_get(v_cfg_216_, 1);
v_roots_219_ = lean_ctor_get(v_cfg_216_, 2);
v_globs_220_ = lean_ctor_get(v_cfg_216_, 3);
v_libName_221_ = lean_ctor_get(v_cfg_216_, 4);
v_libPrefixOnWindows_222_ = lean_ctor_get_uint8(v_cfg_216_, sizeof(void*)*9);
v_needs_223_ = lean_ctor_get(v_cfg_216_, 5);
v_extraDepTargets_224_ = lean_ctor_get(v_cfg_216_, 6);
v_precompileModules_225_ = lean_ctor_get_uint8(v_cfg_216_, sizeof(void*)*9 + 1);
v_defaultFacets_226_ = lean_ctor_get(v_cfg_216_, 7);
v_nativeFacets_227_ = lean_ctor_get(v_cfg_216_, 8);
v_allowImportAll_228_ = lean_ctor_get_uint8(v_cfg_216_, sizeof(void*)*9 + 2);
v_isSharedCheck_236_ = !lean_is_exclusive(v_cfg_216_);
if (v_isSharedCheck_236_ == 0)
{
v___x_230_ = v_cfg_216_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_nativeFacets_227_);
lean_inc(v_defaultFacets_226_);
lean_inc(v_extraDepTargets_224_);
lean_inc(v_needs_223_);
lean_inc(v_libName_221_);
lean_inc(v_globs_220_);
lean_inc(v_roots_219_);
lean_inc(v_srcDir_218_);
lean_inc(v_toLeanConfig_217_);
lean_dec(v_cfg_216_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_apply_1(v_f_215_, v_globs_220_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 3, v___x_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_toLeanConfig_217_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_srcDir_218_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_roots_219_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_libName_221_);
lean_ctor_set(v_reuseFailAlloc_235_, 5, v_needs_223_);
lean_ctor_set(v_reuseFailAlloc_235_, 6, v_extraDepTargets_224_);
lean_ctor_set(v_reuseFailAlloc_235_, 7, v_defaultFacets_226_);
lean_ctor_set(v_reuseFailAlloc_235_, 8, v_nativeFacets_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_235_, sizeof(void*)*9, v_libPrefixOnWindows_222_);
lean_ctor_set_uint8(v_reuseFailAlloc_235_, sizeof(void*)*9 + 1, v_precompileModules_225_);
lean_ctor_set_uint8(v_reuseFailAlloc_235_, sizeof(void*)*9 + 2, v_allowImportAll_228_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__3(lean_object* v_x_237_){
_start:
{
lean_object* v_roots_238_; size_t v_sz_239_; size_t v___x_240_; lean_object* v___x_241_; 
v_roots_238_ = lean_ctor_get(v_x_237_, 2);
lean_inc_ref(v_roots_238_);
lean_dec_ref(v_x_237_);
v_sz_239_ = lean_array_size(v_roots_238_);
v___x_240_ = ((size_t)0ULL);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_239_, v___x_240_, v_roots_238_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object* v_name_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = ((lean_object*)(l_Lake_LeanLibConfig_globs___proj___closed__4));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object* v_name_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lake_LeanLibConfig_globs___proj(v_name_253_);
lean_dec(v_name_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object* v_name_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lake_LeanLibConfig_globs___proj(v_name_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object* v_name_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_257_);
lean_dec(v_name_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0(lean_object* v_cfg_259_){
_start:
{
lean_object* v_libName_260_; 
v_libName_260_ = lean_ctor_get(v_cfg_259_, 4);
lean_inc_ref(v_libName_260_);
return v_libName_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0___boxed(lean_object* v_cfg_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lake_LeanLibConfig_libName___proj___lam__0(v_cfg_261_);
lean_dec_ref(v_cfg_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__1(lean_object* v_val_263_, lean_object* v_cfg_264_){
_start:
{
lean_object* v_toLeanConfig_265_; lean_object* v_srcDir_266_; lean_object* v_roots_267_; lean_object* v_globs_268_; uint8_t v_libPrefixOnWindows_269_; lean_object* v_needs_270_; lean_object* v_extraDepTargets_271_; uint8_t v_precompileModules_272_; lean_object* v_defaultFacets_273_; lean_object* v_nativeFacets_274_; uint8_t v_allowImportAll_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_toLeanConfig_265_ = lean_ctor_get(v_cfg_264_, 0);
v_srcDir_266_ = lean_ctor_get(v_cfg_264_, 1);
v_roots_267_ = lean_ctor_get(v_cfg_264_, 2);
v_globs_268_ = lean_ctor_get(v_cfg_264_, 3);
v_libPrefixOnWindows_269_ = lean_ctor_get_uint8(v_cfg_264_, sizeof(void*)*9);
v_needs_270_ = lean_ctor_get(v_cfg_264_, 5);
v_extraDepTargets_271_ = lean_ctor_get(v_cfg_264_, 6);
v_precompileModules_272_ = lean_ctor_get_uint8(v_cfg_264_, sizeof(void*)*9 + 1);
v_defaultFacets_273_ = lean_ctor_get(v_cfg_264_, 7);
v_nativeFacets_274_ = lean_ctor_get(v_cfg_264_, 8);
v_allowImportAll_275_ = lean_ctor_get_uint8(v_cfg_264_, sizeof(void*)*9 + 2);
v_isSharedCheck_282_ = !lean_is_exclusive(v_cfg_264_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v_cfg_264_, 4);
lean_dec(v_unused_283_);
v___x_277_ = v_cfg_264_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_nativeFacets_274_);
lean_inc(v_defaultFacets_273_);
lean_inc(v_extraDepTargets_271_);
lean_inc(v_needs_270_);
lean_inc(v_globs_268_);
lean_inc(v_roots_267_);
lean_inc(v_srcDir_266_);
lean_inc(v_toLeanConfig_265_);
lean_dec(v_cfg_264_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 4, v_val_263_);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_toLeanConfig_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_srcDir_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_roots_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_globs_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_val_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_needs_270_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_extraDepTargets_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_defaultFacets_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_nativeFacets_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*9, v_libPrefixOnWindows_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*9 + 1, v_precompileModules_272_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, sizeof(void*)*9 + 2, v_allowImportAll_275_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__2(lean_object* v_f_284_, lean_object* v_cfg_285_){
_start:
{
lean_object* v_toLeanConfig_286_; lean_object* v_srcDir_287_; lean_object* v_roots_288_; lean_object* v_globs_289_; lean_object* v_libName_290_; uint8_t v_libPrefixOnWindows_291_; lean_object* v_needs_292_; lean_object* v_extraDepTargets_293_; uint8_t v_precompileModules_294_; lean_object* v_defaultFacets_295_; lean_object* v_nativeFacets_296_; uint8_t v_allowImportAll_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v_toLeanConfig_286_ = lean_ctor_get(v_cfg_285_, 0);
v_srcDir_287_ = lean_ctor_get(v_cfg_285_, 1);
v_roots_288_ = lean_ctor_get(v_cfg_285_, 2);
v_globs_289_ = lean_ctor_get(v_cfg_285_, 3);
v_libName_290_ = lean_ctor_get(v_cfg_285_, 4);
v_libPrefixOnWindows_291_ = lean_ctor_get_uint8(v_cfg_285_, sizeof(void*)*9);
v_needs_292_ = lean_ctor_get(v_cfg_285_, 5);
v_extraDepTargets_293_ = lean_ctor_get(v_cfg_285_, 6);
v_precompileModules_294_ = lean_ctor_get_uint8(v_cfg_285_, sizeof(void*)*9 + 1);
v_defaultFacets_295_ = lean_ctor_get(v_cfg_285_, 7);
v_nativeFacets_296_ = lean_ctor_get(v_cfg_285_, 8);
v_allowImportAll_297_ = lean_ctor_get_uint8(v_cfg_285_, sizeof(void*)*9 + 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_cfg_285_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v_cfg_285_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_nativeFacets_296_);
lean_inc(v_defaultFacets_295_);
lean_inc(v_extraDepTargets_293_);
lean_inc(v_needs_292_);
lean_inc(v_libName_290_);
lean_inc(v_globs_289_);
lean_inc(v_roots_288_);
lean_inc(v_srcDir_287_);
lean_inc(v_toLeanConfig_286_);
lean_dec(v_cfg_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_apply_1(v_f_284_, v_libName_290_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 4, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_toLeanConfig_286_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_srcDir_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_roots_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_globs_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_needs_292_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_extraDepTargets_293_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_defaultFacets_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_nativeFacets_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*9, v_libPrefixOnWindows_291_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*9 + 1, v_precompileModules_294_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*9 + 2, v_allowImportAll_297_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3(lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3___boxed(lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lake_LeanLibConfig_libName___proj___lam__3(v_x_308_);
lean_dec_ref(v_x_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object* v_name_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = ((lean_object*)(l_Lake_LeanLibConfig_libName___proj___closed__4));
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object* v_name_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lake_LeanLibConfig_libName___proj(v_name_321_);
lean_dec(v_name_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object* v_name_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lake_LeanLibConfig_libName___proj(v_name_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object* v_name_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_325_);
lean_dec(v_name_325_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_327_){
_start:
{
uint8_t v_libPrefixOnWindows_328_; 
v_libPrefixOnWindows_328_ = lean_ctor_get_uint8(v_cfg_327_, sizeof(void*)*9);
return v_libPrefixOnWindows_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(v_cfg_329_);
lean_dec_ref(v_cfg_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_332_, lean_object* v_cfg_333_){
_start:
{
lean_object* v_toLeanConfig_334_; lean_object* v_srcDir_335_; lean_object* v_roots_336_; lean_object* v_globs_337_; lean_object* v_libName_338_; lean_object* v_needs_339_; lean_object* v_extraDepTargets_340_; uint8_t v_precompileModules_341_; lean_object* v_defaultFacets_342_; lean_object* v_nativeFacets_343_; uint8_t v_allowImportAll_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_toLeanConfig_334_ = lean_ctor_get(v_cfg_333_, 0);
v_srcDir_335_ = lean_ctor_get(v_cfg_333_, 1);
v_roots_336_ = lean_ctor_get(v_cfg_333_, 2);
v_globs_337_ = lean_ctor_get(v_cfg_333_, 3);
v_libName_338_ = lean_ctor_get(v_cfg_333_, 4);
v_needs_339_ = lean_ctor_get(v_cfg_333_, 5);
v_extraDepTargets_340_ = lean_ctor_get(v_cfg_333_, 6);
v_precompileModules_341_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*9 + 1);
v_defaultFacets_342_ = lean_ctor_get(v_cfg_333_, 7);
v_nativeFacets_343_ = lean_ctor_get(v_cfg_333_, 8);
v_allowImportAll_344_ = lean_ctor_get_uint8(v_cfg_333_, sizeof(void*)*9 + 2);
v_isSharedCheck_351_ = !lean_is_exclusive(v_cfg_333_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v_cfg_333_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_nativeFacets_343_);
lean_inc(v_defaultFacets_342_);
lean_inc(v_extraDepTargets_340_);
lean_inc(v_needs_339_);
lean_inc(v_libName_338_);
lean_inc(v_globs_337_);
lean_inc(v_roots_336_);
lean_inc(v_srcDir_335_);
lean_inc(v_toLeanConfig_334_);
lean_dec(v_cfg_333_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_toLeanConfig_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_srcDir_335_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_roots_336_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_globs_337_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_libName_338_);
lean_ctor_set(v_reuseFailAlloc_350_, 5, v_needs_339_);
lean_ctor_set(v_reuseFailAlloc_350_, 6, v_extraDepTargets_340_);
lean_ctor_set(v_reuseFailAlloc_350_, 7, v_defaultFacets_342_);
lean_ctor_set(v_reuseFailAlloc_350_, 8, v_nativeFacets_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_350_, sizeof(void*)*9 + 1, v_precompileModules_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_350_, sizeof(void*)*9 + 2, v_allowImportAll_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*9, v_val_332_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_352_, lean_object* v_cfg_353_){
_start:
{
uint8_t v_val_71__boxed_354_; lean_object* v_res_355_; 
v_val_71__boxed_354_ = lean_unbox(v_val_352_);
v_res_355_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(v_val_71__boxed_354_, v_cfg_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_356_, lean_object* v_cfg_357_){
_start:
{
lean_object* v_toLeanConfig_358_; lean_object* v_srcDir_359_; lean_object* v_roots_360_; lean_object* v_globs_361_; lean_object* v_libName_362_; uint8_t v_libPrefixOnWindows_363_; lean_object* v_needs_364_; lean_object* v_extraDepTargets_365_; uint8_t v_precompileModules_366_; lean_object* v_defaultFacets_367_; lean_object* v_nativeFacets_368_; uint8_t v_allowImportAll_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_379_; 
v_toLeanConfig_358_ = lean_ctor_get(v_cfg_357_, 0);
v_srcDir_359_ = lean_ctor_get(v_cfg_357_, 1);
v_roots_360_ = lean_ctor_get(v_cfg_357_, 2);
v_globs_361_ = lean_ctor_get(v_cfg_357_, 3);
v_libName_362_ = lean_ctor_get(v_cfg_357_, 4);
v_libPrefixOnWindows_363_ = lean_ctor_get_uint8(v_cfg_357_, sizeof(void*)*9);
v_needs_364_ = lean_ctor_get(v_cfg_357_, 5);
v_extraDepTargets_365_ = lean_ctor_get(v_cfg_357_, 6);
v_precompileModules_366_ = lean_ctor_get_uint8(v_cfg_357_, sizeof(void*)*9 + 1);
v_defaultFacets_367_ = lean_ctor_get(v_cfg_357_, 7);
v_nativeFacets_368_ = lean_ctor_get(v_cfg_357_, 8);
v_allowImportAll_369_ = lean_ctor_get_uint8(v_cfg_357_, sizeof(void*)*9 + 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_cfg_357_);
if (v_isSharedCheck_379_ == 0)
{
v___x_371_ = v_cfg_357_;
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_nativeFacets_368_);
lean_inc(v_defaultFacets_367_);
lean_inc(v_extraDepTargets_365_);
lean_inc(v_needs_364_);
lean_inc(v_libName_362_);
lean_inc(v_globs_361_);
lean_inc(v_roots_360_);
lean_inc(v_srcDir_359_);
lean_inc(v_toLeanConfig_358_);
lean_dec(v_cfg_357_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_box(v_libPrefixOnWindows_363_);
v___x_374_ = lean_apply_1(v_f_356_, v___x_373_);
if (v_isShared_372_ == 0)
{
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_toLeanConfig_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_srcDir_359_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_roots_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_globs_361_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_libName_362_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_needs_364_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_extraDepTargets_365_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v_defaultFacets_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v_nativeFacets_368_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
uint8_t v___x_377_; 
v___x_377_ = lean_unbox(v___x_374_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*9, v___x_377_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*9 + 1, v_precompileModules_366_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*9 + 2, v_allowImportAll_369_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(lean_object* v_x_380_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = 0;
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed(lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(v_x_382_);
lean_dec_ref(v_x_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object* v_name_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = ((lean_object*)(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4));
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object* v_name_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_396_);
lean_dec(v_name_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object* v_name_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_name_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_400_);
lean_dec(v_name_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0(lean_object* v_cfg_402_){
_start:
{
lean_object* v_needs_403_; 
v_needs_403_ = lean_ctor_get(v_cfg_402_, 5);
lean_inc_ref(v_needs_403_);
return v_needs_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0___boxed(lean_object* v_cfg_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lake_LeanLibConfig_needs___proj___lam__0(v_cfg_404_);
lean_dec_ref(v_cfg_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__1(lean_object* v_val_406_, lean_object* v_cfg_407_){
_start:
{
lean_object* v_toLeanConfig_408_; lean_object* v_srcDir_409_; lean_object* v_roots_410_; lean_object* v_globs_411_; lean_object* v_libName_412_; uint8_t v_libPrefixOnWindows_413_; lean_object* v_extraDepTargets_414_; uint8_t v_precompileModules_415_; lean_object* v_defaultFacets_416_; lean_object* v_nativeFacets_417_; uint8_t v_allowImportAll_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_toLeanConfig_408_ = lean_ctor_get(v_cfg_407_, 0);
v_srcDir_409_ = lean_ctor_get(v_cfg_407_, 1);
v_roots_410_ = lean_ctor_get(v_cfg_407_, 2);
v_globs_411_ = lean_ctor_get(v_cfg_407_, 3);
v_libName_412_ = lean_ctor_get(v_cfg_407_, 4);
v_libPrefixOnWindows_413_ = lean_ctor_get_uint8(v_cfg_407_, sizeof(void*)*9);
v_extraDepTargets_414_ = lean_ctor_get(v_cfg_407_, 6);
v_precompileModules_415_ = lean_ctor_get_uint8(v_cfg_407_, sizeof(void*)*9 + 1);
v_defaultFacets_416_ = lean_ctor_get(v_cfg_407_, 7);
v_nativeFacets_417_ = lean_ctor_get(v_cfg_407_, 8);
v_allowImportAll_418_ = lean_ctor_get_uint8(v_cfg_407_, sizeof(void*)*9 + 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v_cfg_407_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_cfg_407_, 5);
lean_dec(v_unused_426_);
v___x_420_ = v_cfg_407_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_nativeFacets_417_);
lean_inc(v_defaultFacets_416_);
lean_inc(v_extraDepTargets_414_);
lean_inc(v_libName_412_);
lean_inc(v_globs_411_);
lean_inc(v_roots_410_);
lean_inc(v_srcDir_409_);
lean_inc(v_toLeanConfig_408_);
lean_dec(v_cfg_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 5, v_val_406_);
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_toLeanConfig_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_srcDir_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_roots_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_globs_411_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_libName_412_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_val_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_extraDepTargets_414_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_defaultFacets_416_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_nativeFacets_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*9, v_libPrefixOnWindows_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*9 + 1, v_precompileModules_415_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*9 + 2, v_allowImportAll_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__2(lean_object* v_f_427_, lean_object* v_cfg_428_){
_start:
{
lean_object* v_toLeanConfig_429_; lean_object* v_srcDir_430_; lean_object* v_roots_431_; lean_object* v_globs_432_; lean_object* v_libName_433_; uint8_t v_libPrefixOnWindows_434_; lean_object* v_needs_435_; lean_object* v_extraDepTargets_436_; uint8_t v_precompileModules_437_; lean_object* v_defaultFacets_438_; lean_object* v_nativeFacets_439_; uint8_t v_allowImportAll_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_toLeanConfig_429_ = lean_ctor_get(v_cfg_428_, 0);
v_srcDir_430_ = lean_ctor_get(v_cfg_428_, 1);
v_roots_431_ = lean_ctor_get(v_cfg_428_, 2);
v_globs_432_ = lean_ctor_get(v_cfg_428_, 3);
v_libName_433_ = lean_ctor_get(v_cfg_428_, 4);
v_libPrefixOnWindows_434_ = lean_ctor_get_uint8(v_cfg_428_, sizeof(void*)*9);
v_needs_435_ = lean_ctor_get(v_cfg_428_, 5);
v_extraDepTargets_436_ = lean_ctor_get(v_cfg_428_, 6);
v_precompileModules_437_ = lean_ctor_get_uint8(v_cfg_428_, sizeof(void*)*9 + 1);
v_defaultFacets_438_ = lean_ctor_get(v_cfg_428_, 7);
v_nativeFacets_439_ = lean_ctor_get(v_cfg_428_, 8);
v_allowImportAll_440_ = lean_ctor_get_uint8(v_cfg_428_, sizeof(void*)*9 + 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_cfg_428_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v_cfg_428_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_nativeFacets_439_);
lean_inc(v_defaultFacets_438_);
lean_inc(v_extraDepTargets_436_);
lean_inc(v_needs_435_);
lean_inc(v_libName_433_);
lean_inc(v_globs_432_);
lean_inc(v_roots_431_);
lean_inc(v_srcDir_430_);
lean_inc(v_toLeanConfig_429_);
lean_dec(v_cfg_428_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_apply_1(v_f_427_, v_needs_435_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 5, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_toLeanConfig_429_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_srcDir_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_roots_431_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_globs_432_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_libName_433_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_extraDepTargets_436_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_defaultFacets_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_nativeFacets_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*9, v_libPrefixOnWindows_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*9 + 1, v_precompileModules_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*9 + 2, v_allowImportAll_440_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3(lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_LeanLibConfig_needs___proj___lam__3(v_x_451_);
lean_dec_ref(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object* v_name_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___closed__4));
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object* v_name_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_LeanLibConfig_needs___proj(v_name_464_);
lean_dec(v_name_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object* v_name_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lake_LeanLibConfig_needs___proj(v_name_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object* v_name_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_468_);
lean_dec(v_name_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_470_){
_start:
{
lean_object* v_extraDepTargets_471_; 
v_extraDepTargets_471_ = lean_ctor_get(v_cfg_470_, 6);
lean_inc_ref(v_extraDepTargets_471_);
return v_extraDepTargets_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(v_cfg_472_);
lean_dec_ref(v_cfg_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1(lean_object* v_val_474_, lean_object* v_cfg_475_){
_start:
{
lean_object* v_toLeanConfig_476_; lean_object* v_srcDir_477_; lean_object* v_roots_478_; lean_object* v_globs_479_; lean_object* v_libName_480_; uint8_t v_libPrefixOnWindows_481_; lean_object* v_needs_482_; uint8_t v_precompileModules_483_; lean_object* v_defaultFacets_484_; lean_object* v_nativeFacets_485_; uint8_t v_allowImportAll_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_toLeanConfig_476_ = lean_ctor_get(v_cfg_475_, 0);
v_srcDir_477_ = lean_ctor_get(v_cfg_475_, 1);
v_roots_478_ = lean_ctor_get(v_cfg_475_, 2);
v_globs_479_ = lean_ctor_get(v_cfg_475_, 3);
v_libName_480_ = lean_ctor_get(v_cfg_475_, 4);
v_libPrefixOnWindows_481_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9);
v_needs_482_ = lean_ctor_get(v_cfg_475_, 5);
v_precompileModules_483_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9 + 1);
v_defaultFacets_484_ = lean_ctor_get(v_cfg_475_, 7);
v_nativeFacets_485_ = lean_ctor_get(v_cfg_475_, 8);
v_allowImportAll_486_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9 + 2);
v_isSharedCheck_493_ = !lean_is_exclusive(v_cfg_475_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_cfg_475_, 6);
lean_dec(v_unused_494_);
v___x_488_ = v_cfg_475_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_nativeFacets_485_);
lean_inc(v_defaultFacets_484_);
lean_inc(v_needs_482_);
lean_inc(v_libName_480_);
lean_inc(v_globs_479_);
lean_inc(v_roots_478_);
lean_inc(v_srcDir_477_);
lean_inc(v_toLeanConfig_476_);
lean_dec(v_cfg_475_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 6, v_val_474_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_toLeanConfig_476_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_srcDir_477_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_roots_478_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_globs_479_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_libName_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_needs_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_val_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 7, v_defaultFacets_484_);
lean_ctor_set(v_reuseFailAlloc_492_, 8, v_nativeFacets_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*9, v_libPrefixOnWindows_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*9 + 1, v_precompileModules_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*9 + 2, v_allowImportAll_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2(lean_object* v_f_495_, lean_object* v_cfg_496_){
_start:
{
lean_object* v_toLeanConfig_497_; lean_object* v_srcDir_498_; lean_object* v_roots_499_; lean_object* v_globs_500_; lean_object* v_libName_501_; uint8_t v_libPrefixOnWindows_502_; lean_object* v_needs_503_; lean_object* v_extraDepTargets_504_; uint8_t v_precompileModules_505_; lean_object* v_defaultFacets_506_; lean_object* v_nativeFacets_507_; uint8_t v_allowImportAll_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_toLeanConfig_497_ = lean_ctor_get(v_cfg_496_, 0);
v_srcDir_498_ = lean_ctor_get(v_cfg_496_, 1);
v_roots_499_ = lean_ctor_get(v_cfg_496_, 2);
v_globs_500_ = lean_ctor_get(v_cfg_496_, 3);
v_libName_501_ = lean_ctor_get(v_cfg_496_, 4);
v_libPrefixOnWindows_502_ = lean_ctor_get_uint8(v_cfg_496_, sizeof(void*)*9);
v_needs_503_ = lean_ctor_get(v_cfg_496_, 5);
v_extraDepTargets_504_ = lean_ctor_get(v_cfg_496_, 6);
v_precompileModules_505_ = lean_ctor_get_uint8(v_cfg_496_, sizeof(void*)*9 + 1);
v_defaultFacets_506_ = lean_ctor_get(v_cfg_496_, 7);
v_nativeFacets_507_ = lean_ctor_get(v_cfg_496_, 8);
v_allowImportAll_508_ = lean_ctor_get_uint8(v_cfg_496_, sizeof(void*)*9 + 2);
v_isSharedCheck_516_ = !lean_is_exclusive(v_cfg_496_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v_cfg_496_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_nativeFacets_507_);
lean_inc(v_defaultFacets_506_);
lean_inc(v_extraDepTargets_504_);
lean_inc(v_needs_503_);
lean_inc(v_libName_501_);
lean_inc(v_globs_500_);
lean_inc(v_roots_499_);
lean_inc(v_srcDir_498_);
lean_inc(v_toLeanConfig_497_);
lean_dec(v_cfg_496_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_apply_1(v_f_495_, v_extraDepTargets_504_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 6, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_toLeanConfig_497_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_srcDir_498_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_roots_499_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_globs_500_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_libName_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_needs_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_defaultFacets_506_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_nativeFacets_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_515_, sizeof(void*)*9, v_libPrefixOnWindows_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_515_, sizeof(void*)*9 + 1, v_precompileModules_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_515_, sizeof(void*)*9 + 2, v_allowImportAll_508_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(v_x_521_);
lean_dec_ref(v_x_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object* v_name_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4));
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object* v_name_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_534_);
lean_dec(v_name_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object* v_name_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object* v_name_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_538_);
lean_dec(v_name_538_);
return v_res_539_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___lam__0(lean_object* v_cfg_540_){
_start:
{
uint8_t v_precompileModules_541_; 
v_precompileModules_541_ = lean_ctor_get_uint8(v_cfg_540_, sizeof(void*)*9 + 1);
return v_precompileModules_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__0(v_cfg_542_);
lean_dec_ref(v_cfg_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1(uint8_t v_val_545_, lean_object* v_cfg_546_){
_start:
{
lean_object* v_toLeanConfig_547_; lean_object* v_srcDir_548_; lean_object* v_roots_549_; lean_object* v_globs_550_; lean_object* v_libName_551_; uint8_t v_libPrefixOnWindows_552_; lean_object* v_needs_553_; lean_object* v_extraDepTargets_554_; lean_object* v_defaultFacets_555_; lean_object* v_nativeFacets_556_; uint8_t v_allowImportAll_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_toLeanConfig_547_ = lean_ctor_get(v_cfg_546_, 0);
v_srcDir_548_ = lean_ctor_get(v_cfg_546_, 1);
v_roots_549_ = lean_ctor_get(v_cfg_546_, 2);
v_globs_550_ = lean_ctor_get(v_cfg_546_, 3);
v_libName_551_ = lean_ctor_get(v_cfg_546_, 4);
v_libPrefixOnWindows_552_ = lean_ctor_get_uint8(v_cfg_546_, sizeof(void*)*9);
v_needs_553_ = lean_ctor_get(v_cfg_546_, 5);
v_extraDepTargets_554_ = lean_ctor_get(v_cfg_546_, 6);
v_defaultFacets_555_ = lean_ctor_get(v_cfg_546_, 7);
v_nativeFacets_556_ = lean_ctor_get(v_cfg_546_, 8);
v_allowImportAll_557_ = lean_ctor_get_uint8(v_cfg_546_, sizeof(void*)*9 + 2);
v_isSharedCheck_564_ = !lean_is_exclusive(v_cfg_546_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v_cfg_546_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_nativeFacets_556_);
lean_inc(v_defaultFacets_555_);
lean_inc(v_extraDepTargets_554_);
lean_inc(v_needs_553_);
lean_inc(v_libName_551_);
lean_inc(v_globs_550_);
lean_inc(v_roots_549_);
lean_inc(v_srcDir_548_);
lean_inc(v_toLeanConfig_547_);
lean_dec(v_cfg_546_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_toLeanConfig_547_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_srcDir_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_roots_549_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_globs_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_libName_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v_needs_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_extraDepTargets_554_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_defaultFacets_555_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_nativeFacets_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*9, v_libPrefixOnWindows_552_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*9 + 2, v_allowImportAll_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*9 + 1, v_val_545_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_565_, lean_object* v_cfg_566_){
_start:
{
uint8_t v_val_71__boxed_567_; lean_object* v_res_568_; 
v_val_71__boxed_567_ = lean_unbox(v_val_565_);
v_res_568_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__1(v_val_71__boxed_567_, v_cfg_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__2(lean_object* v_f_569_, lean_object* v_cfg_570_){
_start:
{
lean_object* v_toLeanConfig_571_; lean_object* v_srcDir_572_; lean_object* v_roots_573_; lean_object* v_globs_574_; lean_object* v_libName_575_; uint8_t v_libPrefixOnWindows_576_; lean_object* v_needs_577_; lean_object* v_extraDepTargets_578_; uint8_t v_precompileModules_579_; lean_object* v_defaultFacets_580_; lean_object* v_nativeFacets_581_; uint8_t v_allowImportAll_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_592_; 
v_toLeanConfig_571_ = lean_ctor_get(v_cfg_570_, 0);
v_srcDir_572_ = lean_ctor_get(v_cfg_570_, 1);
v_roots_573_ = lean_ctor_get(v_cfg_570_, 2);
v_globs_574_ = lean_ctor_get(v_cfg_570_, 3);
v_libName_575_ = lean_ctor_get(v_cfg_570_, 4);
v_libPrefixOnWindows_576_ = lean_ctor_get_uint8(v_cfg_570_, sizeof(void*)*9);
v_needs_577_ = lean_ctor_get(v_cfg_570_, 5);
v_extraDepTargets_578_ = lean_ctor_get(v_cfg_570_, 6);
v_precompileModules_579_ = lean_ctor_get_uint8(v_cfg_570_, sizeof(void*)*9 + 1);
v_defaultFacets_580_ = lean_ctor_get(v_cfg_570_, 7);
v_nativeFacets_581_ = lean_ctor_get(v_cfg_570_, 8);
v_allowImportAll_582_ = lean_ctor_get_uint8(v_cfg_570_, sizeof(void*)*9 + 2);
v_isSharedCheck_592_ = !lean_is_exclusive(v_cfg_570_);
if (v_isSharedCheck_592_ == 0)
{
v___x_584_ = v_cfg_570_;
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_nativeFacets_581_);
lean_inc(v_defaultFacets_580_);
lean_inc(v_extraDepTargets_578_);
lean_inc(v_needs_577_);
lean_inc(v_libName_575_);
lean_inc(v_globs_574_);
lean_inc(v_roots_573_);
lean_inc(v_srcDir_572_);
lean_inc(v_toLeanConfig_571_);
lean_dec(v_cfg_570_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = lean_box(v_precompileModules_579_);
v___x_587_ = lean_apply_1(v_f_569_, v___x_586_);
if (v_isShared_585_ == 0)
{
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_toLeanConfig_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_srcDir_572_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_roots_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_globs_574_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_libName_575_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v_needs_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_extraDepTargets_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_defaultFacets_580_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_nativeFacets_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*9, v_libPrefixOnWindows_576_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v___x_587_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*9 + 1, v___x_590_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*9 + 2, v_allowImportAll_582_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object* v_name_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileModules___proj___closed__3));
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object* v_name_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_603_);
lean_dec(v_name_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object* v_name_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object* v_name_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_607_);
lean_dec(v_name_607_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(lean_object* v_cfg_609_){
_start:
{
lean_object* v_defaultFacets_610_; 
v_defaultFacets_610_ = lean_ctor_get(v_cfg_609_, 7);
lean_inc_ref(v_defaultFacets_610_);
return v_defaultFacets_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed(lean_object* v_cfg_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(v_cfg_611_);
lean_dec_ref(v_cfg_611_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__1(lean_object* v_val_613_, lean_object* v_cfg_614_){
_start:
{
lean_object* v_toLeanConfig_615_; lean_object* v_srcDir_616_; lean_object* v_roots_617_; lean_object* v_globs_618_; lean_object* v_libName_619_; uint8_t v_libPrefixOnWindows_620_; lean_object* v_needs_621_; lean_object* v_extraDepTargets_622_; uint8_t v_precompileModules_623_; lean_object* v_nativeFacets_624_; uint8_t v_allowImportAll_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_toLeanConfig_615_ = lean_ctor_get(v_cfg_614_, 0);
v_srcDir_616_ = lean_ctor_get(v_cfg_614_, 1);
v_roots_617_ = lean_ctor_get(v_cfg_614_, 2);
v_globs_618_ = lean_ctor_get(v_cfg_614_, 3);
v_libName_619_ = lean_ctor_get(v_cfg_614_, 4);
v_libPrefixOnWindows_620_ = lean_ctor_get_uint8(v_cfg_614_, sizeof(void*)*9);
v_needs_621_ = lean_ctor_get(v_cfg_614_, 5);
v_extraDepTargets_622_ = lean_ctor_get(v_cfg_614_, 6);
v_precompileModules_623_ = lean_ctor_get_uint8(v_cfg_614_, sizeof(void*)*9 + 1);
v_nativeFacets_624_ = lean_ctor_get(v_cfg_614_, 8);
v_allowImportAll_625_ = lean_ctor_get_uint8(v_cfg_614_, sizeof(void*)*9 + 2);
v_isSharedCheck_632_ = !lean_is_exclusive(v_cfg_614_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_cfg_614_, 7);
lean_dec(v_unused_633_);
v___x_627_ = v_cfg_614_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_nativeFacets_624_);
lean_inc(v_extraDepTargets_622_);
lean_inc(v_needs_621_);
lean_inc(v_libName_619_);
lean_inc(v_globs_618_);
lean_inc(v_roots_617_);
lean_inc(v_srcDir_616_);
lean_inc(v_toLeanConfig_615_);
lean_dec(v_cfg_614_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 7, v_val_613_);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_toLeanConfig_615_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_srcDir_616_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_roots_617_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_globs_618_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_libName_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 5, v_needs_621_);
lean_ctor_set(v_reuseFailAlloc_631_, 6, v_extraDepTargets_622_);
lean_ctor_set(v_reuseFailAlloc_631_, 7, v_val_613_);
lean_ctor_set(v_reuseFailAlloc_631_, 8, v_nativeFacets_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*9, v_libPrefixOnWindows_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*9 + 1, v_precompileModules_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*9 + 2, v_allowImportAll_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__2(lean_object* v_f_634_, lean_object* v_cfg_635_){
_start:
{
lean_object* v_toLeanConfig_636_; lean_object* v_srcDir_637_; lean_object* v_roots_638_; lean_object* v_globs_639_; lean_object* v_libName_640_; uint8_t v_libPrefixOnWindows_641_; lean_object* v_needs_642_; lean_object* v_extraDepTargets_643_; uint8_t v_precompileModules_644_; lean_object* v_defaultFacets_645_; lean_object* v_nativeFacets_646_; uint8_t v_allowImportAll_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
v_toLeanConfig_636_ = lean_ctor_get(v_cfg_635_, 0);
v_srcDir_637_ = lean_ctor_get(v_cfg_635_, 1);
v_roots_638_ = lean_ctor_get(v_cfg_635_, 2);
v_globs_639_ = lean_ctor_get(v_cfg_635_, 3);
v_libName_640_ = lean_ctor_get(v_cfg_635_, 4);
v_libPrefixOnWindows_641_ = lean_ctor_get_uint8(v_cfg_635_, sizeof(void*)*9);
v_needs_642_ = lean_ctor_get(v_cfg_635_, 5);
v_extraDepTargets_643_ = lean_ctor_get(v_cfg_635_, 6);
v_precompileModules_644_ = lean_ctor_get_uint8(v_cfg_635_, sizeof(void*)*9 + 1);
v_defaultFacets_645_ = lean_ctor_get(v_cfg_635_, 7);
v_nativeFacets_646_ = lean_ctor_get(v_cfg_635_, 8);
v_allowImportAll_647_ = lean_ctor_get_uint8(v_cfg_635_, sizeof(void*)*9 + 2);
v_isSharedCheck_655_ = !lean_is_exclusive(v_cfg_635_);
if (v_isSharedCheck_655_ == 0)
{
v___x_649_ = v_cfg_635_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_nativeFacets_646_);
lean_inc(v_defaultFacets_645_);
lean_inc(v_extraDepTargets_643_);
lean_inc(v_needs_642_);
lean_inc(v_libName_640_);
lean_inc(v_globs_639_);
lean_inc(v_roots_638_);
lean_inc(v_srcDir_637_);
lean_inc(v_toLeanConfig_636_);
lean_dec(v_cfg_635_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_apply_1(v_f_634_, v_defaultFacets_645_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 7, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_toLeanConfig_636_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_srcDir_637_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_roots_638_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_globs_639_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_libName_640_);
lean_ctor_set(v_reuseFailAlloc_654_, 5, v_needs_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 6, v_extraDepTargets_643_);
lean_ctor_set(v_reuseFailAlloc_654_, 7, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 8, v_nativeFacets_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_654_, sizeof(void*)*9, v_libPrefixOnWindows_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_654_, sizeof(void*)*9 + 1, v_precompileModules_644_);
lean_ctor_set_uint8(v_reuseFailAlloc_654_, sizeof(void*)*9 + 2, v_allowImportAll_647_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_mk_empty_array_with_capacity(v___x_657_);
lean_dec_ref(v___x_658_);
v___x_659_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed(lean_object* v_x_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(v_x_660_);
lean_dec_ref(v_x_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object* v_name_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = ((lean_object*)(l_Lake_LeanLibConfig_defaultFacets___proj___closed__4));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object* v_name_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_673_);
lean_dec(v_name_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object* v_name_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object* v_name_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_677_);
lean_dec(v_name_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(lean_object* v_cfg_679_, uint8_t v___y_680_){
_start:
{
lean_object* v_nativeFacets_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_nativeFacets_681_ = lean_ctor_get(v_cfg_679_, 8);
lean_inc_ref(v_nativeFacets_681_);
lean_dec_ref(v_cfg_679_);
v___x_682_ = lean_box(v___y_680_);
v___x_683_ = lean_apply_1(v_nativeFacets_681_, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed(lean_object* v_cfg_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___y_147__boxed_686_; lean_object* v_res_687_; 
v___y_147__boxed_686_ = lean_unbox(v___y_685_);
v_res_687_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(v_cfg_684_, v___y_147__boxed_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__1(lean_object* v_val_688_, lean_object* v_cfg_689_){
_start:
{
lean_object* v_toLeanConfig_690_; lean_object* v_srcDir_691_; lean_object* v_roots_692_; lean_object* v_globs_693_; lean_object* v_libName_694_; uint8_t v_libPrefixOnWindows_695_; lean_object* v_needs_696_; lean_object* v_extraDepTargets_697_; uint8_t v_precompileModules_698_; lean_object* v_defaultFacets_699_; uint8_t v_allowImportAll_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_toLeanConfig_690_ = lean_ctor_get(v_cfg_689_, 0);
v_srcDir_691_ = lean_ctor_get(v_cfg_689_, 1);
v_roots_692_ = lean_ctor_get(v_cfg_689_, 2);
v_globs_693_ = lean_ctor_get(v_cfg_689_, 3);
v_libName_694_ = lean_ctor_get(v_cfg_689_, 4);
v_libPrefixOnWindows_695_ = lean_ctor_get_uint8(v_cfg_689_, sizeof(void*)*9);
v_needs_696_ = lean_ctor_get(v_cfg_689_, 5);
v_extraDepTargets_697_ = lean_ctor_get(v_cfg_689_, 6);
v_precompileModules_698_ = lean_ctor_get_uint8(v_cfg_689_, sizeof(void*)*9 + 1);
v_defaultFacets_699_ = lean_ctor_get(v_cfg_689_, 7);
v_allowImportAll_700_ = lean_ctor_get_uint8(v_cfg_689_, sizeof(void*)*9 + 2);
v_isSharedCheck_707_ = !lean_is_exclusive(v_cfg_689_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_cfg_689_, 8);
lean_dec(v_unused_708_);
v___x_702_ = v_cfg_689_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_defaultFacets_699_);
lean_inc(v_extraDepTargets_697_);
lean_inc(v_needs_696_);
lean_inc(v_libName_694_);
lean_inc(v_globs_693_);
lean_inc(v_roots_692_);
lean_inc(v_srcDir_691_);
lean_inc(v_toLeanConfig_690_);
lean_dec(v_cfg_689_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 8, v_val_688_);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_toLeanConfig_690_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_srcDir_691_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_roots_692_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_globs_693_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_libName_694_);
lean_ctor_set(v_reuseFailAlloc_706_, 5, v_needs_696_);
lean_ctor_set(v_reuseFailAlloc_706_, 6, v_extraDepTargets_697_);
lean_ctor_set(v_reuseFailAlloc_706_, 7, v_defaultFacets_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 8, v_val_688_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*9, v_libPrefixOnWindows_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*9 + 1, v_precompileModules_698_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*9 + 2, v_allowImportAll_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__2(lean_object* v_f_709_, lean_object* v_cfg_710_){
_start:
{
lean_object* v_toLeanConfig_711_; lean_object* v_srcDir_712_; lean_object* v_roots_713_; lean_object* v_globs_714_; lean_object* v_libName_715_; uint8_t v_libPrefixOnWindows_716_; lean_object* v_needs_717_; lean_object* v_extraDepTargets_718_; uint8_t v_precompileModules_719_; lean_object* v_defaultFacets_720_; lean_object* v_nativeFacets_721_; uint8_t v_allowImportAll_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
v_toLeanConfig_711_ = lean_ctor_get(v_cfg_710_, 0);
v_srcDir_712_ = lean_ctor_get(v_cfg_710_, 1);
v_roots_713_ = lean_ctor_get(v_cfg_710_, 2);
v_globs_714_ = lean_ctor_get(v_cfg_710_, 3);
v_libName_715_ = lean_ctor_get(v_cfg_710_, 4);
v_libPrefixOnWindows_716_ = lean_ctor_get_uint8(v_cfg_710_, sizeof(void*)*9);
v_needs_717_ = lean_ctor_get(v_cfg_710_, 5);
v_extraDepTargets_718_ = lean_ctor_get(v_cfg_710_, 6);
v_precompileModules_719_ = lean_ctor_get_uint8(v_cfg_710_, sizeof(void*)*9 + 1);
v_defaultFacets_720_ = lean_ctor_get(v_cfg_710_, 7);
v_nativeFacets_721_ = lean_ctor_get(v_cfg_710_, 8);
v_allowImportAll_722_ = lean_ctor_get_uint8(v_cfg_710_, sizeof(void*)*9 + 2);
v_isSharedCheck_730_ = !lean_is_exclusive(v_cfg_710_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v_cfg_710_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_nativeFacets_721_);
lean_inc(v_defaultFacets_720_);
lean_inc(v_extraDepTargets_718_);
lean_inc(v_needs_717_);
lean_inc(v_libName_715_);
lean_inc(v_globs_714_);
lean_inc(v_roots_713_);
lean_inc(v_srcDir_712_);
lean_inc(v_toLeanConfig_711_);
lean_dec(v_cfg_710_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_apply_1(v_f_709_, v_nativeFacets_721_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 8, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_toLeanConfig_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_srcDir_712_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_roots_713_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_globs_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_libName_715_);
lean_ctor_set(v_reuseFailAlloc_729_, 5, v_needs_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 6, v_extraDepTargets_718_);
lean_ctor_set(v_reuseFailAlloc_729_, 7, v_defaultFacets_720_);
lean_ctor_set(v_reuseFailAlloc_729_, 8, v___x_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*9, v_libPrefixOnWindows_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*9 + 1, v_precompileModules_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*9 + 2, v_allowImportAll_722_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(lean_object* v_x_731_, uint8_t v___y_732_){
_start:
{
lean_object* v___y_734_; 
if (v___y_732_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = l_Lake_Module_oFacet;
v___y_734_ = v___x_738_;
goto v___jp_733_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Lake_Module_oExportFacet;
v___y_734_ = v___x_739_;
goto v___jp_733_;
}
v___jp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_mk_empty_array_with_capacity(v___x_735_);
lean_inc(v___y_734_);
v___x_737_ = lean_array_push(v___x_736_, v___y_734_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed(lean_object* v_x_740_, lean_object* v___y_741_){
_start:
{
uint8_t v___y_197__boxed_742_; lean_object* v_res_743_; 
v___y_197__boxed_742_ = lean_unbox(v___y_741_);
v_res_743_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(v_x_740_, v___y_197__boxed_742_);
lean_dec_ref(v_x_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object* v_name_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Lake_LeanLibConfig_nativeFacets___proj___closed__4));
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object* v_name_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_755_);
lean_dec(v_name_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object* v_name_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object* v_name_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_759_);
lean_dec(v_name_759_);
return v_res_760_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_761_){
_start:
{
uint8_t v_allowImportAll_762_; 
v_allowImportAll_762_ = lean_ctor_get_uint8(v_cfg_761_, sizeof(void*)*9 + 2);
return v_allowImportAll_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(v_cfg_763_);
lean_dec_ref(v_cfg_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(uint8_t v_val_766_, lean_object* v_cfg_767_){
_start:
{
lean_object* v_toLeanConfig_768_; lean_object* v_srcDir_769_; lean_object* v_roots_770_; lean_object* v_globs_771_; lean_object* v_libName_772_; uint8_t v_libPrefixOnWindows_773_; lean_object* v_needs_774_; lean_object* v_extraDepTargets_775_; uint8_t v_precompileModules_776_; lean_object* v_defaultFacets_777_; lean_object* v_nativeFacets_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_toLeanConfig_768_ = lean_ctor_get(v_cfg_767_, 0);
v_srcDir_769_ = lean_ctor_get(v_cfg_767_, 1);
v_roots_770_ = lean_ctor_get(v_cfg_767_, 2);
v_globs_771_ = lean_ctor_get(v_cfg_767_, 3);
v_libName_772_ = lean_ctor_get(v_cfg_767_, 4);
v_libPrefixOnWindows_773_ = lean_ctor_get_uint8(v_cfg_767_, sizeof(void*)*9);
v_needs_774_ = lean_ctor_get(v_cfg_767_, 5);
v_extraDepTargets_775_ = lean_ctor_get(v_cfg_767_, 6);
v_precompileModules_776_ = lean_ctor_get_uint8(v_cfg_767_, sizeof(void*)*9 + 1);
v_defaultFacets_777_ = lean_ctor_get(v_cfg_767_, 7);
v_nativeFacets_778_ = lean_ctor_get(v_cfg_767_, 8);
v_isSharedCheck_785_ = !lean_is_exclusive(v_cfg_767_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v_cfg_767_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_nativeFacets_778_);
lean_inc(v_defaultFacets_777_);
lean_inc(v_extraDepTargets_775_);
lean_inc(v_needs_774_);
lean_inc(v_libName_772_);
lean_inc(v_globs_771_);
lean_inc(v_roots_770_);
lean_inc(v_srcDir_769_);
lean_inc(v_toLeanConfig_768_);
lean_dec(v_cfg_767_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_toLeanConfig_768_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_srcDir_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_roots_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_globs_771_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_libName_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_needs_774_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_extraDepTargets_775_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_defaultFacets_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_nativeFacets_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*9, v_libPrefixOnWindows_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*9 + 1, v_precompileModules_776_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*9 + 2, v_val_766_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_786_, lean_object* v_cfg_787_){
_start:
{
uint8_t v_val_71__boxed_788_; lean_object* v_res_789_; 
v_val_71__boxed_788_ = lean_unbox(v_val_786_);
v_res_789_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(v_val_71__boxed_788_, v_cfg_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__2(lean_object* v_f_790_, lean_object* v_cfg_791_){
_start:
{
lean_object* v_toLeanConfig_792_; lean_object* v_srcDir_793_; lean_object* v_roots_794_; lean_object* v_globs_795_; lean_object* v_libName_796_; uint8_t v_libPrefixOnWindows_797_; lean_object* v_needs_798_; lean_object* v_extraDepTargets_799_; uint8_t v_precompileModules_800_; lean_object* v_defaultFacets_801_; lean_object* v_nativeFacets_802_; uint8_t v_allowImportAll_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v_toLeanConfig_792_ = lean_ctor_get(v_cfg_791_, 0);
v_srcDir_793_ = lean_ctor_get(v_cfg_791_, 1);
v_roots_794_ = lean_ctor_get(v_cfg_791_, 2);
v_globs_795_ = lean_ctor_get(v_cfg_791_, 3);
v_libName_796_ = lean_ctor_get(v_cfg_791_, 4);
v_libPrefixOnWindows_797_ = lean_ctor_get_uint8(v_cfg_791_, sizeof(void*)*9);
v_needs_798_ = lean_ctor_get(v_cfg_791_, 5);
v_extraDepTargets_799_ = lean_ctor_get(v_cfg_791_, 6);
v_precompileModules_800_ = lean_ctor_get_uint8(v_cfg_791_, sizeof(void*)*9 + 1);
v_defaultFacets_801_ = lean_ctor_get(v_cfg_791_, 7);
v_nativeFacets_802_ = lean_ctor_get(v_cfg_791_, 8);
v_allowImportAll_803_ = lean_ctor_get_uint8(v_cfg_791_, sizeof(void*)*9 + 2);
v_isSharedCheck_813_ = !lean_is_exclusive(v_cfg_791_);
if (v_isSharedCheck_813_ == 0)
{
v___x_805_ = v_cfg_791_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_nativeFacets_802_);
lean_inc(v_defaultFacets_801_);
lean_inc(v_extraDepTargets_799_);
lean_inc(v_needs_798_);
lean_inc(v_libName_796_);
lean_inc(v_globs_795_);
lean_inc(v_roots_794_);
lean_inc(v_srcDir_793_);
lean_inc(v_toLeanConfig_792_);
lean_dec(v_cfg_791_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = lean_box(v_allowImportAll_803_);
v___x_808_ = lean_apply_1(v_f_790_, v___x_807_);
if (v_isShared_806_ == 0)
{
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_toLeanConfig_792_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_srcDir_793_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_roots_794_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_globs_795_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_libName_796_);
lean_ctor_set(v_reuseFailAlloc_812_, 5, v_needs_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 6, v_extraDepTargets_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 7, v_defaultFacets_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 8, v_nativeFacets_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*9, v_libPrefixOnWindows_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*9 + 1, v_precompileModules_800_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
uint8_t v___x_811_; 
v___x_811_ = lean_unbox(v___x_808_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*9 + 2, v___x_811_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object* v_name_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l_Lake_LeanLibConfig_allowImportAll___proj___closed__3));
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object* v_name_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_824_);
lean_dec(v_name_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object* v_name_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object* v_name_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_828_);
lean_dec(v_name_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_830_){
_start:
{
lean_object* v_toLeanConfig_831_; 
v_toLeanConfig_831_ = lean_ctor_get(v_cfg_830_, 0);
lean_inc_ref(v_toLeanConfig_831_);
return v_toLeanConfig_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(v_cfg_832_);
lean_dec_ref(v_cfg_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1(lean_object* v_val_834_, lean_object* v_cfg_835_){
_start:
{
lean_object* v_srcDir_836_; lean_object* v_roots_837_; lean_object* v_globs_838_; lean_object* v_libName_839_; uint8_t v_libPrefixOnWindows_840_; lean_object* v_needs_841_; lean_object* v_extraDepTargets_842_; uint8_t v_precompileModules_843_; lean_object* v_defaultFacets_844_; lean_object* v_nativeFacets_845_; uint8_t v_allowImportAll_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_srcDir_836_ = lean_ctor_get(v_cfg_835_, 1);
v_roots_837_ = lean_ctor_get(v_cfg_835_, 2);
v_globs_838_ = lean_ctor_get(v_cfg_835_, 3);
v_libName_839_ = lean_ctor_get(v_cfg_835_, 4);
v_libPrefixOnWindows_840_ = lean_ctor_get_uint8(v_cfg_835_, sizeof(void*)*9);
v_needs_841_ = lean_ctor_get(v_cfg_835_, 5);
v_extraDepTargets_842_ = lean_ctor_get(v_cfg_835_, 6);
v_precompileModules_843_ = lean_ctor_get_uint8(v_cfg_835_, sizeof(void*)*9 + 1);
v_defaultFacets_844_ = lean_ctor_get(v_cfg_835_, 7);
v_nativeFacets_845_ = lean_ctor_get(v_cfg_835_, 8);
v_allowImportAll_846_ = lean_ctor_get_uint8(v_cfg_835_, sizeof(void*)*9 + 2);
v_isSharedCheck_853_ = !lean_is_exclusive(v_cfg_835_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_cfg_835_, 0);
lean_dec(v_unused_854_);
v___x_848_ = v_cfg_835_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_nativeFacets_845_);
lean_inc(v_defaultFacets_844_);
lean_inc(v_extraDepTargets_842_);
lean_inc(v_needs_841_);
lean_inc(v_libName_839_);
lean_inc(v_globs_838_);
lean_inc(v_roots_837_);
lean_inc(v_srcDir_836_);
lean_dec(v_cfg_835_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_val_834_);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_val_834_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_srcDir_836_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_roots_837_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_globs_838_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v_libName_839_);
lean_ctor_set(v_reuseFailAlloc_852_, 5, v_needs_841_);
lean_ctor_set(v_reuseFailAlloc_852_, 6, v_extraDepTargets_842_);
lean_ctor_set(v_reuseFailAlloc_852_, 7, v_defaultFacets_844_);
lean_ctor_set(v_reuseFailAlloc_852_, 8, v_nativeFacets_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*9, v_libPrefixOnWindows_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*9 + 1, v_precompileModules_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*9 + 2, v_allowImportAll_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2(lean_object* v_f_855_, lean_object* v_cfg_856_){
_start:
{
lean_object* v_toLeanConfig_857_; lean_object* v_srcDir_858_; lean_object* v_roots_859_; lean_object* v_globs_860_; lean_object* v_libName_861_; uint8_t v_libPrefixOnWindows_862_; lean_object* v_needs_863_; lean_object* v_extraDepTargets_864_; uint8_t v_precompileModules_865_; lean_object* v_defaultFacets_866_; lean_object* v_nativeFacets_867_; uint8_t v_allowImportAll_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_toLeanConfig_857_ = lean_ctor_get(v_cfg_856_, 0);
v_srcDir_858_ = lean_ctor_get(v_cfg_856_, 1);
v_roots_859_ = lean_ctor_get(v_cfg_856_, 2);
v_globs_860_ = lean_ctor_get(v_cfg_856_, 3);
v_libName_861_ = lean_ctor_get(v_cfg_856_, 4);
v_libPrefixOnWindows_862_ = lean_ctor_get_uint8(v_cfg_856_, sizeof(void*)*9);
v_needs_863_ = lean_ctor_get(v_cfg_856_, 5);
v_extraDepTargets_864_ = lean_ctor_get(v_cfg_856_, 6);
v_precompileModules_865_ = lean_ctor_get_uint8(v_cfg_856_, sizeof(void*)*9 + 1);
v_defaultFacets_866_ = lean_ctor_get(v_cfg_856_, 7);
v_nativeFacets_867_ = lean_ctor_get(v_cfg_856_, 8);
v_allowImportAll_868_ = lean_ctor_get_uint8(v_cfg_856_, sizeof(void*)*9 + 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_cfg_856_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v_cfg_856_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_nativeFacets_867_);
lean_inc(v_defaultFacets_866_);
lean_inc(v_extraDepTargets_864_);
lean_inc(v_needs_863_);
lean_inc(v_libName_861_);
lean_inc(v_globs_860_);
lean_inc(v_roots_859_);
lean_inc(v_srcDir_858_);
lean_inc(v_toLeanConfig_857_);
lean_dec(v_cfg_856_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_apply_1(v_f_855_, v_toLeanConfig_857_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_srcDir_858_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_roots_859_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_globs_860_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_libName_861_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_needs_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 6, v_extraDepTargets_864_);
lean_ctor_set(v_reuseFailAlloc_875_, 7, v_defaultFacets_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 8, v_nativeFacets_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*9, v_libPrefixOnWindows_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*9 + 1, v_precompileModules_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*9 + 2, v_allowImportAll_868_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1));
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
v___x_1091_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_1092_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_1093_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_mk_empty_array_with_capacity(v___x_1094_);
v___x_1096_ = lean_array_push(v___x_1095_, v_name_1088_);
v___x_1097_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v_sz_1098_ = lean_array_size(v___x_1096_);
v___x_1099_ = ((size_t)0ULL);
lean_inc_ref(v___x_1096_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1097_, v___f_1089_, v_sz_1098_, v___x_1099_, v___x_1096_);
v___x_1101_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_1102_ = 0;
v___x_1103_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
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
