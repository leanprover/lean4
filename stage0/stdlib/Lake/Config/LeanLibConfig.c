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
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileLibrary___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileLibrary___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileLibrary___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileLibrary___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileLibrary___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileLibrary___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig_precompileLibrary___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___boxed(lean_object*);
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
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileLibrary"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__29 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__29_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__29_value),LEAN_SCALAR_PTR_LITERAL(71, 18, 27, 24, 108, 72, 213, 250)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__30 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__30_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__30_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__30_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__31 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__31_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__32;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileModules"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__33 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__33_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__33_value),LEAN_SCALAR_PTR_LITERAL(210, 72, 98, 56, 225, 29, 247, 45)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__34 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__34_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__34_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__34_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__35 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__35_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__36;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "defaultFacets"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__37 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__37_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__37_value),LEAN_SCALAR_PTR_LITERAL(74, 73, 74, 204, 169, 19, 96, 134)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__38 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__38_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__38_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__38_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__39 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__39_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__40;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeFacets"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__41 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__41_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__41_value),LEAN_SCALAR_PTR_LITERAL(130, 15, 19, 239, 40, 85, 158, 29)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__42 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__42_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__42_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__42_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__43 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__43_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__44;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__45 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__45_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__45_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__46 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__46_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__46_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__46_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__47 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__47_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__48;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__49;
static const lean_string_object l_Lake_LeanLibConfig___fields___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__50 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__50_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__50_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__51 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__51_value;
static const lean_ctor_object l_Lake_LeanLibConfig___fields___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig___fields___closed__51_value),((lean_object*)&l_Lake_LeanLibConfig___fields___closed__51_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig___fields___closed__52 = (const lean_object*)&l_Lake_LeanLibConfig___fields___closed__52_value;
static lean_once_cell_t l_Lake_LeanLibConfig___fields___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig___fields___closed__53;
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
v___x_53_ = lean_alloc_ctor(0, 9, 4);
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
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*9 + 3, v___x_50_);
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
lean_object* v_toLeanConfig_62_; lean_object* v_roots_63_; lean_object* v_globs_64_; lean_object* v_libName_65_; uint8_t v_libPrefixOnWindows_66_; lean_object* v_needs_67_; lean_object* v_extraDepTargets_68_; uint8_t v_precompileLibrary_69_; uint8_t v_precompileModules_70_; lean_object* v_defaultFacets_71_; lean_object* v_nativeFacets_72_; uint8_t v_allowImportAll_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_toLeanConfig_62_ = lean_ctor_get(v_cfg_61_, 0);
v_roots_63_ = lean_ctor_get(v_cfg_61_, 2);
v_globs_64_ = lean_ctor_get(v_cfg_61_, 3);
v_libName_65_ = lean_ctor_get(v_cfg_61_, 4);
v_libPrefixOnWindows_66_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9);
v_needs_67_ = lean_ctor_get(v_cfg_61_, 5);
v_extraDepTargets_68_ = lean_ctor_get(v_cfg_61_, 6);
v_precompileLibrary_69_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9 + 1);
v_precompileModules_70_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9 + 2);
v_defaultFacets_71_ = lean_ctor_get(v_cfg_61_, 7);
v_nativeFacets_72_ = lean_ctor_get(v_cfg_61_, 8);
v_allowImportAll_73_ = lean_ctor_get_uint8(v_cfg_61_, sizeof(void*)*9 + 3);
v_isSharedCheck_80_ = !lean_is_exclusive(v_cfg_61_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v_cfg_61_, 1);
lean_dec(v_unused_81_);
v___x_75_ = v_cfg_61_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_nativeFacets_72_);
lean_inc(v_defaultFacets_71_);
lean_inc(v_extraDepTargets_68_);
lean_inc(v_needs_67_);
lean_inc(v_libName_65_);
lean_inc(v_globs_64_);
lean_inc(v_roots_63_);
lean_inc(v_toLeanConfig_62_);
lean_dec(v_cfg_61_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_val_60_);
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_toLeanConfig_62_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_val_60_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_roots_63_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_globs_64_);
lean_ctor_set(v_reuseFailAlloc_79_, 4, v_libName_65_);
lean_ctor_set(v_reuseFailAlloc_79_, 5, v_needs_67_);
lean_ctor_set(v_reuseFailAlloc_79_, 6, v_extraDepTargets_68_);
lean_ctor_set(v_reuseFailAlloc_79_, 7, v_defaultFacets_71_);
lean_ctor_set(v_reuseFailAlloc_79_, 8, v_nativeFacets_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*9, v_libPrefixOnWindows_66_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*9 + 1, v_precompileLibrary_69_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*9 + 2, v_precompileModules_70_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*9 + 3, v_allowImportAll_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__2(lean_object* v_f_82_, lean_object* v_cfg_83_){
_start:
{
lean_object* v_toLeanConfig_84_; lean_object* v_srcDir_85_; lean_object* v_roots_86_; lean_object* v_globs_87_; lean_object* v_libName_88_; uint8_t v_libPrefixOnWindows_89_; lean_object* v_needs_90_; lean_object* v_extraDepTargets_91_; uint8_t v_precompileLibrary_92_; uint8_t v_precompileModules_93_; lean_object* v_defaultFacets_94_; lean_object* v_nativeFacets_95_; uint8_t v_allowImportAll_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_toLeanConfig_84_ = lean_ctor_get(v_cfg_83_, 0);
v_srcDir_85_ = lean_ctor_get(v_cfg_83_, 1);
v_roots_86_ = lean_ctor_get(v_cfg_83_, 2);
v_globs_87_ = lean_ctor_get(v_cfg_83_, 3);
v_libName_88_ = lean_ctor_get(v_cfg_83_, 4);
v_libPrefixOnWindows_89_ = lean_ctor_get_uint8(v_cfg_83_, sizeof(void*)*9);
v_needs_90_ = lean_ctor_get(v_cfg_83_, 5);
v_extraDepTargets_91_ = lean_ctor_get(v_cfg_83_, 6);
v_precompileLibrary_92_ = lean_ctor_get_uint8(v_cfg_83_, sizeof(void*)*9 + 1);
v_precompileModules_93_ = lean_ctor_get_uint8(v_cfg_83_, sizeof(void*)*9 + 2);
v_defaultFacets_94_ = lean_ctor_get(v_cfg_83_, 7);
v_nativeFacets_95_ = lean_ctor_get(v_cfg_83_, 8);
v_allowImportAll_96_ = lean_ctor_get_uint8(v_cfg_83_, sizeof(void*)*9 + 3);
v_isSharedCheck_104_ = !lean_is_exclusive(v_cfg_83_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v_cfg_83_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_nativeFacets_95_);
lean_inc(v_defaultFacets_94_);
lean_inc(v_extraDepTargets_91_);
lean_inc(v_needs_90_);
lean_inc(v_libName_88_);
lean_inc(v_globs_87_);
lean_inc(v_roots_86_);
lean_inc(v_srcDir_85_);
lean_inc(v_toLeanConfig_84_);
lean_dec(v_cfg_83_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_apply_1(v_f_82_, v_srcDir_85_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_toLeanConfig_84_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_roots_86_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_globs_87_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v_libName_88_);
lean_ctor_set(v_reuseFailAlloc_103_, 5, v_needs_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 6, v_extraDepTargets_91_);
lean_ctor_set(v_reuseFailAlloc_103_, 7, v_defaultFacets_94_);
lean_ctor_set(v_reuseFailAlloc_103_, 8, v_nativeFacets_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*9, v_libPrefixOnWindows_89_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*9 + 1, v_precompileLibrary_92_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*9 + 2, v_precompileModules_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*9 + 3, v_allowImportAll_96_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3(lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lake_LeanLibConfig_srcDir___proj___lam__3(v_x_107_);
lean_dec_ref(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object* v_name_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___closed__4));
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object* v_name_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_120_);
lean_dec(v_name_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object* v_name_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object* v_name_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_124_);
lean_dec(v_name_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object* v_cfg_126_){
_start:
{
lean_object* v_roots_127_; 
v_roots_127_ = lean_ctor_get(v_cfg_126_, 2);
lean_inc_ref(v_roots_127_);
return v_roots_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object* v_cfg_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_128_);
lean_dec_ref(v_cfg_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object* v_val_130_, lean_object* v_cfg_131_){
_start:
{
lean_object* v_toLeanConfig_132_; lean_object* v_srcDir_133_; lean_object* v_globs_134_; lean_object* v_libName_135_; uint8_t v_libPrefixOnWindows_136_; lean_object* v_needs_137_; lean_object* v_extraDepTargets_138_; uint8_t v_precompileLibrary_139_; uint8_t v_precompileModules_140_; lean_object* v_defaultFacets_141_; lean_object* v_nativeFacets_142_; uint8_t v_allowImportAll_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_toLeanConfig_132_ = lean_ctor_get(v_cfg_131_, 0);
v_srcDir_133_ = lean_ctor_get(v_cfg_131_, 1);
v_globs_134_ = lean_ctor_get(v_cfg_131_, 3);
v_libName_135_ = lean_ctor_get(v_cfg_131_, 4);
v_libPrefixOnWindows_136_ = lean_ctor_get_uint8(v_cfg_131_, sizeof(void*)*9);
v_needs_137_ = lean_ctor_get(v_cfg_131_, 5);
v_extraDepTargets_138_ = lean_ctor_get(v_cfg_131_, 6);
v_precompileLibrary_139_ = lean_ctor_get_uint8(v_cfg_131_, sizeof(void*)*9 + 1);
v_precompileModules_140_ = lean_ctor_get_uint8(v_cfg_131_, sizeof(void*)*9 + 2);
v_defaultFacets_141_ = lean_ctor_get(v_cfg_131_, 7);
v_nativeFacets_142_ = lean_ctor_get(v_cfg_131_, 8);
v_allowImportAll_143_ = lean_ctor_get_uint8(v_cfg_131_, sizeof(void*)*9 + 3);
v_isSharedCheck_150_ = !lean_is_exclusive(v_cfg_131_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v_cfg_131_, 2);
lean_dec(v_unused_151_);
v___x_145_ = v_cfg_131_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_nativeFacets_142_);
lean_inc(v_defaultFacets_141_);
lean_inc(v_extraDepTargets_138_);
lean_inc(v_needs_137_);
lean_inc(v_libName_135_);
lean_inc(v_globs_134_);
lean_inc(v_srcDir_133_);
lean_inc(v_toLeanConfig_132_);
lean_dec(v_cfg_131_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 2, v_val_130_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_toLeanConfig_132_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_srcDir_133_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_val_130_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_globs_134_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v_libName_135_);
lean_ctor_set(v_reuseFailAlloc_149_, 5, v_needs_137_);
lean_ctor_set(v_reuseFailAlloc_149_, 6, v_extraDepTargets_138_);
lean_ctor_set(v_reuseFailAlloc_149_, 7, v_defaultFacets_141_);
lean_ctor_set(v_reuseFailAlloc_149_, 8, v_nativeFacets_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_149_, sizeof(void*)*9, v_libPrefixOnWindows_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_149_, sizeof(void*)*9 + 1, v_precompileLibrary_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_149_, sizeof(void*)*9 + 2, v_precompileModules_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_149_, sizeof(void*)*9 + 3, v_allowImportAll_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object* v_f_152_, lean_object* v_cfg_153_){
_start:
{
lean_object* v_toLeanConfig_154_; lean_object* v_srcDir_155_; lean_object* v_roots_156_; lean_object* v_globs_157_; lean_object* v_libName_158_; uint8_t v_libPrefixOnWindows_159_; lean_object* v_needs_160_; lean_object* v_extraDepTargets_161_; uint8_t v_precompileLibrary_162_; uint8_t v_precompileModules_163_; lean_object* v_defaultFacets_164_; lean_object* v_nativeFacets_165_; uint8_t v_allowImportAll_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_174_; 
v_toLeanConfig_154_ = lean_ctor_get(v_cfg_153_, 0);
v_srcDir_155_ = lean_ctor_get(v_cfg_153_, 1);
v_roots_156_ = lean_ctor_get(v_cfg_153_, 2);
v_globs_157_ = lean_ctor_get(v_cfg_153_, 3);
v_libName_158_ = lean_ctor_get(v_cfg_153_, 4);
v_libPrefixOnWindows_159_ = lean_ctor_get_uint8(v_cfg_153_, sizeof(void*)*9);
v_needs_160_ = lean_ctor_get(v_cfg_153_, 5);
v_extraDepTargets_161_ = lean_ctor_get(v_cfg_153_, 6);
v_precompileLibrary_162_ = lean_ctor_get_uint8(v_cfg_153_, sizeof(void*)*9 + 1);
v_precompileModules_163_ = lean_ctor_get_uint8(v_cfg_153_, sizeof(void*)*9 + 2);
v_defaultFacets_164_ = lean_ctor_get(v_cfg_153_, 7);
v_nativeFacets_165_ = lean_ctor_get(v_cfg_153_, 8);
v_allowImportAll_166_ = lean_ctor_get_uint8(v_cfg_153_, sizeof(void*)*9 + 3);
v_isSharedCheck_174_ = !lean_is_exclusive(v_cfg_153_);
if (v_isSharedCheck_174_ == 0)
{
v___x_168_ = v_cfg_153_;
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_nativeFacets_165_);
lean_inc(v_defaultFacets_164_);
lean_inc(v_extraDepTargets_161_);
lean_inc(v_needs_160_);
lean_inc(v_libName_158_);
lean_inc(v_globs_157_);
lean_inc(v_roots_156_);
lean_inc(v_srcDir_155_);
lean_inc(v_toLeanConfig_154_);
lean_dec(v_cfg_153_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_apply_1(v_f_152_, v_roots_156_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 2, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_toLeanConfig_154_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_srcDir_155_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_globs_157_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_libName_158_);
lean_ctor_set(v_reuseFailAlloc_173_, 5, v_needs_160_);
lean_ctor_set(v_reuseFailAlloc_173_, 6, v_extraDepTargets_161_);
lean_ctor_set(v_reuseFailAlloc_173_, 7, v_defaultFacets_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 8, v_nativeFacets_165_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*9, v_libPrefixOnWindows_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*9 + 1, v_precompileLibrary_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*9 + 2, v_precompileModules_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*9 + 3, v_allowImportAll_166_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object* v_name_175_, lean_object* v_x_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_179_ = lean_array_push(v___x_178_, v_name_175_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object* v_name_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_180_, v_x_181_);
lean_dec_ref(v_x_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object* v_name_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; 
v___f_187_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__0));
v___f_188_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__1));
v___f_189_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__2));
v___f_190_ = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_roots___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_190_, 0, v_name_186_);
v___x_191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_191_, 0, v___f_187_);
lean_ctor_set(v___x_191_, 1, v___f_188_);
lean_ctor_set(v___x_191_, 2, v___f_189_);
lean_ctor_set(v___x_191_, 3, v___f_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object* v_name_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lake_LeanLibConfig_roots___proj(v_name_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0(lean_object* v_cfg_194_){
_start:
{
lean_object* v_globs_195_; 
v_globs_195_ = lean_ctor_get(v_cfg_194_, 3);
lean_inc_ref(v_globs_195_);
return v_globs_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__0___boxed(lean_object* v_cfg_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lake_LeanLibConfig_globs___proj___lam__0(v_cfg_196_);
lean_dec_ref(v_cfg_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__1(lean_object* v_val_198_, lean_object* v_cfg_199_){
_start:
{
lean_object* v_toLeanConfig_200_; lean_object* v_srcDir_201_; lean_object* v_roots_202_; lean_object* v_libName_203_; uint8_t v_libPrefixOnWindows_204_; lean_object* v_needs_205_; lean_object* v_extraDepTargets_206_; uint8_t v_precompileLibrary_207_; uint8_t v_precompileModules_208_; lean_object* v_defaultFacets_209_; lean_object* v_nativeFacets_210_; uint8_t v_allowImportAll_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_toLeanConfig_200_ = lean_ctor_get(v_cfg_199_, 0);
v_srcDir_201_ = lean_ctor_get(v_cfg_199_, 1);
v_roots_202_ = lean_ctor_get(v_cfg_199_, 2);
v_libName_203_ = lean_ctor_get(v_cfg_199_, 4);
v_libPrefixOnWindows_204_ = lean_ctor_get_uint8(v_cfg_199_, sizeof(void*)*9);
v_needs_205_ = lean_ctor_get(v_cfg_199_, 5);
v_extraDepTargets_206_ = lean_ctor_get(v_cfg_199_, 6);
v_precompileLibrary_207_ = lean_ctor_get_uint8(v_cfg_199_, sizeof(void*)*9 + 1);
v_precompileModules_208_ = lean_ctor_get_uint8(v_cfg_199_, sizeof(void*)*9 + 2);
v_defaultFacets_209_ = lean_ctor_get(v_cfg_199_, 7);
v_nativeFacets_210_ = lean_ctor_get(v_cfg_199_, 8);
v_allowImportAll_211_ = lean_ctor_get_uint8(v_cfg_199_, sizeof(void*)*9 + 3);
v_isSharedCheck_218_ = !lean_is_exclusive(v_cfg_199_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_cfg_199_, 3);
lean_dec(v_unused_219_);
v___x_213_ = v_cfg_199_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_nativeFacets_210_);
lean_inc(v_defaultFacets_209_);
lean_inc(v_extraDepTargets_206_);
lean_inc(v_needs_205_);
lean_inc(v_libName_203_);
lean_inc(v_roots_202_);
lean_inc(v_srcDir_201_);
lean_inc(v_toLeanConfig_200_);
lean_dec(v_cfg_199_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v_val_198_);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_toLeanConfig_200_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_srcDir_201_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_roots_202_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_val_198_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_libName_203_);
lean_ctor_set(v_reuseFailAlloc_217_, 5, v_needs_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 6, v_extraDepTargets_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 7, v_defaultFacets_209_);
lean_ctor_set(v_reuseFailAlloc_217_, 8, v_nativeFacets_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9, v_libPrefixOnWindows_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9 + 1, v_precompileLibrary_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9 + 2, v_precompileModules_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*9 + 3, v_allowImportAll_211_);
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
lean_object* v_toLeanConfig_222_; lean_object* v_srcDir_223_; lean_object* v_roots_224_; lean_object* v_globs_225_; lean_object* v_libName_226_; uint8_t v_libPrefixOnWindows_227_; lean_object* v_needs_228_; lean_object* v_extraDepTargets_229_; uint8_t v_precompileLibrary_230_; uint8_t v_precompileModules_231_; lean_object* v_defaultFacets_232_; lean_object* v_nativeFacets_233_; uint8_t v_allowImportAll_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_toLeanConfig_222_ = lean_ctor_get(v_cfg_221_, 0);
v_srcDir_223_ = lean_ctor_get(v_cfg_221_, 1);
v_roots_224_ = lean_ctor_get(v_cfg_221_, 2);
v_globs_225_ = lean_ctor_get(v_cfg_221_, 3);
v_libName_226_ = lean_ctor_get(v_cfg_221_, 4);
v_libPrefixOnWindows_227_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9);
v_needs_228_ = lean_ctor_get(v_cfg_221_, 5);
v_extraDepTargets_229_ = lean_ctor_get(v_cfg_221_, 6);
v_precompileLibrary_230_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9 + 1);
v_precompileModules_231_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9 + 2);
v_defaultFacets_232_ = lean_ctor_get(v_cfg_221_, 7);
v_nativeFacets_233_ = lean_ctor_get(v_cfg_221_, 8);
v_allowImportAll_234_ = lean_ctor_get_uint8(v_cfg_221_, sizeof(void*)*9 + 3);
v_isSharedCheck_242_ = !lean_is_exclusive(v_cfg_221_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v_cfg_221_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_nativeFacets_233_);
lean_inc(v_defaultFacets_232_);
lean_inc(v_extraDepTargets_229_);
lean_inc(v_needs_228_);
lean_inc(v_libName_226_);
lean_inc(v_globs_225_);
lean_inc(v_roots_224_);
lean_inc(v_srcDir_223_);
lean_inc(v_toLeanConfig_222_);
lean_dec(v_cfg_221_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_apply_1(v_f_220_, v_globs_225_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 3, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_toLeanConfig_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_srcDir_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_roots_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_libName_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_needs_228_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_extraDepTargets_229_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v_defaultFacets_232_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v_nativeFacets_233_);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, sizeof(void*)*9, v_libPrefixOnWindows_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, sizeof(void*)*9 + 1, v_precompileLibrary_230_);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, sizeof(void*)*9 + 2, v_precompileModules_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, sizeof(void*)*9 + 3, v_allowImportAll_234_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___lam__3(lean_object* v_x_243_){
_start:
{
lean_object* v_roots_244_; size_t v_sz_245_; size_t v___x_246_; lean_object* v___x_247_; 
v_roots_244_ = lean_ctor_get(v_x_243_, 2);
lean_inc_ref(v_roots_244_);
lean_dec_ref(v_x_243_);
v_sz_245_ = lean_array_size(v_roots_244_);
v___x_246_ = ((size_t)0ULL);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_245_, v___x_246_, v_roots_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object* v_name_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = ((lean_object*)(l_Lake_LeanLibConfig_globs___proj___closed__4));
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object* v_name_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lake_LeanLibConfig_globs___proj(v_name_259_);
lean_dec(v_name_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object* v_name_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lake_LeanLibConfig_globs___proj(v_name_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object* v_name_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_263_);
lean_dec(v_name_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0(lean_object* v_cfg_265_){
_start:
{
lean_object* v_libName_266_; 
v_libName_266_ = lean_ctor_get(v_cfg_265_, 4);
lean_inc_ref(v_libName_266_);
return v_libName_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__0___boxed(lean_object* v_cfg_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lake_LeanLibConfig_libName___proj___lam__0(v_cfg_267_);
lean_dec_ref(v_cfg_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__1(lean_object* v_val_269_, lean_object* v_cfg_270_){
_start:
{
lean_object* v_toLeanConfig_271_; lean_object* v_srcDir_272_; lean_object* v_roots_273_; lean_object* v_globs_274_; uint8_t v_libPrefixOnWindows_275_; lean_object* v_needs_276_; lean_object* v_extraDepTargets_277_; uint8_t v_precompileLibrary_278_; uint8_t v_precompileModules_279_; lean_object* v_defaultFacets_280_; lean_object* v_nativeFacets_281_; uint8_t v_allowImportAll_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_toLeanConfig_271_ = lean_ctor_get(v_cfg_270_, 0);
v_srcDir_272_ = lean_ctor_get(v_cfg_270_, 1);
v_roots_273_ = lean_ctor_get(v_cfg_270_, 2);
v_globs_274_ = lean_ctor_get(v_cfg_270_, 3);
v_libPrefixOnWindows_275_ = lean_ctor_get_uint8(v_cfg_270_, sizeof(void*)*9);
v_needs_276_ = lean_ctor_get(v_cfg_270_, 5);
v_extraDepTargets_277_ = lean_ctor_get(v_cfg_270_, 6);
v_precompileLibrary_278_ = lean_ctor_get_uint8(v_cfg_270_, sizeof(void*)*9 + 1);
v_precompileModules_279_ = lean_ctor_get_uint8(v_cfg_270_, sizeof(void*)*9 + 2);
v_defaultFacets_280_ = lean_ctor_get(v_cfg_270_, 7);
v_nativeFacets_281_ = lean_ctor_get(v_cfg_270_, 8);
v_allowImportAll_282_ = lean_ctor_get_uint8(v_cfg_270_, sizeof(void*)*9 + 3);
v_isSharedCheck_289_ = !lean_is_exclusive(v_cfg_270_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v_cfg_270_, 4);
lean_dec(v_unused_290_);
v___x_284_ = v_cfg_270_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_nativeFacets_281_);
lean_inc(v_defaultFacets_280_);
lean_inc(v_extraDepTargets_277_);
lean_inc(v_needs_276_);
lean_inc(v_globs_274_);
lean_inc(v_roots_273_);
lean_inc(v_srcDir_272_);
lean_inc(v_toLeanConfig_271_);
lean_dec(v_cfg_270_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 4, v_val_269_);
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_toLeanConfig_271_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_srcDir_272_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_roots_273_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_globs_274_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_val_269_);
lean_ctor_set(v_reuseFailAlloc_288_, 5, v_needs_276_);
lean_ctor_set(v_reuseFailAlloc_288_, 6, v_extraDepTargets_277_);
lean_ctor_set(v_reuseFailAlloc_288_, 7, v_defaultFacets_280_);
lean_ctor_set(v_reuseFailAlloc_288_, 8, v_nativeFacets_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*9, v_libPrefixOnWindows_275_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*9 + 1, v_precompileLibrary_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*9 + 2, v_precompileModules_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*9 + 3, v_allowImportAll_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__2(lean_object* v_f_291_, lean_object* v_cfg_292_){
_start:
{
lean_object* v_toLeanConfig_293_; lean_object* v_srcDir_294_; lean_object* v_roots_295_; lean_object* v_globs_296_; lean_object* v_libName_297_; uint8_t v_libPrefixOnWindows_298_; lean_object* v_needs_299_; lean_object* v_extraDepTargets_300_; uint8_t v_precompileLibrary_301_; uint8_t v_precompileModules_302_; lean_object* v_defaultFacets_303_; lean_object* v_nativeFacets_304_; uint8_t v_allowImportAll_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v_toLeanConfig_293_ = lean_ctor_get(v_cfg_292_, 0);
v_srcDir_294_ = lean_ctor_get(v_cfg_292_, 1);
v_roots_295_ = lean_ctor_get(v_cfg_292_, 2);
v_globs_296_ = lean_ctor_get(v_cfg_292_, 3);
v_libName_297_ = lean_ctor_get(v_cfg_292_, 4);
v_libPrefixOnWindows_298_ = lean_ctor_get_uint8(v_cfg_292_, sizeof(void*)*9);
v_needs_299_ = lean_ctor_get(v_cfg_292_, 5);
v_extraDepTargets_300_ = lean_ctor_get(v_cfg_292_, 6);
v_precompileLibrary_301_ = lean_ctor_get_uint8(v_cfg_292_, sizeof(void*)*9 + 1);
v_precompileModules_302_ = lean_ctor_get_uint8(v_cfg_292_, sizeof(void*)*9 + 2);
v_defaultFacets_303_ = lean_ctor_get(v_cfg_292_, 7);
v_nativeFacets_304_ = lean_ctor_get(v_cfg_292_, 8);
v_allowImportAll_305_ = lean_ctor_get_uint8(v_cfg_292_, sizeof(void*)*9 + 3);
v_isSharedCheck_313_ = !lean_is_exclusive(v_cfg_292_);
if (v_isSharedCheck_313_ == 0)
{
v___x_307_ = v_cfg_292_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_nativeFacets_304_);
lean_inc(v_defaultFacets_303_);
lean_inc(v_extraDepTargets_300_);
lean_inc(v_needs_299_);
lean_inc(v_libName_297_);
lean_inc(v_globs_296_);
lean_inc(v_roots_295_);
lean_inc(v_srcDir_294_);
lean_inc(v_toLeanConfig_293_);
lean_dec(v_cfg_292_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_apply_1(v_f_291_, v_libName_297_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 4, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_toLeanConfig_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_srcDir_294_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_roots_295_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_globs_296_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_needs_299_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_extraDepTargets_300_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_defaultFacets_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_nativeFacets_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9, v_libPrefixOnWindows_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9 + 1, v_precompileLibrary_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9 + 2, v_precompileModules_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9 + 3, v_allowImportAll_305_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3(lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___lam__3___boxed(lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lake_LeanLibConfig_libName___proj___lam__3(v_x_316_);
lean_dec_ref(v_x_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object* v_name_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l_Lake_LeanLibConfig_libName___proj___closed__4));
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object* v_name_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lake_LeanLibConfig_libName___proj(v_name_329_);
lean_dec(v_name_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object* v_name_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lake_LeanLibConfig_libName___proj(v_name_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object* v_name_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_333_);
lean_dec(v_name_333_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_335_){
_start:
{
uint8_t v_libPrefixOnWindows_336_; 
v_libPrefixOnWindows_336_ = lean_ctor_get_uint8(v_cfg_335_, sizeof(void*)*9);
return v_libPrefixOnWindows_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(v_cfg_337_);
lean_dec_ref(v_cfg_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_340_, lean_object* v_cfg_341_){
_start:
{
lean_object* v_toLeanConfig_342_; lean_object* v_srcDir_343_; lean_object* v_roots_344_; lean_object* v_globs_345_; lean_object* v_libName_346_; lean_object* v_needs_347_; lean_object* v_extraDepTargets_348_; uint8_t v_precompileLibrary_349_; uint8_t v_precompileModules_350_; lean_object* v_defaultFacets_351_; lean_object* v_nativeFacets_352_; uint8_t v_allowImportAll_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_toLeanConfig_342_ = lean_ctor_get(v_cfg_341_, 0);
v_srcDir_343_ = lean_ctor_get(v_cfg_341_, 1);
v_roots_344_ = lean_ctor_get(v_cfg_341_, 2);
v_globs_345_ = lean_ctor_get(v_cfg_341_, 3);
v_libName_346_ = lean_ctor_get(v_cfg_341_, 4);
v_needs_347_ = lean_ctor_get(v_cfg_341_, 5);
v_extraDepTargets_348_ = lean_ctor_get(v_cfg_341_, 6);
v_precompileLibrary_349_ = lean_ctor_get_uint8(v_cfg_341_, sizeof(void*)*9 + 1);
v_precompileModules_350_ = lean_ctor_get_uint8(v_cfg_341_, sizeof(void*)*9 + 2);
v_defaultFacets_351_ = lean_ctor_get(v_cfg_341_, 7);
v_nativeFacets_352_ = lean_ctor_get(v_cfg_341_, 8);
v_allowImportAll_353_ = lean_ctor_get_uint8(v_cfg_341_, sizeof(void*)*9 + 3);
v_isSharedCheck_360_ = !lean_is_exclusive(v_cfg_341_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v_cfg_341_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_nativeFacets_352_);
lean_inc(v_defaultFacets_351_);
lean_inc(v_extraDepTargets_348_);
lean_inc(v_needs_347_);
lean_inc(v_libName_346_);
lean_inc(v_globs_345_);
lean_inc(v_roots_344_);
lean_inc(v_srcDir_343_);
lean_inc(v_toLeanConfig_342_);
lean_dec(v_cfg_341_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_toLeanConfig_342_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_srcDir_343_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_roots_344_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_globs_345_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v_libName_346_);
lean_ctor_set(v_reuseFailAlloc_359_, 5, v_needs_347_);
lean_ctor_set(v_reuseFailAlloc_359_, 6, v_extraDepTargets_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 7, v_defaultFacets_351_);
lean_ctor_set(v_reuseFailAlloc_359_, 8, v_nativeFacets_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*9 + 1, v_precompileLibrary_349_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*9 + 2, v_precompileModules_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*9 + 3, v_allowImportAll_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*9, v_val_340_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_361_, lean_object* v_cfg_362_){
_start:
{
uint8_t v_val_74__boxed_363_; lean_object* v_res_364_; 
v_val_74__boxed_363_ = lean_unbox(v_val_361_);
v_res_364_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(v_val_74__boxed_363_, v_cfg_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_365_, lean_object* v_cfg_366_){
_start:
{
lean_object* v_toLeanConfig_367_; lean_object* v_srcDir_368_; lean_object* v_roots_369_; lean_object* v_globs_370_; lean_object* v_libName_371_; uint8_t v_libPrefixOnWindows_372_; lean_object* v_needs_373_; lean_object* v_extraDepTargets_374_; uint8_t v_precompileLibrary_375_; uint8_t v_precompileModules_376_; lean_object* v_defaultFacets_377_; lean_object* v_nativeFacets_378_; uint8_t v_allowImportAll_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_389_; 
v_toLeanConfig_367_ = lean_ctor_get(v_cfg_366_, 0);
v_srcDir_368_ = lean_ctor_get(v_cfg_366_, 1);
v_roots_369_ = lean_ctor_get(v_cfg_366_, 2);
v_globs_370_ = lean_ctor_get(v_cfg_366_, 3);
v_libName_371_ = lean_ctor_get(v_cfg_366_, 4);
v_libPrefixOnWindows_372_ = lean_ctor_get_uint8(v_cfg_366_, sizeof(void*)*9);
v_needs_373_ = lean_ctor_get(v_cfg_366_, 5);
v_extraDepTargets_374_ = lean_ctor_get(v_cfg_366_, 6);
v_precompileLibrary_375_ = lean_ctor_get_uint8(v_cfg_366_, sizeof(void*)*9 + 1);
v_precompileModules_376_ = lean_ctor_get_uint8(v_cfg_366_, sizeof(void*)*9 + 2);
v_defaultFacets_377_ = lean_ctor_get(v_cfg_366_, 7);
v_nativeFacets_378_ = lean_ctor_get(v_cfg_366_, 8);
v_allowImportAll_379_ = lean_ctor_get_uint8(v_cfg_366_, sizeof(void*)*9 + 3);
v_isSharedCheck_389_ = !lean_is_exclusive(v_cfg_366_);
if (v_isSharedCheck_389_ == 0)
{
v___x_381_ = v_cfg_366_;
v_isShared_382_ = v_isSharedCheck_389_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_nativeFacets_378_);
lean_inc(v_defaultFacets_377_);
lean_inc(v_extraDepTargets_374_);
lean_inc(v_needs_373_);
lean_inc(v_libName_371_);
lean_inc(v_globs_370_);
lean_inc(v_roots_369_);
lean_inc(v_srcDir_368_);
lean_inc(v_toLeanConfig_367_);
lean_dec(v_cfg_366_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_389_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = lean_box(v_libPrefixOnWindows_372_);
v___x_384_ = lean_apply_1(v_f_365_, v___x_383_);
if (v_isShared_382_ == 0)
{
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_toLeanConfig_367_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_srcDir_368_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_roots_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_globs_370_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_libName_371_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_needs_373_);
lean_ctor_set(v_reuseFailAlloc_388_, 6, v_extraDepTargets_374_);
lean_ctor_set(v_reuseFailAlloc_388_, 7, v_defaultFacets_377_);
lean_ctor_set(v_reuseFailAlloc_388_, 8, v_nativeFacets_378_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
uint8_t v___x_387_; 
v___x_387_ = lean_unbox(v___x_384_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*9, v___x_387_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*9 + 1, v_precompileLibrary_375_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*9 + 2, v_precompileModules_376_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*9 + 3, v_allowImportAll_379_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(lean_object* v_x_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed(lean_object* v_x_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(v_x_392_);
lean_dec_ref(v_x_392_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object* v_name_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = ((lean_object*)(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4));
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object* v_name_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_406_);
lean_dec(v_name_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object* v_name_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_name_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_410_);
lean_dec(v_name_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0(lean_object* v_cfg_412_){
_start:
{
lean_object* v_needs_413_; 
v_needs_413_ = lean_ctor_get(v_cfg_412_, 5);
lean_inc_ref(v_needs_413_);
return v_needs_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__0___boxed(lean_object* v_cfg_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_LeanLibConfig_needs___proj___lam__0(v_cfg_414_);
lean_dec_ref(v_cfg_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__1(lean_object* v_val_416_, lean_object* v_cfg_417_){
_start:
{
lean_object* v_toLeanConfig_418_; lean_object* v_srcDir_419_; lean_object* v_roots_420_; lean_object* v_globs_421_; lean_object* v_libName_422_; uint8_t v_libPrefixOnWindows_423_; lean_object* v_extraDepTargets_424_; uint8_t v_precompileLibrary_425_; uint8_t v_precompileModules_426_; lean_object* v_defaultFacets_427_; lean_object* v_nativeFacets_428_; uint8_t v_allowImportAll_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_toLeanConfig_418_ = lean_ctor_get(v_cfg_417_, 0);
v_srcDir_419_ = lean_ctor_get(v_cfg_417_, 1);
v_roots_420_ = lean_ctor_get(v_cfg_417_, 2);
v_globs_421_ = lean_ctor_get(v_cfg_417_, 3);
v_libName_422_ = lean_ctor_get(v_cfg_417_, 4);
v_libPrefixOnWindows_423_ = lean_ctor_get_uint8(v_cfg_417_, sizeof(void*)*9);
v_extraDepTargets_424_ = lean_ctor_get(v_cfg_417_, 6);
v_precompileLibrary_425_ = lean_ctor_get_uint8(v_cfg_417_, sizeof(void*)*9 + 1);
v_precompileModules_426_ = lean_ctor_get_uint8(v_cfg_417_, sizeof(void*)*9 + 2);
v_defaultFacets_427_ = lean_ctor_get(v_cfg_417_, 7);
v_nativeFacets_428_ = lean_ctor_get(v_cfg_417_, 8);
v_allowImportAll_429_ = lean_ctor_get_uint8(v_cfg_417_, sizeof(void*)*9 + 3);
v_isSharedCheck_436_ = !lean_is_exclusive(v_cfg_417_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_cfg_417_, 5);
lean_dec(v_unused_437_);
v___x_431_ = v_cfg_417_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_nativeFacets_428_);
lean_inc(v_defaultFacets_427_);
lean_inc(v_extraDepTargets_424_);
lean_inc(v_libName_422_);
lean_inc(v_globs_421_);
lean_inc(v_roots_420_);
lean_inc(v_srcDir_419_);
lean_inc(v_toLeanConfig_418_);
lean_dec(v_cfg_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 5, v_val_416_);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_toLeanConfig_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_srcDir_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_roots_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_globs_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_libName_422_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_val_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_extraDepTargets_424_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_defaultFacets_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_nativeFacets_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9, v_libPrefixOnWindows_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9 + 1, v_precompileLibrary_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9 + 2, v_precompileModules_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*9 + 3, v_allowImportAll_429_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__2(lean_object* v_f_438_, lean_object* v_cfg_439_){
_start:
{
lean_object* v_toLeanConfig_440_; lean_object* v_srcDir_441_; lean_object* v_roots_442_; lean_object* v_globs_443_; lean_object* v_libName_444_; uint8_t v_libPrefixOnWindows_445_; lean_object* v_needs_446_; lean_object* v_extraDepTargets_447_; uint8_t v_precompileLibrary_448_; uint8_t v_precompileModules_449_; lean_object* v_defaultFacets_450_; lean_object* v_nativeFacets_451_; uint8_t v_allowImportAll_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_460_; 
v_toLeanConfig_440_ = lean_ctor_get(v_cfg_439_, 0);
v_srcDir_441_ = lean_ctor_get(v_cfg_439_, 1);
v_roots_442_ = lean_ctor_get(v_cfg_439_, 2);
v_globs_443_ = lean_ctor_get(v_cfg_439_, 3);
v_libName_444_ = lean_ctor_get(v_cfg_439_, 4);
v_libPrefixOnWindows_445_ = lean_ctor_get_uint8(v_cfg_439_, sizeof(void*)*9);
v_needs_446_ = lean_ctor_get(v_cfg_439_, 5);
v_extraDepTargets_447_ = lean_ctor_get(v_cfg_439_, 6);
v_precompileLibrary_448_ = lean_ctor_get_uint8(v_cfg_439_, sizeof(void*)*9 + 1);
v_precompileModules_449_ = lean_ctor_get_uint8(v_cfg_439_, sizeof(void*)*9 + 2);
v_defaultFacets_450_ = lean_ctor_get(v_cfg_439_, 7);
v_nativeFacets_451_ = lean_ctor_get(v_cfg_439_, 8);
v_allowImportAll_452_ = lean_ctor_get_uint8(v_cfg_439_, sizeof(void*)*9 + 3);
v_isSharedCheck_460_ = !lean_is_exclusive(v_cfg_439_);
if (v_isSharedCheck_460_ == 0)
{
v___x_454_ = v_cfg_439_;
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_nativeFacets_451_);
lean_inc(v_defaultFacets_450_);
lean_inc(v_extraDepTargets_447_);
lean_inc(v_needs_446_);
lean_inc(v_libName_444_);
lean_inc(v_globs_443_);
lean_inc(v_roots_442_);
lean_inc(v_srcDir_441_);
lean_inc(v_toLeanConfig_440_);
lean_dec(v_cfg_439_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_apply_1(v_f_438_, v_needs_446_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 5, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_toLeanConfig_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_srcDir_441_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_roots_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_globs_443_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_libName_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 5, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_459_, 6, v_extraDepTargets_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 7, v_defaultFacets_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 8, v_nativeFacets_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*9, v_libPrefixOnWindows_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*9 + 1, v_precompileLibrary_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*9 + 2, v_precompileModules_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*9 + 3, v_allowImportAll_452_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3(lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___lam__3___boxed(lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lake_LeanLibConfig_needs___proj___lam__3(v_x_463_);
lean_dec_ref(v_x_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object* v_name_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___closed__4));
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object* v_name_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lake_LeanLibConfig_needs___proj(v_name_476_);
lean_dec(v_name_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object* v_name_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lake_LeanLibConfig_needs___proj(v_name_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object* v_name_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_480_);
lean_dec(v_name_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_482_){
_start:
{
lean_object* v_extraDepTargets_483_; 
v_extraDepTargets_483_ = lean_ctor_get(v_cfg_482_, 6);
lean_inc_ref(v_extraDepTargets_483_);
return v_extraDepTargets_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(v_cfg_484_);
lean_dec_ref(v_cfg_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1(lean_object* v_val_486_, lean_object* v_cfg_487_){
_start:
{
lean_object* v_toLeanConfig_488_; lean_object* v_srcDir_489_; lean_object* v_roots_490_; lean_object* v_globs_491_; lean_object* v_libName_492_; uint8_t v_libPrefixOnWindows_493_; lean_object* v_needs_494_; uint8_t v_precompileLibrary_495_; uint8_t v_precompileModules_496_; lean_object* v_defaultFacets_497_; lean_object* v_nativeFacets_498_; uint8_t v_allowImportAll_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_toLeanConfig_488_ = lean_ctor_get(v_cfg_487_, 0);
v_srcDir_489_ = lean_ctor_get(v_cfg_487_, 1);
v_roots_490_ = lean_ctor_get(v_cfg_487_, 2);
v_globs_491_ = lean_ctor_get(v_cfg_487_, 3);
v_libName_492_ = lean_ctor_get(v_cfg_487_, 4);
v_libPrefixOnWindows_493_ = lean_ctor_get_uint8(v_cfg_487_, sizeof(void*)*9);
v_needs_494_ = lean_ctor_get(v_cfg_487_, 5);
v_precompileLibrary_495_ = lean_ctor_get_uint8(v_cfg_487_, sizeof(void*)*9 + 1);
v_precompileModules_496_ = lean_ctor_get_uint8(v_cfg_487_, sizeof(void*)*9 + 2);
v_defaultFacets_497_ = lean_ctor_get(v_cfg_487_, 7);
v_nativeFacets_498_ = lean_ctor_get(v_cfg_487_, 8);
v_allowImportAll_499_ = lean_ctor_get_uint8(v_cfg_487_, sizeof(void*)*9 + 3);
v_isSharedCheck_506_ = !lean_is_exclusive(v_cfg_487_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_cfg_487_, 6);
lean_dec(v_unused_507_);
v___x_501_ = v_cfg_487_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_nativeFacets_498_);
lean_inc(v_defaultFacets_497_);
lean_inc(v_needs_494_);
lean_inc(v_libName_492_);
lean_inc(v_globs_491_);
lean_inc(v_roots_490_);
lean_inc(v_srcDir_489_);
lean_inc(v_toLeanConfig_488_);
lean_dec(v_cfg_487_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 6, v_val_486_);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_toLeanConfig_488_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_srcDir_489_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_roots_490_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_globs_491_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_libName_492_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_needs_494_);
lean_ctor_set(v_reuseFailAlloc_505_, 6, v_val_486_);
lean_ctor_set(v_reuseFailAlloc_505_, 7, v_defaultFacets_497_);
lean_ctor_set(v_reuseFailAlloc_505_, 8, v_nativeFacets_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9, v_libPrefixOnWindows_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9 + 1, v_precompileLibrary_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9 + 2, v_precompileModules_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*9 + 3, v_allowImportAll_499_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2(lean_object* v_f_508_, lean_object* v_cfg_509_){
_start:
{
lean_object* v_toLeanConfig_510_; lean_object* v_srcDir_511_; lean_object* v_roots_512_; lean_object* v_globs_513_; lean_object* v_libName_514_; uint8_t v_libPrefixOnWindows_515_; lean_object* v_needs_516_; lean_object* v_extraDepTargets_517_; uint8_t v_precompileLibrary_518_; uint8_t v_precompileModules_519_; lean_object* v_defaultFacets_520_; lean_object* v_nativeFacets_521_; uint8_t v_allowImportAll_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_toLeanConfig_510_ = lean_ctor_get(v_cfg_509_, 0);
v_srcDir_511_ = lean_ctor_get(v_cfg_509_, 1);
v_roots_512_ = lean_ctor_get(v_cfg_509_, 2);
v_globs_513_ = lean_ctor_get(v_cfg_509_, 3);
v_libName_514_ = lean_ctor_get(v_cfg_509_, 4);
v_libPrefixOnWindows_515_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*9);
v_needs_516_ = lean_ctor_get(v_cfg_509_, 5);
v_extraDepTargets_517_ = lean_ctor_get(v_cfg_509_, 6);
v_precompileLibrary_518_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*9 + 1);
v_precompileModules_519_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*9 + 2);
v_defaultFacets_520_ = lean_ctor_get(v_cfg_509_, 7);
v_nativeFacets_521_ = lean_ctor_get(v_cfg_509_, 8);
v_allowImportAll_522_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*9 + 3);
v_isSharedCheck_530_ = !lean_is_exclusive(v_cfg_509_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v_cfg_509_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_nativeFacets_521_);
lean_inc(v_defaultFacets_520_);
lean_inc(v_extraDepTargets_517_);
lean_inc(v_needs_516_);
lean_inc(v_libName_514_);
lean_inc(v_globs_513_);
lean_inc(v_roots_512_);
lean_inc(v_srcDir_511_);
lean_inc(v_toLeanConfig_510_);
lean_dec(v_cfg_509_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_apply_1(v_f_508_, v_extraDepTargets_517_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 6, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_toLeanConfig_510_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_srcDir_511_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_roots_512_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_globs_513_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_libName_514_);
lean_ctor_set(v_reuseFailAlloc_529_, 5, v_needs_516_);
lean_ctor_set(v_reuseFailAlloc_529_, 6, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 7, v_defaultFacets_520_);
lean_ctor_set(v_reuseFailAlloc_529_, 8, v_nativeFacets_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*9, v_libPrefixOnWindows_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*9 + 1, v_precompileLibrary_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*9 + 2, v_precompileModules_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*9 + 3, v_allowImportAll_522_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(v_x_535_);
lean_dec_ref(v_x_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object* v_name_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4));
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object* v_name_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_548_);
lean_dec(v_name_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object* v_name_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object* v_name_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_552_);
lean_dec(v_name_552_);
return v_res_553_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileLibrary___proj___lam__0(lean_object* v_cfg_554_){
_start:
{
uint8_t v_precompileLibrary_555_; 
v_precompileLibrary_555_ = lean_ctor_get_uint8(v_cfg_554_, sizeof(void*)*9 + 1);
return v_precompileLibrary_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__0___boxed(lean_object* v_cfg_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lake_LeanLibConfig_precompileLibrary___proj___lam__0(v_cfg_556_);
lean_dec_ref(v_cfg_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__1(uint8_t v_val_559_, lean_object* v_cfg_560_){
_start:
{
lean_object* v_toLeanConfig_561_; lean_object* v_srcDir_562_; lean_object* v_roots_563_; lean_object* v_globs_564_; lean_object* v_libName_565_; uint8_t v_libPrefixOnWindows_566_; lean_object* v_needs_567_; lean_object* v_extraDepTargets_568_; uint8_t v_precompileModules_569_; lean_object* v_defaultFacets_570_; lean_object* v_nativeFacets_571_; uint8_t v_allowImportAll_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_toLeanConfig_561_ = lean_ctor_get(v_cfg_560_, 0);
v_srcDir_562_ = lean_ctor_get(v_cfg_560_, 1);
v_roots_563_ = lean_ctor_get(v_cfg_560_, 2);
v_globs_564_ = lean_ctor_get(v_cfg_560_, 3);
v_libName_565_ = lean_ctor_get(v_cfg_560_, 4);
v_libPrefixOnWindows_566_ = lean_ctor_get_uint8(v_cfg_560_, sizeof(void*)*9);
v_needs_567_ = lean_ctor_get(v_cfg_560_, 5);
v_extraDepTargets_568_ = lean_ctor_get(v_cfg_560_, 6);
v_precompileModules_569_ = lean_ctor_get_uint8(v_cfg_560_, sizeof(void*)*9 + 2);
v_defaultFacets_570_ = lean_ctor_get(v_cfg_560_, 7);
v_nativeFacets_571_ = lean_ctor_get(v_cfg_560_, 8);
v_allowImportAll_572_ = lean_ctor_get_uint8(v_cfg_560_, sizeof(void*)*9 + 3);
v_isSharedCheck_579_ = !lean_is_exclusive(v_cfg_560_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v_cfg_560_;
v_isShared_575_ = v_isSharedCheck_579_;
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
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_toLeanConfig_561_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_srcDir_562_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_roots_563_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_globs_564_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_libName_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 5, v_needs_567_);
lean_ctor_set(v_reuseFailAlloc_578_, 6, v_extraDepTargets_568_);
lean_ctor_set(v_reuseFailAlloc_578_, 7, v_defaultFacets_570_);
lean_ctor_set(v_reuseFailAlloc_578_, 8, v_nativeFacets_571_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*9, v_libPrefixOnWindows_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*9 + 2, v_precompileModules_569_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*9 + 3, v_allowImportAll_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*9 + 1, v_val_559_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__1___boxed(lean_object* v_val_580_, lean_object* v_cfg_581_){
_start:
{
uint8_t v_val_74__boxed_582_; lean_object* v_res_583_; 
v_val_74__boxed_582_ = lean_unbox(v_val_580_);
v_res_583_ = l_Lake_LeanLibConfig_precompileLibrary___proj___lam__1(v_val_74__boxed_582_, v_cfg_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___lam__2(lean_object* v_f_584_, lean_object* v_cfg_585_){
_start:
{
lean_object* v_toLeanConfig_586_; lean_object* v_srcDir_587_; lean_object* v_roots_588_; lean_object* v_globs_589_; lean_object* v_libName_590_; uint8_t v_libPrefixOnWindows_591_; lean_object* v_needs_592_; lean_object* v_extraDepTargets_593_; uint8_t v_precompileLibrary_594_; uint8_t v_precompileModules_595_; lean_object* v_defaultFacets_596_; lean_object* v_nativeFacets_597_; uint8_t v_allowImportAll_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_608_; 
v_toLeanConfig_586_ = lean_ctor_get(v_cfg_585_, 0);
v_srcDir_587_ = lean_ctor_get(v_cfg_585_, 1);
v_roots_588_ = lean_ctor_get(v_cfg_585_, 2);
v_globs_589_ = lean_ctor_get(v_cfg_585_, 3);
v_libName_590_ = lean_ctor_get(v_cfg_585_, 4);
v_libPrefixOnWindows_591_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*9);
v_needs_592_ = lean_ctor_get(v_cfg_585_, 5);
v_extraDepTargets_593_ = lean_ctor_get(v_cfg_585_, 6);
v_precompileLibrary_594_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*9 + 1);
v_precompileModules_595_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*9 + 2);
v_defaultFacets_596_ = lean_ctor_get(v_cfg_585_, 7);
v_nativeFacets_597_ = lean_ctor_get(v_cfg_585_, 8);
v_allowImportAll_598_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*9 + 3);
v_isSharedCheck_608_ = !lean_is_exclusive(v_cfg_585_);
if (v_isSharedCheck_608_ == 0)
{
v___x_600_ = v_cfg_585_;
v_isShared_601_ = v_isSharedCheck_608_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_nativeFacets_597_);
lean_inc(v_defaultFacets_596_);
lean_inc(v_extraDepTargets_593_);
lean_inc(v_needs_592_);
lean_inc(v_libName_590_);
lean_inc(v_globs_589_);
lean_inc(v_roots_588_);
lean_inc(v_srcDir_587_);
lean_inc(v_toLeanConfig_586_);
lean_dec(v_cfg_585_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_608_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = lean_box(v_precompileLibrary_594_);
v___x_603_ = lean_apply_1(v_f_584_, v___x_602_);
if (v_isShared_601_ == 0)
{
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_toLeanConfig_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_srcDir_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_roots_588_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_globs_589_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_libName_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v_needs_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 6, v_extraDepTargets_593_);
lean_ctor_set(v_reuseFailAlloc_607_, 7, v_defaultFacets_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 8, v_nativeFacets_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*9, v_libPrefixOnWindows_591_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
uint8_t v___x_606_; 
v___x_606_ = lean_unbox(v___x_603_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*9 + 1, v___x_606_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*9 + 2, v_precompileModules_595_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*9 + 3, v_allowImportAll_598_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj(lean_object* v_name_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileLibrary___proj___closed__3));
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___boxed(lean_object* v_name_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lake_LeanLibConfig_precompileLibrary___proj(v_name_619_);
lean_dec(v_name_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField(lean_object* v_name_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lake_LeanLibConfig_precompileLibrary___proj(v_name_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___boxed(lean_object* v_name_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lake_LeanLibConfig_precompileLibrary_instConfigField(v_name_623_);
lean_dec(v_name_623_);
return v_res_624_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___lam__0(lean_object* v_cfg_625_){
_start:
{
uint8_t v_precompileModules_626_; 
v_precompileModules_626_ = lean_ctor_get_uint8(v_cfg_625_, sizeof(void*)*9 + 2);
return v_precompileModules_626_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__0(v_cfg_627_);
lean_dec_ref(v_cfg_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1(uint8_t v_val_630_, lean_object* v_cfg_631_){
_start:
{
lean_object* v_toLeanConfig_632_; lean_object* v_srcDir_633_; lean_object* v_roots_634_; lean_object* v_globs_635_; lean_object* v_libName_636_; uint8_t v_libPrefixOnWindows_637_; lean_object* v_needs_638_; lean_object* v_extraDepTargets_639_; uint8_t v_precompileLibrary_640_; lean_object* v_defaultFacets_641_; lean_object* v_nativeFacets_642_; uint8_t v_allowImportAll_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_toLeanConfig_632_ = lean_ctor_get(v_cfg_631_, 0);
v_srcDir_633_ = lean_ctor_get(v_cfg_631_, 1);
v_roots_634_ = lean_ctor_get(v_cfg_631_, 2);
v_globs_635_ = lean_ctor_get(v_cfg_631_, 3);
v_libName_636_ = lean_ctor_get(v_cfg_631_, 4);
v_libPrefixOnWindows_637_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*9);
v_needs_638_ = lean_ctor_get(v_cfg_631_, 5);
v_extraDepTargets_639_ = lean_ctor_get(v_cfg_631_, 6);
v_precompileLibrary_640_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*9 + 1);
v_defaultFacets_641_ = lean_ctor_get(v_cfg_631_, 7);
v_nativeFacets_642_ = lean_ctor_get(v_cfg_631_, 8);
v_allowImportAll_643_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*9 + 3);
v_isSharedCheck_650_ = !lean_is_exclusive(v_cfg_631_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v_cfg_631_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_nativeFacets_642_);
lean_inc(v_defaultFacets_641_);
lean_inc(v_extraDepTargets_639_);
lean_inc(v_needs_638_);
lean_inc(v_libName_636_);
lean_inc(v_globs_635_);
lean_inc(v_roots_634_);
lean_inc(v_srcDir_633_);
lean_inc(v_toLeanConfig_632_);
lean_dec(v_cfg_631_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_toLeanConfig_632_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_srcDir_633_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_roots_634_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_globs_635_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_libName_636_);
lean_ctor_set(v_reuseFailAlloc_649_, 5, v_needs_638_);
lean_ctor_set(v_reuseFailAlloc_649_, 6, v_extraDepTargets_639_);
lean_ctor_set(v_reuseFailAlloc_649_, 7, v_defaultFacets_641_);
lean_ctor_set(v_reuseFailAlloc_649_, 8, v_nativeFacets_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_649_, sizeof(void*)*9, v_libPrefixOnWindows_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_649_, sizeof(void*)*9 + 1, v_precompileLibrary_640_);
lean_ctor_set_uint8(v_reuseFailAlloc_649_, sizeof(void*)*9 + 3, v_allowImportAll_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*9 + 2, v_val_630_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_651_, lean_object* v_cfg_652_){
_start:
{
uint8_t v_val_74__boxed_653_; lean_object* v_res_654_; 
v_val_74__boxed_653_ = lean_unbox(v_val_651_);
v_res_654_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__1(v_val_74__boxed_653_, v_cfg_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___lam__2(lean_object* v_f_655_, lean_object* v_cfg_656_){
_start:
{
lean_object* v_toLeanConfig_657_; lean_object* v_srcDir_658_; lean_object* v_roots_659_; lean_object* v_globs_660_; lean_object* v_libName_661_; uint8_t v_libPrefixOnWindows_662_; lean_object* v_needs_663_; lean_object* v_extraDepTargets_664_; uint8_t v_precompileLibrary_665_; uint8_t v_precompileModules_666_; lean_object* v_defaultFacets_667_; lean_object* v_nativeFacets_668_; uint8_t v_allowImportAll_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_679_; 
v_toLeanConfig_657_ = lean_ctor_get(v_cfg_656_, 0);
v_srcDir_658_ = lean_ctor_get(v_cfg_656_, 1);
v_roots_659_ = lean_ctor_get(v_cfg_656_, 2);
v_globs_660_ = lean_ctor_get(v_cfg_656_, 3);
v_libName_661_ = lean_ctor_get(v_cfg_656_, 4);
v_libPrefixOnWindows_662_ = lean_ctor_get_uint8(v_cfg_656_, sizeof(void*)*9);
v_needs_663_ = lean_ctor_get(v_cfg_656_, 5);
v_extraDepTargets_664_ = lean_ctor_get(v_cfg_656_, 6);
v_precompileLibrary_665_ = lean_ctor_get_uint8(v_cfg_656_, sizeof(void*)*9 + 1);
v_precompileModules_666_ = lean_ctor_get_uint8(v_cfg_656_, sizeof(void*)*9 + 2);
v_defaultFacets_667_ = lean_ctor_get(v_cfg_656_, 7);
v_nativeFacets_668_ = lean_ctor_get(v_cfg_656_, 8);
v_allowImportAll_669_ = lean_ctor_get_uint8(v_cfg_656_, sizeof(void*)*9 + 3);
v_isSharedCheck_679_ = !lean_is_exclusive(v_cfg_656_);
if (v_isSharedCheck_679_ == 0)
{
v___x_671_ = v_cfg_656_;
v_isShared_672_ = v_isSharedCheck_679_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_nativeFacets_668_);
lean_inc(v_defaultFacets_667_);
lean_inc(v_extraDepTargets_664_);
lean_inc(v_needs_663_);
lean_inc(v_libName_661_);
lean_inc(v_globs_660_);
lean_inc(v_roots_659_);
lean_inc(v_srcDir_658_);
lean_inc(v_toLeanConfig_657_);
lean_dec(v_cfg_656_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_679_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_box(v_precompileModules_666_);
v___x_674_ = lean_apply_1(v_f_655_, v___x_673_);
if (v_isShared_672_ == 0)
{
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_toLeanConfig_657_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_srcDir_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_roots_659_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_globs_660_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_libName_661_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v_needs_663_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_extraDepTargets_664_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_defaultFacets_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_nativeFacets_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_678_, sizeof(void*)*9, v_libPrefixOnWindows_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_678_, sizeof(void*)*9 + 1, v_precompileLibrary_665_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
uint8_t v___x_677_; 
v___x_677_ = lean_unbox(v___x_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*9 + 2, v___x_677_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*9 + 3, v_allowImportAll_669_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object* v_name_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileModules___proj___closed__3));
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object* v_name_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_690_);
lean_dec(v_name_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object* v_name_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object* v_name_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_694_);
lean_dec(v_name_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(lean_object* v_cfg_696_){
_start:
{
lean_object* v_defaultFacets_697_; 
v_defaultFacets_697_ = lean_ctor_get(v_cfg_696_, 7);
lean_inc_ref(v_defaultFacets_697_);
return v_defaultFacets_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed(lean_object* v_cfg_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(v_cfg_698_);
lean_dec_ref(v_cfg_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__1(lean_object* v_val_700_, lean_object* v_cfg_701_){
_start:
{
lean_object* v_toLeanConfig_702_; lean_object* v_srcDir_703_; lean_object* v_roots_704_; lean_object* v_globs_705_; lean_object* v_libName_706_; uint8_t v_libPrefixOnWindows_707_; lean_object* v_needs_708_; lean_object* v_extraDepTargets_709_; uint8_t v_precompileLibrary_710_; uint8_t v_precompileModules_711_; lean_object* v_nativeFacets_712_; uint8_t v_allowImportAll_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
v_toLeanConfig_702_ = lean_ctor_get(v_cfg_701_, 0);
v_srcDir_703_ = lean_ctor_get(v_cfg_701_, 1);
v_roots_704_ = lean_ctor_get(v_cfg_701_, 2);
v_globs_705_ = lean_ctor_get(v_cfg_701_, 3);
v_libName_706_ = lean_ctor_get(v_cfg_701_, 4);
v_libPrefixOnWindows_707_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*9);
v_needs_708_ = lean_ctor_get(v_cfg_701_, 5);
v_extraDepTargets_709_ = lean_ctor_get(v_cfg_701_, 6);
v_precompileLibrary_710_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*9 + 1);
v_precompileModules_711_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*9 + 2);
v_nativeFacets_712_ = lean_ctor_get(v_cfg_701_, 8);
v_allowImportAll_713_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*9 + 3);
v_isSharedCheck_720_ = !lean_is_exclusive(v_cfg_701_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_cfg_701_, 7);
lean_dec(v_unused_721_);
v___x_715_ = v_cfg_701_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_nativeFacets_712_);
lean_inc(v_extraDepTargets_709_);
lean_inc(v_needs_708_);
lean_inc(v_libName_706_);
lean_inc(v_globs_705_);
lean_inc(v_roots_704_);
lean_inc(v_srcDir_703_);
lean_inc(v_toLeanConfig_702_);
lean_dec(v_cfg_701_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 7, v_val_700_);
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_toLeanConfig_702_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_srcDir_703_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_roots_704_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_globs_705_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_libName_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 5, v_needs_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 6, v_extraDepTargets_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 7, v_val_700_);
lean_ctor_set(v_reuseFailAlloc_719_, 8, v_nativeFacets_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*9, v_libPrefixOnWindows_707_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*9 + 1, v_precompileLibrary_710_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*9 + 2, v_precompileModules_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*9 + 3, v_allowImportAll_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__2(lean_object* v_f_722_, lean_object* v_cfg_723_){
_start:
{
lean_object* v_toLeanConfig_724_; lean_object* v_srcDir_725_; lean_object* v_roots_726_; lean_object* v_globs_727_; lean_object* v_libName_728_; uint8_t v_libPrefixOnWindows_729_; lean_object* v_needs_730_; lean_object* v_extraDepTargets_731_; uint8_t v_precompileLibrary_732_; uint8_t v_precompileModules_733_; lean_object* v_defaultFacets_734_; lean_object* v_nativeFacets_735_; uint8_t v_allowImportAll_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_toLeanConfig_724_ = lean_ctor_get(v_cfg_723_, 0);
v_srcDir_725_ = lean_ctor_get(v_cfg_723_, 1);
v_roots_726_ = lean_ctor_get(v_cfg_723_, 2);
v_globs_727_ = lean_ctor_get(v_cfg_723_, 3);
v_libName_728_ = lean_ctor_get(v_cfg_723_, 4);
v_libPrefixOnWindows_729_ = lean_ctor_get_uint8(v_cfg_723_, sizeof(void*)*9);
v_needs_730_ = lean_ctor_get(v_cfg_723_, 5);
v_extraDepTargets_731_ = lean_ctor_get(v_cfg_723_, 6);
v_precompileLibrary_732_ = lean_ctor_get_uint8(v_cfg_723_, sizeof(void*)*9 + 1);
v_precompileModules_733_ = lean_ctor_get_uint8(v_cfg_723_, sizeof(void*)*9 + 2);
v_defaultFacets_734_ = lean_ctor_get(v_cfg_723_, 7);
v_nativeFacets_735_ = lean_ctor_get(v_cfg_723_, 8);
v_allowImportAll_736_ = lean_ctor_get_uint8(v_cfg_723_, sizeof(void*)*9 + 3);
v_isSharedCheck_744_ = !lean_is_exclusive(v_cfg_723_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v_cfg_723_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_nativeFacets_735_);
lean_inc(v_defaultFacets_734_);
lean_inc(v_extraDepTargets_731_);
lean_inc(v_needs_730_);
lean_inc(v_libName_728_);
lean_inc(v_globs_727_);
lean_inc(v_roots_726_);
lean_inc(v_srcDir_725_);
lean_inc(v_toLeanConfig_724_);
lean_dec(v_cfg_723_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_apply_1(v_f_722_, v_defaultFacets_734_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 7, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_toLeanConfig_724_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_srcDir_725_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_roots_726_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_globs_727_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_libName_728_);
lean_ctor_set(v_reuseFailAlloc_743_, 5, v_needs_730_);
lean_ctor_set(v_reuseFailAlloc_743_, 6, v_extraDepTargets_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 7, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_743_, 8, v_nativeFacets_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*9, v_libPrefixOnWindows_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*9 + 1, v_precompileLibrary_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*9 + 2, v_precompileModules_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*9 + 3, v_allowImportAll_736_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(lean_object* v_x_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_746_);
lean_dec_ref(v___x_747_);
v___x_748_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed(lean_object* v_x_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(v_x_749_);
lean_dec_ref(v_x_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object* v_name_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Lake_LeanLibConfig_defaultFacets___proj___closed__4));
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object* v_name_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_762_);
lean_dec(v_name_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object* v_name_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object* v_name_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_766_);
lean_dec(v_name_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(lean_object* v_cfg_768_, uint8_t v___y_769_){
_start:
{
lean_object* v_nativeFacets_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_nativeFacets_770_ = lean_ctor_get(v_cfg_768_, 8);
lean_inc_ref(v_nativeFacets_770_);
lean_dec_ref(v_cfg_768_);
v___x_771_ = lean_box(v___y_769_);
v___x_772_ = lean_apply_1(v_nativeFacets_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed(lean_object* v_cfg_773_, lean_object* v___y_774_){
_start:
{
uint8_t v___y_129__boxed_775_; lean_object* v_res_776_; 
v___y_129__boxed_775_ = lean_unbox(v___y_774_);
v_res_776_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(v_cfg_773_, v___y_129__boxed_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__1(lean_object* v_val_777_, lean_object* v_cfg_778_){
_start:
{
lean_object* v_toLeanConfig_779_; lean_object* v_srcDir_780_; lean_object* v_roots_781_; lean_object* v_globs_782_; lean_object* v_libName_783_; uint8_t v_libPrefixOnWindows_784_; lean_object* v_needs_785_; lean_object* v_extraDepTargets_786_; uint8_t v_precompileLibrary_787_; uint8_t v_precompileModules_788_; lean_object* v_defaultFacets_789_; uint8_t v_allowImportAll_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_toLeanConfig_779_ = lean_ctor_get(v_cfg_778_, 0);
v_srcDir_780_ = lean_ctor_get(v_cfg_778_, 1);
v_roots_781_ = lean_ctor_get(v_cfg_778_, 2);
v_globs_782_ = lean_ctor_get(v_cfg_778_, 3);
v_libName_783_ = lean_ctor_get(v_cfg_778_, 4);
v_libPrefixOnWindows_784_ = lean_ctor_get_uint8(v_cfg_778_, sizeof(void*)*9);
v_needs_785_ = lean_ctor_get(v_cfg_778_, 5);
v_extraDepTargets_786_ = lean_ctor_get(v_cfg_778_, 6);
v_precompileLibrary_787_ = lean_ctor_get_uint8(v_cfg_778_, sizeof(void*)*9 + 1);
v_precompileModules_788_ = lean_ctor_get_uint8(v_cfg_778_, sizeof(void*)*9 + 2);
v_defaultFacets_789_ = lean_ctor_get(v_cfg_778_, 7);
v_allowImportAll_790_ = lean_ctor_get_uint8(v_cfg_778_, sizeof(void*)*9 + 3);
v_isSharedCheck_797_ = !lean_is_exclusive(v_cfg_778_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v_cfg_778_, 8);
lean_dec(v_unused_798_);
v___x_792_ = v_cfg_778_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_defaultFacets_789_);
lean_inc(v_extraDepTargets_786_);
lean_inc(v_needs_785_);
lean_inc(v_libName_783_);
lean_inc(v_globs_782_);
lean_inc(v_roots_781_);
lean_inc(v_srcDir_780_);
lean_inc(v_toLeanConfig_779_);
lean_dec(v_cfg_778_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 8, v_val_777_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_toLeanConfig_779_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_srcDir_780_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_roots_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_globs_782_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_libName_783_);
lean_ctor_set(v_reuseFailAlloc_796_, 5, v_needs_785_);
lean_ctor_set(v_reuseFailAlloc_796_, 6, v_extraDepTargets_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 7, v_defaultFacets_789_);
lean_ctor_set(v_reuseFailAlloc_796_, 8, v_val_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_796_, sizeof(void*)*9, v_libPrefixOnWindows_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_796_, sizeof(void*)*9 + 1, v_precompileLibrary_787_);
lean_ctor_set_uint8(v_reuseFailAlloc_796_, sizeof(void*)*9 + 2, v_precompileModules_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_796_, sizeof(void*)*9 + 3, v_allowImportAll_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__2(lean_object* v_f_799_, lean_object* v_cfg_800_){
_start:
{
lean_object* v_toLeanConfig_801_; lean_object* v_srcDir_802_; lean_object* v_roots_803_; lean_object* v_globs_804_; lean_object* v_libName_805_; uint8_t v_libPrefixOnWindows_806_; lean_object* v_needs_807_; lean_object* v_extraDepTargets_808_; uint8_t v_precompileLibrary_809_; uint8_t v_precompileModules_810_; lean_object* v_defaultFacets_811_; lean_object* v_nativeFacets_812_; uint8_t v_allowImportAll_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_toLeanConfig_801_ = lean_ctor_get(v_cfg_800_, 0);
v_srcDir_802_ = lean_ctor_get(v_cfg_800_, 1);
v_roots_803_ = lean_ctor_get(v_cfg_800_, 2);
v_globs_804_ = lean_ctor_get(v_cfg_800_, 3);
v_libName_805_ = lean_ctor_get(v_cfg_800_, 4);
v_libPrefixOnWindows_806_ = lean_ctor_get_uint8(v_cfg_800_, sizeof(void*)*9);
v_needs_807_ = lean_ctor_get(v_cfg_800_, 5);
v_extraDepTargets_808_ = lean_ctor_get(v_cfg_800_, 6);
v_precompileLibrary_809_ = lean_ctor_get_uint8(v_cfg_800_, sizeof(void*)*9 + 1);
v_precompileModules_810_ = lean_ctor_get_uint8(v_cfg_800_, sizeof(void*)*9 + 2);
v_defaultFacets_811_ = lean_ctor_get(v_cfg_800_, 7);
v_nativeFacets_812_ = lean_ctor_get(v_cfg_800_, 8);
v_allowImportAll_813_ = lean_ctor_get_uint8(v_cfg_800_, sizeof(void*)*9 + 3);
v_isSharedCheck_821_ = !lean_is_exclusive(v_cfg_800_);
if (v_isSharedCheck_821_ == 0)
{
v___x_815_ = v_cfg_800_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_nativeFacets_812_);
lean_inc(v_defaultFacets_811_);
lean_inc(v_extraDepTargets_808_);
lean_inc(v_needs_807_);
lean_inc(v_libName_805_);
lean_inc(v_globs_804_);
lean_inc(v_roots_803_);
lean_inc(v_srcDir_802_);
lean_inc(v_toLeanConfig_801_);
lean_dec(v_cfg_800_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_apply_1(v_f_799_, v_nativeFacets_812_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 8, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_toLeanConfig_801_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_srcDir_802_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_roots_803_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_globs_804_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_libName_805_);
lean_ctor_set(v_reuseFailAlloc_820_, 5, v_needs_807_);
lean_ctor_set(v_reuseFailAlloc_820_, 6, v_extraDepTargets_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 7, v_defaultFacets_811_);
lean_ctor_set(v_reuseFailAlloc_820_, 8, v___x_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*9, v_libPrefixOnWindows_806_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*9 + 1, v_precompileLibrary_809_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*9 + 2, v_precompileModules_810_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*9 + 3, v_allowImportAll_813_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(lean_object* v_x_822_, uint8_t v___y_823_){
_start:
{
lean_object* v___y_825_; 
if (v___y_823_ == 0)
{
lean_object* v___x_829_; 
v___x_829_ = l_Lake_Module_oFacet;
v___y_825_ = v___x_829_;
goto v___jp_824_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = l_Lake_Module_oExportFacet;
v___y_825_ = v___x_830_;
goto v___jp_824_;
}
v___jp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
lean_inc(v___y_825_);
v___x_828_ = lean_array_push(v___x_827_, v___y_825_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed(lean_object* v_x_831_, lean_object* v___y_832_){
_start:
{
uint8_t v___y_179__boxed_833_; lean_object* v_res_834_; 
v___y_179__boxed_833_ = lean_unbox(v___y_832_);
v_res_834_ = l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(v_x_831_, v___y_179__boxed_833_);
lean_dec_ref(v_x_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object* v_name_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lake_LeanLibConfig_nativeFacets___proj___closed__4));
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object* v_name_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_846_);
lean_dec(v_name_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object* v_name_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object* v_name_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_850_);
lean_dec(v_name_850_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_852_){
_start:
{
uint8_t v_allowImportAll_853_; 
v_allowImportAll_853_ = lean_ctor_get_uint8(v_cfg_852_, sizeof(void*)*9 + 3);
return v_allowImportAll_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(v_cfg_854_);
lean_dec_ref(v_cfg_854_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(uint8_t v_val_857_, lean_object* v_cfg_858_){
_start:
{
lean_object* v_toLeanConfig_859_; lean_object* v_srcDir_860_; lean_object* v_roots_861_; lean_object* v_globs_862_; lean_object* v_libName_863_; uint8_t v_libPrefixOnWindows_864_; lean_object* v_needs_865_; lean_object* v_extraDepTargets_866_; uint8_t v_precompileLibrary_867_; uint8_t v_precompileModules_868_; lean_object* v_defaultFacets_869_; lean_object* v_nativeFacets_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_toLeanConfig_859_ = lean_ctor_get(v_cfg_858_, 0);
v_srcDir_860_ = lean_ctor_get(v_cfg_858_, 1);
v_roots_861_ = lean_ctor_get(v_cfg_858_, 2);
v_globs_862_ = lean_ctor_get(v_cfg_858_, 3);
v_libName_863_ = lean_ctor_get(v_cfg_858_, 4);
v_libPrefixOnWindows_864_ = lean_ctor_get_uint8(v_cfg_858_, sizeof(void*)*9);
v_needs_865_ = lean_ctor_get(v_cfg_858_, 5);
v_extraDepTargets_866_ = lean_ctor_get(v_cfg_858_, 6);
v_precompileLibrary_867_ = lean_ctor_get_uint8(v_cfg_858_, sizeof(void*)*9 + 1);
v_precompileModules_868_ = lean_ctor_get_uint8(v_cfg_858_, sizeof(void*)*9 + 2);
v_defaultFacets_869_ = lean_ctor_get(v_cfg_858_, 7);
v_nativeFacets_870_ = lean_ctor_get(v_cfg_858_, 8);
v_isSharedCheck_877_ = !lean_is_exclusive(v_cfg_858_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v_cfg_858_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_nativeFacets_870_);
lean_inc(v_defaultFacets_869_);
lean_inc(v_extraDepTargets_866_);
lean_inc(v_needs_865_);
lean_inc(v_libName_863_);
lean_inc(v_globs_862_);
lean_inc(v_roots_861_);
lean_inc(v_srcDir_860_);
lean_inc(v_toLeanConfig_859_);
lean_dec(v_cfg_858_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_toLeanConfig_859_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_srcDir_860_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_roots_861_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_globs_862_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_libName_863_);
lean_ctor_set(v_reuseFailAlloc_876_, 5, v_needs_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 6, v_extraDepTargets_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 7, v_defaultFacets_869_);
lean_ctor_set(v_reuseFailAlloc_876_, 8, v_nativeFacets_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*9, v_libPrefixOnWindows_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*9 + 1, v_precompileLibrary_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*9 + 2, v_precompileModules_868_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*9 + 3, v_val_857_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_878_, lean_object* v_cfg_879_){
_start:
{
uint8_t v_val_74__boxed_880_; lean_object* v_res_881_; 
v_val_74__boxed_880_ = lean_unbox(v_val_878_);
v_res_881_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(v_val_74__boxed_880_, v_cfg_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___lam__2(lean_object* v_f_882_, lean_object* v_cfg_883_){
_start:
{
lean_object* v_toLeanConfig_884_; lean_object* v_srcDir_885_; lean_object* v_roots_886_; lean_object* v_globs_887_; lean_object* v_libName_888_; uint8_t v_libPrefixOnWindows_889_; lean_object* v_needs_890_; lean_object* v_extraDepTargets_891_; uint8_t v_precompileLibrary_892_; uint8_t v_precompileModules_893_; lean_object* v_defaultFacets_894_; lean_object* v_nativeFacets_895_; uint8_t v_allowImportAll_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
v_toLeanConfig_884_ = lean_ctor_get(v_cfg_883_, 0);
v_srcDir_885_ = lean_ctor_get(v_cfg_883_, 1);
v_roots_886_ = lean_ctor_get(v_cfg_883_, 2);
v_globs_887_ = lean_ctor_get(v_cfg_883_, 3);
v_libName_888_ = lean_ctor_get(v_cfg_883_, 4);
v_libPrefixOnWindows_889_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*9);
v_needs_890_ = lean_ctor_get(v_cfg_883_, 5);
v_extraDepTargets_891_ = lean_ctor_get(v_cfg_883_, 6);
v_precompileLibrary_892_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*9 + 1);
v_precompileModules_893_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*9 + 2);
v_defaultFacets_894_ = lean_ctor_get(v_cfg_883_, 7);
v_nativeFacets_895_ = lean_ctor_get(v_cfg_883_, 8);
v_allowImportAll_896_ = lean_ctor_get_uint8(v_cfg_883_, sizeof(void*)*9 + 3);
v_isSharedCheck_906_ = !lean_is_exclusive(v_cfg_883_);
if (v_isSharedCheck_906_ == 0)
{
v___x_898_ = v_cfg_883_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_nativeFacets_895_);
lean_inc(v_defaultFacets_894_);
lean_inc(v_extraDepTargets_891_);
lean_inc(v_needs_890_);
lean_inc(v_libName_888_);
lean_inc(v_globs_887_);
lean_inc(v_roots_886_);
lean_inc(v_srcDir_885_);
lean_inc(v_toLeanConfig_884_);
lean_dec(v_cfg_883_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_900_ = lean_box(v_allowImportAll_896_);
v___x_901_ = lean_apply_1(v_f_882_, v___x_900_);
if (v_isShared_899_ == 0)
{
v___x_903_ = v___x_898_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_toLeanConfig_884_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_srcDir_885_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_roots_886_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_globs_887_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_libName_888_);
lean_ctor_set(v_reuseFailAlloc_905_, 5, v_needs_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 6, v_extraDepTargets_891_);
lean_ctor_set(v_reuseFailAlloc_905_, 7, v_defaultFacets_894_);
lean_ctor_set(v_reuseFailAlloc_905_, 8, v_nativeFacets_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9, v_libPrefixOnWindows_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9 + 1, v_precompileLibrary_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9 + 2, v_precompileModules_893_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
uint8_t v___x_904_; 
v___x_904_ = lean_unbox(v___x_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*9 + 3, v___x_904_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object* v_name_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l_Lake_LeanLibConfig_allowImportAll___proj___closed__3));
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object* v_name_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_917_);
lean_dec(v_name_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object* v_name_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object* v_name_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_921_);
lean_dec(v_name_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_923_){
_start:
{
lean_object* v_toLeanConfig_924_; 
v_toLeanConfig_924_ = lean_ctor_get(v_cfg_923_, 0);
lean_inc_ref(v_toLeanConfig_924_);
return v_toLeanConfig_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(v_cfg_925_);
lean_dec_ref(v_cfg_925_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1(lean_object* v_val_927_, lean_object* v_cfg_928_){
_start:
{
lean_object* v_srcDir_929_; lean_object* v_roots_930_; lean_object* v_globs_931_; lean_object* v_libName_932_; uint8_t v_libPrefixOnWindows_933_; lean_object* v_needs_934_; lean_object* v_extraDepTargets_935_; uint8_t v_precompileLibrary_936_; uint8_t v_precompileModules_937_; lean_object* v_defaultFacets_938_; lean_object* v_nativeFacets_939_; uint8_t v_allowImportAll_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_srcDir_929_ = lean_ctor_get(v_cfg_928_, 1);
v_roots_930_ = lean_ctor_get(v_cfg_928_, 2);
v_globs_931_ = lean_ctor_get(v_cfg_928_, 3);
v_libName_932_ = lean_ctor_get(v_cfg_928_, 4);
v_libPrefixOnWindows_933_ = lean_ctor_get_uint8(v_cfg_928_, sizeof(void*)*9);
v_needs_934_ = lean_ctor_get(v_cfg_928_, 5);
v_extraDepTargets_935_ = lean_ctor_get(v_cfg_928_, 6);
v_precompileLibrary_936_ = lean_ctor_get_uint8(v_cfg_928_, sizeof(void*)*9 + 1);
v_precompileModules_937_ = lean_ctor_get_uint8(v_cfg_928_, sizeof(void*)*9 + 2);
v_defaultFacets_938_ = lean_ctor_get(v_cfg_928_, 7);
v_nativeFacets_939_ = lean_ctor_get(v_cfg_928_, 8);
v_allowImportAll_940_ = lean_ctor_get_uint8(v_cfg_928_, sizeof(void*)*9 + 3);
v_isSharedCheck_947_ = !lean_is_exclusive(v_cfg_928_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_cfg_928_, 0);
lean_dec(v_unused_948_);
v___x_942_ = v_cfg_928_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_nativeFacets_939_);
lean_inc(v_defaultFacets_938_);
lean_inc(v_extraDepTargets_935_);
lean_inc(v_needs_934_);
lean_inc(v_libName_932_);
lean_inc(v_globs_931_);
lean_inc(v_roots_930_);
lean_inc(v_srcDir_929_);
lean_dec(v_cfg_928_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_val_927_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_val_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_srcDir_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_roots_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_globs_931_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_libName_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_needs_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_extraDepTargets_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_defaultFacets_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v_nativeFacets_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*9, v_libPrefixOnWindows_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*9 + 1, v_precompileLibrary_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*9 + 2, v_precompileModules_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*9 + 3, v_allowImportAll_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2(lean_object* v_f_949_, lean_object* v_cfg_950_){
_start:
{
lean_object* v_toLeanConfig_951_; lean_object* v_srcDir_952_; lean_object* v_roots_953_; lean_object* v_globs_954_; lean_object* v_libName_955_; uint8_t v_libPrefixOnWindows_956_; lean_object* v_needs_957_; lean_object* v_extraDepTargets_958_; uint8_t v_precompileLibrary_959_; uint8_t v_precompileModules_960_; lean_object* v_defaultFacets_961_; lean_object* v_nativeFacets_962_; uint8_t v_allowImportAll_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_971_; 
v_toLeanConfig_951_ = lean_ctor_get(v_cfg_950_, 0);
v_srcDir_952_ = lean_ctor_get(v_cfg_950_, 1);
v_roots_953_ = lean_ctor_get(v_cfg_950_, 2);
v_globs_954_ = lean_ctor_get(v_cfg_950_, 3);
v_libName_955_ = lean_ctor_get(v_cfg_950_, 4);
v_libPrefixOnWindows_956_ = lean_ctor_get_uint8(v_cfg_950_, sizeof(void*)*9);
v_needs_957_ = lean_ctor_get(v_cfg_950_, 5);
v_extraDepTargets_958_ = lean_ctor_get(v_cfg_950_, 6);
v_precompileLibrary_959_ = lean_ctor_get_uint8(v_cfg_950_, sizeof(void*)*9 + 1);
v_precompileModules_960_ = lean_ctor_get_uint8(v_cfg_950_, sizeof(void*)*9 + 2);
v_defaultFacets_961_ = lean_ctor_get(v_cfg_950_, 7);
v_nativeFacets_962_ = lean_ctor_get(v_cfg_950_, 8);
v_allowImportAll_963_ = lean_ctor_get_uint8(v_cfg_950_, sizeof(void*)*9 + 3);
v_isSharedCheck_971_ = !lean_is_exclusive(v_cfg_950_);
if (v_isSharedCheck_971_ == 0)
{
v___x_965_ = v_cfg_950_;
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_nativeFacets_962_);
lean_inc(v_defaultFacets_961_);
lean_inc(v_extraDepTargets_958_);
lean_inc(v_needs_957_);
lean_inc(v_libName_955_);
lean_inc(v_globs_954_);
lean_inc(v_roots_953_);
lean_inc(v_srcDir_952_);
lean_inc(v_toLeanConfig_951_);
lean_dec(v_cfg_950_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_apply_1(v_f_949_, v_toLeanConfig_951_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_srcDir_952_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_roots_953_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_globs_954_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_libName_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v_needs_957_);
lean_ctor_set(v_reuseFailAlloc_970_, 6, v_extraDepTargets_958_);
lean_ctor_set(v_reuseFailAlloc_970_, 7, v_defaultFacets_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 8, v_nativeFacets_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*9, v_libPrefixOnWindows_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*9 + 1, v_precompileLibrary_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*9 + 2, v_precompileModules_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*9 + 3, v_allowImportAll_963_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(lean_object* v_x_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1));
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(v_x_982_);
lean_dec_ref(v_x_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object* v_name_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4));
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object* v_name_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_995_);
lean_dec(v_name_995_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(lean_object* v_name_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_name_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(v_name_999_);
lean_dec(v_name_999_);
return v_res_1000_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__3));
v___x_1011_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__0));
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__7));
v___x_1021_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__4, &l_Lake_LeanLibConfig___fields___closed__4_once, _init_l_Lake_LeanLibConfig___fields___closed__4);
v___x_1022_ = lean_array_push(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__11));
v___x_1031_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__8, &l_Lake_LeanLibConfig___fields___closed__8_once, _init_l_Lake_LeanLibConfig___fields___closed__8);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__15));
v___x_1041_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__12, &l_Lake_LeanLibConfig___fields___closed__12_once, _init_l_Lake_LeanLibConfig___fields___closed__12);
v___x_1042_ = lean_array_push(v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__19));
v___x_1051_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__16, &l_Lake_LeanLibConfig___fields___closed__16_once, _init_l_Lake_LeanLibConfig___fields___closed__16);
v___x_1052_ = lean_array_push(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__23));
v___x_1061_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__20, &l_Lake_LeanLibConfig___fields___closed__20_once, _init_l_Lake_LeanLibConfig___fields___closed__20);
v___x_1062_ = lean_array_push(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__27));
v___x_1071_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__24, &l_Lake_LeanLibConfig___fields___closed__24_once, _init_l_Lake_LeanLibConfig___fields___closed__24);
v___x_1072_ = lean_array_push(v___x_1071_, v___x_1070_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__31));
v___x_1081_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__28, &l_Lake_LeanLibConfig___fields___closed__28_once, _init_l_Lake_LeanLibConfig___fields___closed__28);
v___x_1082_ = lean_array_push(v___x_1081_, v___x_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__35));
v___x_1091_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__32, &l_Lake_LeanLibConfig___fields___closed__32_once, _init_l_Lake_LeanLibConfig___fields___closed__32);
v___x_1092_ = lean_array_push(v___x_1091_, v___x_1090_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__39));
v___x_1101_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__36, &l_Lake_LeanLibConfig___fields___closed__36_once, _init_l_Lake_LeanLibConfig___fields___closed__36);
v___x_1102_ = lean_array_push(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__43));
v___x_1111_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__40, &l_Lake_LeanLibConfig___fields___closed__40_once, _init_l_Lake_LeanLibConfig___fields___closed__40);
v___x_1112_ = lean_array_push(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__47));
v___x_1121_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__44, &l_Lake_LeanLibConfig___fields___closed__44_once, _init_l_Lake_LeanLibConfig___fields___closed__44);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1120_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__49(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lake_LeanConfig___fields;
v___x_1124_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__48, &l_Lake_LeanLibConfig___fields___closed__48_once, _init_l_Lake_LeanLibConfig___fields___closed__48);
v___x_1125_ = l_Array_append___redArg(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__53(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__52));
v___x_1134_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__49, &l_Lake_LeanLibConfig___fields___closed__49_once, _init_l_Lake_LeanLibConfig___fields___closed__49);
v___x_1135_ = lean_array_push(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields(void){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__53, &l_Lake_LeanLibConfig___fields___closed__53_once, _init_l_Lake_LeanLibConfig___fields___closed__53);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields(lean_object* v_name_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lake_LeanLibConfig___fields;
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___boxed(lean_object* v_name_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lake_LeanLibConfig_instConfigFields(v_name_1139_);
lean_dec(v_name_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo___lam__0(lean_object* v_x1_1141_, lean_object* v_x2_1142_){
_start:
{
lean_object* v_name_1143_; lean_object* v___x_1144_; 
v_name_1143_ = lean_ctor_get(v_x2_1142_, 0);
lean_inc(v_name_1143_);
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1143_, v_x2_1142_, v_x1_1141_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = l_Lake_LeanLibConfig___fields;
v___x_1146_ = lean_array_get_size(v___x_1145_);
return v___x_1146_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_nat_dec_lt(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1171_ = lean_nat_dec_le(v___x_1170_, v___x_1170_);
return v___x_1171_;
}
}
static size_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_1172_; size_t v___x_1173_; 
v___x_1172_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1173_ = lean_usize_of_nat(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1174_ = lean_box(1);
v___x_1175_ = lean_usize_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__14, &l_Lake_LeanLibConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14);
v___x_1176_ = ((size_t)0ULL);
v___x_1177_ = l_Lake_LeanLibConfig___fields;
v___f_1178_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__12));
v___x_1179_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1179_, v___f_1178_, v___x_1177_, v___x_1176_, v___x_1175_, v___x_1174_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___y_1183_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1181_ = l_Lake_LeanLibConfig___fields;
v___x_1186_ = lean_box(1);
v___x_1187_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__11, &l_Lake_LeanLibConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11);
if (v___x_1187_ == 0)
{
v___y_1183_ = v___x_1186_;
goto v___jp_1182_;
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__13, &l_Lake_LeanLibConfig_instConfigInfo___closed__13_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13);
if (v___x_1188_ == 0)
{
if (v___x_1187_ == 0)
{
v___y_1183_ = v___x_1186_;
goto v___jp_1182_;
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1183_ = v___x_1189_;
goto v___jp_1182_;
}
}
else
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1183_ = v___x_1190_;
goto v___jp_1182_;
}
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_1183_);
v___x_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1181_);
lean_ctor_set(v___x_1185_, 1, v___y_1183_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__0(lean_object* v_x_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection(lean_object* v_name_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; size_t v_sz_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___f_1195_ = ((lean_object*)(l_Lake_LeanLibConfig_instEmptyCollection___closed__0));
v___f_1196_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_1197_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_1198_ = 0;
v___x_1199_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_1200_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_mk_empty_array_with_capacity(v___x_1201_);
v___x_1203_ = lean_array_push(v___x_1202_, v_name_1194_);
v___x_1204_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v_sz_1205_ = lean_array_size(v___x_1203_);
v___x_1206_ = ((size_t)0ULL);
lean_inc_ref(v___x_1203_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1204_, v___f_1195_, v_sz_1205_, v___x_1206_, v___x_1203_);
v___x_1208_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_1209_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
v___x_1210_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v___x_1210_, 0, v___x_1199_);
lean_ctor_set(v___x_1210_, 1, v___x_1200_);
lean_ctor_set(v___x_1210_, 2, v___x_1203_);
lean_ctor_set(v___x_1210_, 3, v___x_1207_);
lean_ctor_set(v___x_1210_, 4, v___x_1208_);
lean_ctor_set(v___x_1210_, 5, v___x_1197_);
lean_ctor_set(v___x_1210_, 6, v___x_1197_);
lean_ctor_set(v___x_1210_, 7, v___x_1209_);
lean_ctor_set(v___x_1210_, 8, v___f_1196_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*9, v___x_1198_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*9 + 1, v___x_1198_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*9 + 2, v___x_1198_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*9 + 3, v___x_1198_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg(lean_object* v_n_1211_){
_start:
{
lean_inc(v_n_1211_);
return v_n_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg___boxed(lean_object* v_n_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lake_LeanLibConfig_name___redArg(v_n_1212_);
lean_dec(v_n_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name(lean_object* v_n_1214_, lean_object* v_x_1215_){
_start:
{
lean_inc(v_n_1214_);
return v_n_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___boxed(lean_object* v_n_1216_, lean_object* v_x_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lake_LeanLibConfig_name(v_n_1216_, v_x_1217_);
lean_dec_ref(v_x_1217_);
lean_dec(v_n_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(lean_object* v_mod_1219_, lean_object* v_as_1220_, size_t v_i_1221_, size_t v_stop_1222_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_eq(v_i_1221_, v_stop_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_array_uget_borrowed(v_as_1220_, v_i_1221_);
v___x_1225_ = l_Lake_Glob_matches(v_mod_1219_, v___x_1224_);
if (v___x_1225_ == 0)
{
size_t v___x_1226_; size_t v___x_1227_; 
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1221_, v___x_1226_);
v_i_1221_ = v___x_1227_;
goto _start;
}
else
{
return v___x_1225_;
}
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(lean_object* v_mod_1230_, lean_object* v_as_1231_, lean_object* v_i_1232_, lean_object* v_stop_1233_){
_start:
{
size_t v_i_boxed_1234_; size_t v_stop_boxed_1235_; uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_i_boxed_1234_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_stop_boxed_1235_ = lean_unbox_usize(v_stop_1233_);
lean_dec(v_stop_1233_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1230_, v_as_1231_, v_i_boxed_1234_, v_stop_boxed_1235_);
lean_dec_ref(v_as_1231_);
lean_dec(v_mod_1230_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(lean_object* v_mod_1238_, lean_object* v_as_1239_, size_t v_i_1240_, size_t v_stop_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_eq(v_i_1240_, v_stop_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_array_uget_borrowed(v_as_1239_, v_i_1240_);
v___x_1244_ = l_Lean_Name_isPrefixOf(v___x_1243_, v_mod_1238_);
if (v___x_1244_ == 0)
{
size_t v___x_1245_; size_t v___x_1246_; 
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1240_, v___x_1245_);
v_i_1240_ = v___x_1246_;
goto _start;
}
else
{
return v___x_1244_;
}
}
else
{
uint8_t v___x_1248_; 
v___x_1248_ = 0;
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(lean_object* v_mod_1249_, lean_object* v_as_1250_, lean_object* v_i_1251_, lean_object* v_stop_1252_){
_start:
{
size_t v_i_boxed_1253_; size_t v_stop_boxed_1254_; uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_i_boxed_1253_ = lean_unbox_usize(v_i_1251_);
lean_dec(v_i_1251_);
v_stop_boxed_1254_ = lean_unbox_usize(v_stop_1252_);
lean_dec(v_stop_1252_);
v_res_1255_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1249_, v_as_1250_, v_i_boxed_1253_, v_stop_boxed_1254_);
lean_dec_ref(v_as_1250_);
lean_dec(v_mod_1249_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object* v_mod_1257_, lean_object* v_self_1258_){
_start:
{
lean_object* v_roots_1259_; lean_object* v_globs_1260_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_roots_1259_ = lean_ctor_get(v_self_1258_, 2);
v_globs_1260_ = lean_ctor_get(v_self_1258_, 3);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_array_get_size(v_roots_1259_);
v___x_1270_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
goto v___jp_1261_;
}
else
{
if (v___x_1270_ == 0)
{
goto v___jp_1261_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1269_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1257_, v_roots_1259_, v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
goto v___jp_1261_;
}
else
{
return v___x_1273_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_array_get_size(v_globs_1260_);
v___x_1264_ = lean_nat_dec_lt(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
return v___x_1264_;
}
else
{
if (v___x_1264_ == 0)
{
return v___x_1264_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = lean_usize_of_nat(v___x_1263_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1257_, v_globs_1260_, v___x_1265_, v___x_1266_);
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(lean_object* v_mod_1274_, lean_object* v_self_1275_){
_start:
{
uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1274_, v_self_1275_);
lean_dec_ref(v_self_1275_);
lean_dec(v_mod_1274_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object* v_n_1278_, lean_object* v_mod_1279_, lean_object* v_self_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1279_, v_self_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___boxed(lean_object* v_n_1282_, lean_object* v_mod_1283_, lean_object* v_self_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_Lake_LeanLibConfig_isLocalModule(v_n_1282_, v_mod_1283_, v_self_1284_);
lean_dec_ref(v_self_1284_);
lean_dec(v_mod_1283_);
lean_dec(v_n_1282_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(lean_object* v_mod_1287_, lean_object* v_self_1288_, lean_object* v_as_1289_, size_t v_i_1290_, size_t v_stop_1291_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_eq(v_i_1290_, v_stop_1291_);
if (v___x_1296_ == 0)
{
uint8_t v___x_1297_; uint8_t v___y_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1297_ = 1;
v___x_1300_ = lean_array_uget_borrowed(v_as_1289_, v_i_1290_);
v___x_1301_ = l_Lean_Name_isPrefixOf(v___x_1300_, v_mod_1287_);
if (v___x_1301_ == 0)
{
v___y_1299_ = v___x_1301_;
goto v___jp_1298_;
}
else
{
lean_object* v_globs_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_globs_1302_ = lean_ctor_get(v_self_1288_, 3);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_array_get_size(v_globs_1302_);
v___x_1305_ = lean_nat_dec_lt(v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
goto v___jp_1292_;
}
else
{
if (v___x_1305_ == 0)
{
goto v___jp_1292_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1304_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v___x_1300_, v_globs_1302_, v___x_1306_, v___x_1307_);
v___y_1299_ = v___x_1308_;
goto v___jp_1298_;
}
}
}
v___jp_1298_:
{
if (v___y_1299_ == 0)
{
goto v___jp_1292_;
}
else
{
return v___x_1297_;
}
}
}
else
{
uint8_t v___x_1309_; 
v___x_1309_ = 0;
return v___x_1309_;
}
v___jp_1292_:
{
size_t v___x_1293_; size_t v___x_1294_; 
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1290_, v___x_1293_);
v_i_1290_ = v___x_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(lean_object* v_mod_1310_, lean_object* v_self_1311_, lean_object* v_as_1312_, lean_object* v_i_1313_, lean_object* v_stop_1314_){
_start:
{
size_t v_i_boxed_1315_; size_t v_stop_boxed_1316_; uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_i_boxed_1315_ = lean_unbox_usize(v_i_1313_);
lean_dec(v_i_1313_);
v_stop_boxed_1316_ = lean_unbox_usize(v_stop_1314_);
lean_dec(v_stop_1314_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1310_, v_self_1311_, v_as_1312_, v_i_boxed_1315_, v_stop_boxed_1316_);
lean_dec_ref(v_as_1312_);
lean_dec_ref(v_self_1311_);
lean_dec(v_mod_1310_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object* v_mod_1319_, lean_object* v_self_1320_){
_start:
{
lean_object* v_roots_1321_; lean_object* v_globs_1322_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_roots_1321_ = lean_ctor_get(v_self_1320_, 2);
v_globs_1322_ = lean_ctor_get(v_self_1320_, 3);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_array_get_size(v_globs_1322_);
v___x_1332_ = lean_nat_dec_lt(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
goto v___jp_1323_;
}
else
{
if (v___x_1332_ == 0)
{
goto v___jp_1323_;
}
else
{
size_t v___x_1333_; size_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = lean_usize_of_nat(v___x_1331_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1319_, v_globs_1322_, v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
goto v___jp_1323_;
}
else
{
return v___x_1335_;
}
}
}
v___jp_1323_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v_roots_1321_);
v___x_1326_ = lean_nat_dec_lt(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
return v___x_1326_;
}
else
{
if (v___x_1326_ == 0)
{
return v___x_1326_;
}
else
{
size_t v___x_1327_; size_t v___x_1328_; uint8_t v___x_1329_; 
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1325_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1319_, v_self_1320_, v_roots_1321_, v___x_1327_, v___x_1328_);
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(lean_object* v_mod_1336_, lean_object* v_self_1337_){
_start:
{
uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_res_1338_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1336_, v_self_1337_);
lean_dec_ref(v_self_1337_);
lean_dec(v_mod_1336_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object* v_n_1340_, lean_object* v_mod_1341_, lean_object* v_self_1342_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1341_, v_self_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___boxed(lean_object* v_n_1344_, lean_object* v_mod_1345_, lean_object* v_self_1346_){
_start:
{
uint8_t v_res_1347_; lean_object* v_r_1348_; 
v_res_1347_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_1344_, v_mod_1345_, v_self_1346_);
lean_dec_ref(v_self_1346_);
lean_dec(v_mod_1345_);
lean_dec(v_n_1344_);
v_r_1348_ = lean_box(v_res_1347_);
return v_r_1348_;
}
}
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Casing(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Facets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Glob(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanLibConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
