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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_srcDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_srcDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__3(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_globs___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_globs___proj___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_globs___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_globs___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_globs___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_globs___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_libName___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libName___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_libName___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_libName___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_libName___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_libName___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_needs___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_needs___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_needs___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_needs___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_needs___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_needs___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_precompileModules___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__0 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__1 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__2 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__3 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__0_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__1_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__2_value),((lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__4 = (const lean_object*)&l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___redArg();
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___redArg___boxed(lean_object*);
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
lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0(uint8_t v_shouldExport_1_){
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
LEAN_EXPORT void l_Lake_instInhabitedLeanLibConfig_default___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldExport_1_ = stack[0].m_num;
lean_object* v_res_9_;
v_res_9_ = l_Lake_instInhabitedLeanLibConfig_default___lam__0(v_shouldExport_1_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(lean_object* v_shouldExport_10_){
_start:
{
uint8_t v_shouldExport_boxed_11_; lean_object* v_res_12_; 
v_shouldExport_boxed_11_ = lean_unbox(v_shouldExport_10_);
v_res_12_ = l_Lake_instInhabitedLeanLibConfig_default___lam__0(v_shouldExport_boxed_11_);
return v_res_12_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(size_t v_sz_13_, size_t v_i_14_, lean_object* v_bs_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = lean_usize_dec_lt(v_i_14_, v_sz_13_);
if (v___x_16_ == 0)
{
return v_bs_15_;
}
else
{
lean_object* v_v_17_; lean_object* v___x_18_; lean_object* v_bs_x27_19_; lean_object* v___x_20_; size_t v___x_21_; size_t v___x_22_; lean_object* v___x_23_; 
v_v_17_ = lean_array_uget(v_bs_15_, v_i_14_);
v___x_18_ = lean_unsigned_to_nat(0u);
v_bs_x27_19_ = lean_array_uset(v_bs_15_, v_i_14_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v_v_17_);
v___x_21_ = ((size_t)1ULL);
v___x_22_ = lean_usize_add(v_i_14_, v___x_21_);
v___x_23_ = lean_array_uset(v_bs_x27_19_, v_i_14_, v___x_20_);
v_i_14_ = v___x_22_;
v_bs_15_ = v___x_23_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_13_ = stack[0].m_num;
size_t v_i_14_ = stack[1].m_num;
lean_object* v_bs_15_ = stack[2].m_obj;
lean_object* v_res_25_;
v_res_25_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_13_, v_i_14_, v_bs_15_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0___boxed(lean_object* v_sz_26_, lean_object* v_i_27_, lean_object* v_bs_28_){
_start:
{
size_t v_sz_boxed_29_; size_t v_i_boxed_30_; lean_object* v_res_31_; 
v_sz_boxed_29_ = lean_unbox_usize(v_sz_26_);
lean_dec(v_sz_26_);
v_i_boxed_30_ = lean_unbox_usize(v_i_27_);
lean_dec(v_i_27_);
v_res_31_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_boxed_29_, v_i_boxed_30_, v_bs_28_);
return v_res_31_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = l_Lake_LeanLib_leanArtsFacet;
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_mk_empty_array_with_capacity(v___x_38_);
v___x_40_ = lean_array_push(v___x_39_, v___x_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig_default(lean_object* v_name_41_){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; size_t v_sz_48_; size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___f_42_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_43_ = l_Lake_instInhabitedLeanConfig_default;
v___x_44_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_45_);
v___x_47_ = lean_array_push(v___x_46_, v_name_41_);
v_sz_48_ = lean_array_size(v___x_47_);
v___x_49_ = ((size_t)0ULL);
lean_inc_ref(v___x_47_);
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_48_, v___x_49_, v___x_47_);
v___x_51_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_52_ = 0;
v___x_53_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
v___x_54_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
v___x_55_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v___x_55_, 0, v___x_43_);
lean_ctor_set(v___x_55_, 1, v___x_44_);
lean_ctor_set(v___x_55_, 2, v___x_47_);
lean_ctor_set(v___x_55_, 3, v___x_50_);
lean_ctor_set(v___x_55_, 4, v___x_51_);
lean_ctor_set(v___x_55_, 5, v___x_53_);
lean_ctor_set(v___x_55_, 6, v___x_53_);
lean_ctor_set(v___x_55_, 7, v___x_54_);
lean_ctor_set(v___x_55_, 8, v___f_42_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*9, v___x_52_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*9 + 1, v___x_52_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*9 + 2, v___x_52_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*9 + 3, v___x_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanLibConfig(lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lake_instInhabitedLeanLibConfig_default(v_a_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0(lean_object* v_cfg_58_){
_start:
{
lean_object* v_srcDir_59_; 
v_srcDir_59_ = lean_ctor_get(v_cfg_58_, 1);
lean_inc_ref(v_srcDir_59_);
return v_srcDir_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0(v_cfg_60_);
lean_dec_ref(v_cfg_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__1(lean_object* v_val_62_, lean_object* v_cfg_63_){
_start:
{
lean_object* v_toLeanConfig_64_; lean_object* v_roots_65_; lean_object* v_globs_66_; lean_object* v_libName_67_; uint8_t v_libPrefixOnWindows_68_; lean_object* v_needs_69_; lean_object* v_extraDepTargets_70_; uint8_t v_precompileLibrary_71_; uint8_t v_precompileModules_72_; lean_object* v_defaultFacets_73_; lean_object* v_nativeFacets_74_; uint8_t v_allowImportAll_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_toLeanConfig_64_ = lean_ctor_get(v_cfg_63_, 0);
v_roots_65_ = lean_ctor_get(v_cfg_63_, 2);
v_globs_66_ = lean_ctor_get(v_cfg_63_, 3);
v_libName_67_ = lean_ctor_get(v_cfg_63_, 4);
v_libPrefixOnWindows_68_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*9);
v_needs_69_ = lean_ctor_get(v_cfg_63_, 5);
v_extraDepTargets_70_ = lean_ctor_get(v_cfg_63_, 6);
v_precompileLibrary_71_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*9 + 1);
v_precompileModules_72_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*9 + 2);
v_defaultFacets_73_ = lean_ctor_get(v_cfg_63_, 7);
v_nativeFacets_74_ = lean_ctor_get(v_cfg_63_, 8);
v_allowImportAll_75_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*9 + 3);
v_isSharedCheck_82_ = !lean_is_exclusive(v_cfg_63_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v_cfg_63_, 1);
lean_dec(v_unused_83_);
v___x_77_ = v_cfg_63_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_nativeFacets_74_);
lean_inc(v_defaultFacets_73_);
lean_inc(v_extraDepTargets_70_);
lean_inc(v_needs_69_);
lean_inc(v_libName_67_);
lean_inc(v_globs_66_);
lean_inc(v_roots_65_);
lean_inc(v_toLeanConfig_64_);
lean_dec(v_cfg_63_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v_val_62_);
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_toLeanConfig_64_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_val_62_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_roots_65_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_globs_66_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v_libName_67_);
lean_ctor_set(v_reuseFailAlloc_81_, 5, v_needs_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 6, v_extraDepTargets_70_);
lean_ctor_set(v_reuseFailAlloc_81_, 7, v_defaultFacets_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 8, v_nativeFacets_74_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*9, v_libPrefixOnWindows_68_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*9 + 1, v_precompileLibrary_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*9 + 2, v_precompileModules_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*9 + 3, v_allowImportAll_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__2(lean_object* v_f_84_, lean_object* v_cfg_85_){
_start:
{
lean_object* v_toLeanConfig_86_; lean_object* v_srcDir_87_; lean_object* v_roots_88_; lean_object* v_globs_89_; lean_object* v_libName_90_; uint8_t v_libPrefixOnWindows_91_; lean_object* v_needs_92_; lean_object* v_extraDepTargets_93_; uint8_t v_precompileLibrary_94_; uint8_t v_precompileModules_95_; lean_object* v_defaultFacets_96_; lean_object* v_nativeFacets_97_; uint8_t v_allowImportAll_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_toLeanConfig_86_ = lean_ctor_get(v_cfg_85_, 0);
v_srcDir_87_ = lean_ctor_get(v_cfg_85_, 1);
v_roots_88_ = lean_ctor_get(v_cfg_85_, 2);
v_globs_89_ = lean_ctor_get(v_cfg_85_, 3);
v_libName_90_ = lean_ctor_get(v_cfg_85_, 4);
v_libPrefixOnWindows_91_ = lean_ctor_get_uint8(v_cfg_85_, sizeof(void*)*9);
v_needs_92_ = lean_ctor_get(v_cfg_85_, 5);
v_extraDepTargets_93_ = lean_ctor_get(v_cfg_85_, 6);
v_precompileLibrary_94_ = lean_ctor_get_uint8(v_cfg_85_, sizeof(void*)*9 + 1);
v_precompileModules_95_ = lean_ctor_get_uint8(v_cfg_85_, sizeof(void*)*9 + 2);
v_defaultFacets_96_ = lean_ctor_get(v_cfg_85_, 7);
v_nativeFacets_97_ = lean_ctor_get(v_cfg_85_, 8);
v_allowImportAll_98_ = lean_ctor_get_uint8(v_cfg_85_, sizeof(void*)*9 + 3);
v_isSharedCheck_106_ = !lean_is_exclusive(v_cfg_85_);
if (v_isSharedCheck_106_ == 0)
{
v___x_100_ = v_cfg_85_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_nativeFacets_97_);
lean_inc(v_defaultFacets_96_);
lean_inc(v_extraDepTargets_93_);
lean_inc(v_needs_92_);
lean_inc(v_libName_90_);
lean_inc(v_globs_89_);
lean_inc(v_roots_88_);
lean_inc(v_srcDir_87_);
lean_inc(v_toLeanConfig_86_);
lean_dec(v_cfg_85_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_apply_1(v_f_84_, v_srcDir_87_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_toLeanConfig_86_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_roots_88_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_globs_89_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v_libName_90_);
lean_ctor_set(v_reuseFailAlloc_105_, 5, v_needs_92_);
lean_ctor_set(v_reuseFailAlloc_105_, 6, v_extraDepTargets_93_);
lean_ctor_set(v_reuseFailAlloc_105_, 7, v_defaultFacets_96_);
lean_ctor_set(v_reuseFailAlloc_105_, 8, v_nativeFacets_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*9, v_libPrefixOnWindows_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*9 + 1, v_precompileLibrary_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*9 + 2, v_precompileModules_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*9 + 3, v_allowImportAll_98_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3(lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3___boxed(lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3(v_x_109_);
lean_dec_ref(v_x_109_);
return v_res_110_;
}
}
lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg(){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__4));
return v___x_121_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_srcDir___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_122_;
v_res_122_ = l_Lake_LeanLibConfig_srcDir___proj___redArg();
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___boxed(lean_object* v___dummy_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lake_LeanLibConfig_srcDir___proj___redArg();
return v_res_124_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lake_LeanLibConfig_srcDir___proj___redArg();
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object* v_name_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lake_LeanLibConfig_srcDir___proj___closed__0, &l_Lake_LeanLibConfig_srcDir___proj___closed__0_once, _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object* v_name_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_128_);
lean_dec(v_name_128_);
return v_res_129_;
}
}
lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lake_LeanLibConfig_srcDir___proj___closed__0, &l_Lake_LeanLibConfig_srcDir___proj___closed__0_once, _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0);
return v___x_131_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_srcDir_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_132_;
v_res_132_ = l_Lake_LeanLibConfig_srcDir_instConfigField___redArg();
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___redArg___boxed(lean_object* v___dummy_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lake_LeanLibConfig_srcDir_instConfigField___redArg();
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object* v_name_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lake_LeanLibConfig_srcDir___proj___closed__0, &l_Lake_LeanLibConfig_srcDir___proj___closed__0_once, _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object* v_name_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_137_);
lean_dec(v_name_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object* v_cfg_139_){
_start:
{
lean_object* v_roots_140_; 
v_roots_140_ = lean_ctor_get(v_cfg_139_, 2);
lean_inc_ref(v_roots_140_);
return v_roots_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object* v_cfg_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_141_);
lean_dec_ref(v_cfg_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object* v_val_143_, lean_object* v_cfg_144_){
_start:
{
lean_object* v_toLeanConfig_145_; lean_object* v_srcDir_146_; lean_object* v_globs_147_; lean_object* v_libName_148_; uint8_t v_libPrefixOnWindows_149_; lean_object* v_needs_150_; lean_object* v_extraDepTargets_151_; uint8_t v_precompileLibrary_152_; uint8_t v_precompileModules_153_; lean_object* v_defaultFacets_154_; lean_object* v_nativeFacets_155_; uint8_t v_allowImportAll_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_toLeanConfig_145_ = lean_ctor_get(v_cfg_144_, 0);
v_srcDir_146_ = lean_ctor_get(v_cfg_144_, 1);
v_globs_147_ = lean_ctor_get(v_cfg_144_, 3);
v_libName_148_ = lean_ctor_get(v_cfg_144_, 4);
v_libPrefixOnWindows_149_ = lean_ctor_get_uint8(v_cfg_144_, sizeof(void*)*9);
v_needs_150_ = lean_ctor_get(v_cfg_144_, 5);
v_extraDepTargets_151_ = lean_ctor_get(v_cfg_144_, 6);
v_precompileLibrary_152_ = lean_ctor_get_uint8(v_cfg_144_, sizeof(void*)*9 + 1);
v_precompileModules_153_ = lean_ctor_get_uint8(v_cfg_144_, sizeof(void*)*9 + 2);
v_defaultFacets_154_ = lean_ctor_get(v_cfg_144_, 7);
v_nativeFacets_155_ = lean_ctor_get(v_cfg_144_, 8);
v_allowImportAll_156_ = lean_ctor_get_uint8(v_cfg_144_, sizeof(void*)*9 + 3);
v_isSharedCheck_163_ = !lean_is_exclusive(v_cfg_144_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v_cfg_144_, 2);
lean_dec(v_unused_164_);
v___x_158_ = v_cfg_144_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_nativeFacets_155_);
lean_inc(v_defaultFacets_154_);
lean_inc(v_extraDepTargets_151_);
lean_inc(v_needs_150_);
lean_inc(v_libName_148_);
lean_inc(v_globs_147_);
lean_inc(v_srcDir_146_);
lean_inc(v_toLeanConfig_145_);
lean_dec(v_cfg_144_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 2, v_val_143_);
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_toLeanConfig_145_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_srcDir_146_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_val_143_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_globs_147_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_libName_148_);
lean_ctor_set(v_reuseFailAlloc_162_, 5, v_needs_150_);
lean_ctor_set(v_reuseFailAlloc_162_, 6, v_extraDepTargets_151_);
lean_ctor_set(v_reuseFailAlloc_162_, 7, v_defaultFacets_154_);
lean_ctor_set(v_reuseFailAlloc_162_, 8, v_nativeFacets_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*9, v_libPrefixOnWindows_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*9 + 1, v_precompileLibrary_152_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*9 + 2, v_precompileModules_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*9 + 3, v_allowImportAll_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object* v_f_165_, lean_object* v_cfg_166_){
_start:
{
lean_object* v_toLeanConfig_167_; lean_object* v_srcDir_168_; lean_object* v_roots_169_; lean_object* v_globs_170_; lean_object* v_libName_171_; uint8_t v_libPrefixOnWindows_172_; lean_object* v_needs_173_; lean_object* v_extraDepTargets_174_; uint8_t v_precompileLibrary_175_; uint8_t v_precompileModules_176_; lean_object* v_defaultFacets_177_; lean_object* v_nativeFacets_178_; uint8_t v_allowImportAll_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_toLeanConfig_167_ = lean_ctor_get(v_cfg_166_, 0);
v_srcDir_168_ = lean_ctor_get(v_cfg_166_, 1);
v_roots_169_ = lean_ctor_get(v_cfg_166_, 2);
v_globs_170_ = lean_ctor_get(v_cfg_166_, 3);
v_libName_171_ = lean_ctor_get(v_cfg_166_, 4);
v_libPrefixOnWindows_172_ = lean_ctor_get_uint8(v_cfg_166_, sizeof(void*)*9);
v_needs_173_ = lean_ctor_get(v_cfg_166_, 5);
v_extraDepTargets_174_ = lean_ctor_get(v_cfg_166_, 6);
v_precompileLibrary_175_ = lean_ctor_get_uint8(v_cfg_166_, sizeof(void*)*9 + 1);
v_precompileModules_176_ = lean_ctor_get_uint8(v_cfg_166_, sizeof(void*)*9 + 2);
v_defaultFacets_177_ = lean_ctor_get(v_cfg_166_, 7);
v_nativeFacets_178_ = lean_ctor_get(v_cfg_166_, 8);
v_allowImportAll_179_ = lean_ctor_get_uint8(v_cfg_166_, sizeof(void*)*9 + 3);
v_isSharedCheck_187_ = !lean_is_exclusive(v_cfg_166_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v_cfg_166_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_nativeFacets_178_);
lean_inc(v_defaultFacets_177_);
lean_inc(v_extraDepTargets_174_);
lean_inc(v_needs_173_);
lean_inc(v_libName_171_);
lean_inc(v_globs_170_);
lean_inc(v_roots_169_);
lean_inc(v_srcDir_168_);
lean_inc(v_toLeanConfig_167_);
lean_dec(v_cfg_166_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_apply_1(v_f_165_, v_roots_169_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_toLeanConfig_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_srcDir_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_globs_170_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_libName_171_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_needs_173_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v_extraDepTargets_174_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v_defaultFacets_177_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v_nativeFacets_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*9, v_libPrefixOnWindows_172_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*9 + 1, v_precompileLibrary_175_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*9 + 2, v_precompileModules_176_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*9 + 3, v_allowImportAll_179_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object* v_name_188_, lean_object* v_x_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_mk_empty_array_with_capacity(v___x_190_);
v___x_192_ = lean_array_push(v___x_191_, v_name_188_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object* v_name_193_, lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_193_, v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object* v_name_199_){
_start:
{
lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; 
v___f_200_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__0));
v___f_201_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__1));
v___f_202_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__2));
v___f_203_ = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_roots___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_203_, 0, v_name_199_);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v___f_200_);
lean_ctor_set(v___x_204_, 1, v___f_201_);
lean_ctor_set(v___x_204_, 2, v___f_202_);
lean_ctor_set(v___x_204_, 3, v___f_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object* v_name_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lake_LeanLibConfig_roots___proj(v_name_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__0(lean_object* v_cfg_207_){
_start:
{
lean_object* v_globs_208_; 
v_globs_208_ = lean_ctor_get(v_cfg_207_, 3);
lean_inc_ref(v_globs_208_);
return v_globs_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__0___boxed(lean_object* v_cfg_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_LeanLibConfig_globs___proj___redArg___lam__0(v_cfg_209_);
lean_dec_ref(v_cfg_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__1(lean_object* v_val_211_, lean_object* v_cfg_212_){
_start:
{
lean_object* v_toLeanConfig_213_; lean_object* v_srcDir_214_; lean_object* v_roots_215_; lean_object* v_libName_216_; uint8_t v_libPrefixOnWindows_217_; lean_object* v_needs_218_; lean_object* v_extraDepTargets_219_; uint8_t v_precompileLibrary_220_; uint8_t v_precompileModules_221_; lean_object* v_defaultFacets_222_; lean_object* v_nativeFacets_223_; uint8_t v_allowImportAll_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_toLeanConfig_213_ = lean_ctor_get(v_cfg_212_, 0);
v_srcDir_214_ = lean_ctor_get(v_cfg_212_, 1);
v_roots_215_ = lean_ctor_get(v_cfg_212_, 2);
v_libName_216_ = lean_ctor_get(v_cfg_212_, 4);
v_libPrefixOnWindows_217_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*9);
v_needs_218_ = lean_ctor_get(v_cfg_212_, 5);
v_extraDepTargets_219_ = lean_ctor_get(v_cfg_212_, 6);
v_precompileLibrary_220_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*9 + 1);
v_precompileModules_221_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*9 + 2);
v_defaultFacets_222_ = lean_ctor_get(v_cfg_212_, 7);
v_nativeFacets_223_ = lean_ctor_get(v_cfg_212_, 8);
v_allowImportAll_224_ = lean_ctor_get_uint8(v_cfg_212_, sizeof(void*)*9 + 3);
v_isSharedCheck_231_ = !lean_is_exclusive(v_cfg_212_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_cfg_212_, 3);
lean_dec(v_unused_232_);
v___x_226_ = v_cfg_212_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_nativeFacets_223_);
lean_inc(v_defaultFacets_222_);
lean_inc(v_extraDepTargets_219_);
lean_inc(v_needs_218_);
lean_inc(v_libName_216_);
lean_inc(v_roots_215_);
lean_inc(v_srcDir_214_);
lean_inc(v_toLeanConfig_213_);
lean_dec(v_cfg_212_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 3, v_val_211_);
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_toLeanConfig_213_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_srcDir_214_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_roots_215_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_val_211_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_libName_216_);
lean_ctor_set(v_reuseFailAlloc_230_, 5, v_needs_218_);
lean_ctor_set(v_reuseFailAlloc_230_, 6, v_extraDepTargets_219_);
lean_ctor_set(v_reuseFailAlloc_230_, 7, v_defaultFacets_222_);
lean_ctor_set(v_reuseFailAlloc_230_, 8, v_nativeFacets_223_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*9, v_libPrefixOnWindows_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*9 + 1, v_precompileLibrary_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*9 + 2, v_precompileModules_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*9 + 3, v_allowImportAll_224_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__2(lean_object* v_f_233_, lean_object* v_cfg_234_){
_start:
{
lean_object* v_toLeanConfig_235_; lean_object* v_srcDir_236_; lean_object* v_roots_237_; lean_object* v_globs_238_; lean_object* v_libName_239_; uint8_t v_libPrefixOnWindows_240_; lean_object* v_needs_241_; lean_object* v_extraDepTargets_242_; uint8_t v_precompileLibrary_243_; uint8_t v_precompileModules_244_; lean_object* v_defaultFacets_245_; lean_object* v_nativeFacets_246_; uint8_t v_allowImportAll_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_255_; 
v_toLeanConfig_235_ = lean_ctor_get(v_cfg_234_, 0);
v_srcDir_236_ = lean_ctor_get(v_cfg_234_, 1);
v_roots_237_ = lean_ctor_get(v_cfg_234_, 2);
v_globs_238_ = lean_ctor_get(v_cfg_234_, 3);
v_libName_239_ = lean_ctor_get(v_cfg_234_, 4);
v_libPrefixOnWindows_240_ = lean_ctor_get_uint8(v_cfg_234_, sizeof(void*)*9);
v_needs_241_ = lean_ctor_get(v_cfg_234_, 5);
v_extraDepTargets_242_ = lean_ctor_get(v_cfg_234_, 6);
v_precompileLibrary_243_ = lean_ctor_get_uint8(v_cfg_234_, sizeof(void*)*9 + 1);
v_precompileModules_244_ = lean_ctor_get_uint8(v_cfg_234_, sizeof(void*)*9 + 2);
v_defaultFacets_245_ = lean_ctor_get(v_cfg_234_, 7);
v_nativeFacets_246_ = lean_ctor_get(v_cfg_234_, 8);
v_allowImportAll_247_ = lean_ctor_get_uint8(v_cfg_234_, sizeof(void*)*9 + 3);
v_isSharedCheck_255_ = !lean_is_exclusive(v_cfg_234_);
if (v_isSharedCheck_255_ == 0)
{
v___x_249_ = v_cfg_234_;
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_nativeFacets_246_);
lean_inc(v_defaultFacets_245_);
lean_inc(v_extraDepTargets_242_);
lean_inc(v_needs_241_);
lean_inc(v_libName_239_);
lean_inc(v_globs_238_);
lean_inc(v_roots_237_);
lean_inc(v_srcDir_236_);
lean_inc(v_toLeanConfig_235_);
lean_dec(v_cfg_234_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_apply_1(v_f_233_, v_globs_238_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 3, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_toLeanConfig_235_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_srcDir_236_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_roots_237_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_libName_239_);
lean_ctor_set(v_reuseFailAlloc_254_, 5, v_needs_241_);
lean_ctor_set(v_reuseFailAlloc_254_, 6, v_extraDepTargets_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 7, v_defaultFacets_245_);
lean_ctor_set(v_reuseFailAlloc_254_, 8, v_nativeFacets_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_254_, sizeof(void*)*9, v_libPrefixOnWindows_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_254_, sizeof(void*)*9 + 1, v_precompileLibrary_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_254_, sizeof(void*)*9 + 2, v_precompileModules_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_254_, sizeof(void*)*9 + 3, v_allowImportAll_247_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__3(lean_object* v_x_256_){
_start:
{
lean_object* v_roots_257_; size_t v_sz_258_; size_t v___x_259_; lean_object* v___x_260_; 
v_roots_257_ = lean_ctor_get(v_x_256_, 2);
lean_inc_ref(v_roots_257_);
lean_dec_ref(v_x_256_);
v_sz_258_ = lean_array_size(v_roots_257_);
v___x_259_ = ((size_t)0ULL);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_258_, v___x_259_, v_roots_257_);
return v___x_260_;
}
}
lean_object* l_Lake_LeanLibConfig_globs___proj___redArg(){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_Lake_LeanLibConfig_globs___proj___redArg___closed__4));
return v___x_271_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_globs___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_272_;
v_res_272_ = l_Lake_LeanLibConfig_globs___proj___redArg();
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___boxed(lean_object* v___dummy_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_LeanLibConfig_globs___proj___redArg();
return v_res_274_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_globs___proj___closed__0(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lake_LeanLibConfig_globs___proj___redArg();
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object* v_name_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lake_LeanLibConfig_globs___proj___closed__0, &l_Lake_LeanLibConfig_globs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_globs___proj___closed__0);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object* v_name_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lake_LeanLibConfig_globs___proj(v_name_278_);
lean_dec(v_name_278_);
return v_res_279_;
}
}
lean_object* l_Lake_LeanLibConfig_globs_instConfigField___redArg(){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lake_LeanLibConfig_globs___proj___closed__0, &l_Lake_LeanLibConfig_globs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_globs___proj___closed__0);
return v___x_281_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_globs_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_282_;
v_res_282_ = l_Lake_LeanLibConfig_globs_instConfigField___redArg();
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___redArg___boxed(lean_object* v___dummy_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lake_LeanLibConfig_globs_instConfigField___redArg();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object* v_name_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lake_LeanLibConfig_globs___proj___closed__0, &l_Lake_LeanLibConfig_globs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_globs___proj___closed__0);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object* v_name_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_287_);
lean_dec(v_name_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__0(lean_object* v_cfg_289_){
_start:
{
lean_object* v_libName_290_; 
v_libName_290_ = lean_ctor_get(v_cfg_289_, 4);
lean_inc_ref(v_libName_290_);
return v_libName_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__0___boxed(lean_object* v_cfg_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_LeanLibConfig_libName___proj___redArg___lam__0(v_cfg_291_);
lean_dec_ref(v_cfg_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__1(lean_object* v_val_293_, lean_object* v_cfg_294_){
_start:
{
lean_object* v_toLeanConfig_295_; lean_object* v_srcDir_296_; lean_object* v_roots_297_; lean_object* v_globs_298_; uint8_t v_libPrefixOnWindows_299_; lean_object* v_needs_300_; lean_object* v_extraDepTargets_301_; uint8_t v_precompileLibrary_302_; uint8_t v_precompileModules_303_; lean_object* v_defaultFacets_304_; lean_object* v_nativeFacets_305_; uint8_t v_allowImportAll_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_toLeanConfig_295_ = lean_ctor_get(v_cfg_294_, 0);
v_srcDir_296_ = lean_ctor_get(v_cfg_294_, 1);
v_roots_297_ = lean_ctor_get(v_cfg_294_, 2);
v_globs_298_ = lean_ctor_get(v_cfg_294_, 3);
v_libPrefixOnWindows_299_ = lean_ctor_get_uint8(v_cfg_294_, sizeof(void*)*9);
v_needs_300_ = lean_ctor_get(v_cfg_294_, 5);
v_extraDepTargets_301_ = lean_ctor_get(v_cfg_294_, 6);
v_precompileLibrary_302_ = lean_ctor_get_uint8(v_cfg_294_, sizeof(void*)*9 + 1);
v_precompileModules_303_ = lean_ctor_get_uint8(v_cfg_294_, sizeof(void*)*9 + 2);
v_defaultFacets_304_ = lean_ctor_get(v_cfg_294_, 7);
v_nativeFacets_305_ = lean_ctor_get(v_cfg_294_, 8);
v_allowImportAll_306_ = lean_ctor_get_uint8(v_cfg_294_, sizeof(void*)*9 + 3);
v_isSharedCheck_313_ = !lean_is_exclusive(v_cfg_294_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v_cfg_294_, 4);
lean_dec(v_unused_314_);
v___x_308_ = v_cfg_294_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_nativeFacets_305_);
lean_inc(v_defaultFacets_304_);
lean_inc(v_extraDepTargets_301_);
lean_inc(v_needs_300_);
lean_inc(v_globs_298_);
lean_inc(v_roots_297_);
lean_inc(v_srcDir_296_);
lean_inc(v_toLeanConfig_295_);
lean_dec(v_cfg_294_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 4, v_val_293_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_toLeanConfig_295_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_srcDir_296_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_roots_297_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_globs_298_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_val_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_needs_300_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_extraDepTargets_301_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_defaultFacets_304_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_nativeFacets_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9, v_libPrefixOnWindows_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9 + 1, v_precompileLibrary_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9 + 2, v_precompileModules_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*9 + 3, v_allowImportAll_306_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__2(lean_object* v_f_315_, lean_object* v_cfg_316_){
_start:
{
lean_object* v_toLeanConfig_317_; lean_object* v_srcDir_318_; lean_object* v_roots_319_; lean_object* v_globs_320_; lean_object* v_libName_321_; uint8_t v_libPrefixOnWindows_322_; lean_object* v_needs_323_; lean_object* v_extraDepTargets_324_; uint8_t v_precompileLibrary_325_; uint8_t v_precompileModules_326_; lean_object* v_defaultFacets_327_; lean_object* v_nativeFacets_328_; uint8_t v_allowImportAll_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
v_toLeanConfig_317_ = lean_ctor_get(v_cfg_316_, 0);
v_srcDir_318_ = lean_ctor_get(v_cfg_316_, 1);
v_roots_319_ = lean_ctor_get(v_cfg_316_, 2);
v_globs_320_ = lean_ctor_get(v_cfg_316_, 3);
v_libName_321_ = lean_ctor_get(v_cfg_316_, 4);
v_libPrefixOnWindows_322_ = lean_ctor_get_uint8(v_cfg_316_, sizeof(void*)*9);
v_needs_323_ = lean_ctor_get(v_cfg_316_, 5);
v_extraDepTargets_324_ = lean_ctor_get(v_cfg_316_, 6);
v_precompileLibrary_325_ = lean_ctor_get_uint8(v_cfg_316_, sizeof(void*)*9 + 1);
v_precompileModules_326_ = lean_ctor_get_uint8(v_cfg_316_, sizeof(void*)*9 + 2);
v_defaultFacets_327_ = lean_ctor_get(v_cfg_316_, 7);
v_nativeFacets_328_ = lean_ctor_get(v_cfg_316_, 8);
v_allowImportAll_329_ = lean_ctor_get_uint8(v_cfg_316_, sizeof(void*)*9 + 3);
v_isSharedCheck_337_ = !lean_is_exclusive(v_cfg_316_);
if (v_isSharedCheck_337_ == 0)
{
v___x_331_ = v_cfg_316_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_nativeFacets_328_);
lean_inc(v_defaultFacets_327_);
lean_inc(v_extraDepTargets_324_);
lean_inc(v_needs_323_);
lean_inc(v_libName_321_);
lean_inc(v_globs_320_);
lean_inc(v_roots_319_);
lean_inc(v_srcDir_318_);
lean_inc(v_toLeanConfig_317_);
lean_dec(v_cfg_316_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_apply_1(v_f_315_, v_libName_321_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_toLeanConfig_317_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_srcDir_318_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_roots_319_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_globs_320_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_336_, 5, v_needs_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 6, v_extraDepTargets_324_);
lean_ctor_set(v_reuseFailAlloc_336_, 7, v_defaultFacets_327_);
lean_ctor_set(v_reuseFailAlloc_336_, 8, v_nativeFacets_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*9, v_libPrefixOnWindows_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*9 + 1, v_precompileLibrary_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*9 + 2, v_precompileModules_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*9 + 3, v_allowImportAll_329_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__3(lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__3___boxed(lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lake_LeanLibConfig_libName___proj___redArg___lam__3(v_x_340_);
lean_dec_ref(v_x_340_);
return v_res_341_;
}
}
lean_object* l_Lake_LeanLibConfig_libName___proj___redArg(){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_Lake_LeanLibConfig_libName___proj___redArg___closed__4));
return v___x_352_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libName___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_353_;
v_res_353_ = l_Lake_LeanLibConfig_libName___proj___redArg();
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___boxed(lean_object* v___dummy_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_LeanLibConfig_libName___proj___redArg();
return v_res_355_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_libName___proj___closed__0(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lake_LeanLibConfig_libName___proj___redArg();
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object* v_name_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lake_LeanLibConfig_libName___proj___closed__0, &l_Lake_LeanLibConfig_libName___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libName___proj___closed__0);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object* v_name_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lake_LeanLibConfig_libName___proj(v_name_359_);
lean_dec(v_name_359_);
return v_res_360_;
}
}
lean_object* l_Lake_LeanLibConfig_libName_instConfigField___redArg(){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lake_LeanLibConfig_libName___proj___closed__0, &l_Lake_LeanLibConfig_libName___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libName___proj___closed__0);
return v___x_362_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libName_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_363_;
v_res_363_ = l_Lake_LeanLibConfig_libName_instConfigField___redArg();
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___redArg___boxed(lean_object* v___dummy_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lake_LeanLibConfig_libName_instConfigField___redArg();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object* v_name_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l_Lake_LeanLibConfig_libName___proj___closed__0, &l_Lake_LeanLibConfig_libName___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libName___proj___closed__0);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object* v_name_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_368_);
lean_dec(v_name_368_);
return v_res_369_;
}
}
uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object* v_cfg_370_){
_start:
{
uint8_t v_libPrefixOnWindows_371_; 
v_libPrefixOnWindows_371_ = lean_ctor_get_uint8(v_cfg_370_, sizeof(void*)*9);
return v_libPrefixOnWindows_371_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_370_ = stack[0].m_obj;
uint8_t v_res_372_;
v_res_372_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_370_);
stack->m_num = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object* v_cfg_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_373_);
lean_dec_ref(v_cfg_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t v_val_376_, lean_object* v_cfg_377_){
_start:
{
lean_object* v_toLeanConfig_378_; lean_object* v_srcDir_379_; lean_object* v_roots_380_; lean_object* v_globs_381_; lean_object* v_libName_382_; lean_object* v_needs_383_; lean_object* v_extraDepTargets_384_; uint8_t v_precompileLibrary_385_; uint8_t v_precompileModules_386_; lean_object* v_defaultFacets_387_; lean_object* v_nativeFacets_388_; uint8_t v_allowImportAll_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v_toLeanConfig_378_ = lean_ctor_get(v_cfg_377_, 0);
v_srcDir_379_ = lean_ctor_get(v_cfg_377_, 1);
v_roots_380_ = lean_ctor_get(v_cfg_377_, 2);
v_globs_381_ = lean_ctor_get(v_cfg_377_, 3);
v_libName_382_ = lean_ctor_get(v_cfg_377_, 4);
v_needs_383_ = lean_ctor_get(v_cfg_377_, 5);
v_extraDepTargets_384_ = lean_ctor_get(v_cfg_377_, 6);
v_precompileLibrary_385_ = lean_ctor_get_uint8(v_cfg_377_, sizeof(void*)*9 + 1);
v_precompileModules_386_ = lean_ctor_get_uint8(v_cfg_377_, sizeof(void*)*9 + 2);
v_defaultFacets_387_ = lean_ctor_get(v_cfg_377_, 7);
v_nativeFacets_388_ = lean_ctor_get(v_cfg_377_, 8);
v_allowImportAll_389_ = lean_ctor_get_uint8(v_cfg_377_, sizeof(void*)*9 + 3);
v_isSharedCheck_396_ = !lean_is_exclusive(v_cfg_377_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v_cfg_377_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_nativeFacets_388_);
lean_inc(v_defaultFacets_387_);
lean_inc(v_extraDepTargets_384_);
lean_inc(v_needs_383_);
lean_inc(v_libName_382_);
lean_inc(v_globs_381_);
lean_inc(v_roots_380_);
lean_inc(v_srcDir_379_);
lean_inc(v_toLeanConfig_378_);
lean_dec(v_cfg_377_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_toLeanConfig_378_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_srcDir_379_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_roots_380_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_globs_381_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_libName_382_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v_needs_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 6, v_extraDepTargets_384_);
lean_ctor_set(v_reuseFailAlloc_395_, 7, v_defaultFacets_387_);
lean_ctor_set(v_reuseFailAlloc_395_, 8, v_nativeFacets_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_395_, sizeof(void*)*9 + 1, v_precompileLibrary_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_395_, sizeof(void*)*9 + 2, v_precompileModules_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_395_, sizeof(void*)*9 + 3, v_allowImportAll_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*9, v_val_376_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_376_ = stack[0].m_num;
lean_object* v_cfg_377_ = stack[1].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_376_, v_cfg_377_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object* v_val_398_, lean_object* v_cfg_399_){
_start:
{
uint8_t v_val_77__boxed_400_; lean_object* v_res_401_; 
v_val_77__boxed_400_ = lean_unbox(v_val_398_);
v_res_401_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_77__boxed_400_, v_cfg_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object* v_f_402_, lean_object* v_cfg_403_){
_start:
{
lean_object* v_toLeanConfig_404_; lean_object* v_srcDir_405_; lean_object* v_roots_406_; lean_object* v_globs_407_; lean_object* v_libName_408_; uint8_t v_libPrefixOnWindows_409_; lean_object* v_needs_410_; lean_object* v_extraDepTargets_411_; uint8_t v_precompileLibrary_412_; uint8_t v_precompileModules_413_; lean_object* v_defaultFacets_414_; lean_object* v_nativeFacets_415_; uint8_t v_allowImportAll_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_426_; 
v_toLeanConfig_404_ = lean_ctor_get(v_cfg_403_, 0);
v_srcDir_405_ = lean_ctor_get(v_cfg_403_, 1);
v_roots_406_ = lean_ctor_get(v_cfg_403_, 2);
v_globs_407_ = lean_ctor_get(v_cfg_403_, 3);
v_libName_408_ = lean_ctor_get(v_cfg_403_, 4);
v_libPrefixOnWindows_409_ = lean_ctor_get_uint8(v_cfg_403_, sizeof(void*)*9);
v_needs_410_ = lean_ctor_get(v_cfg_403_, 5);
v_extraDepTargets_411_ = lean_ctor_get(v_cfg_403_, 6);
v_precompileLibrary_412_ = lean_ctor_get_uint8(v_cfg_403_, sizeof(void*)*9 + 1);
v_precompileModules_413_ = lean_ctor_get_uint8(v_cfg_403_, sizeof(void*)*9 + 2);
v_defaultFacets_414_ = lean_ctor_get(v_cfg_403_, 7);
v_nativeFacets_415_ = lean_ctor_get(v_cfg_403_, 8);
v_allowImportAll_416_ = lean_ctor_get_uint8(v_cfg_403_, sizeof(void*)*9 + 3);
v_isSharedCheck_426_ = !lean_is_exclusive(v_cfg_403_);
if (v_isSharedCheck_426_ == 0)
{
v___x_418_ = v_cfg_403_;
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_nativeFacets_415_);
lean_inc(v_defaultFacets_414_);
lean_inc(v_extraDepTargets_411_);
lean_inc(v_needs_410_);
lean_inc(v_libName_408_);
lean_inc(v_globs_407_);
lean_inc(v_roots_406_);
lean_inc(v_srcDir_405_);
lean_inc(v_toLeanConfig_404_);
lean_dec(v_cfg_403_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_box(v_libPrefixOnWindows_409_);
v___x_421_ = lean_apply_1(v_f_402_, v___x_420_);
if (v_isShared_419_ == 0)
{
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_toLeanConfig_404_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_srcDir_405_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_roots_406_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_globs_407_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_libName_408_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_needs_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v_extraDepTargets_411_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_defaultFacets_414_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v_nativeFacets_415_);
v___x_423_ = v_reuseFailAlloc_425_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
uint8_t v___x_424_; 
v___x_424_ = lean_unbox(v___x_421_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*9, v___x_424_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*9 + 1, v_precompileLibrary_412_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*9 + 2, v_precompileModules_413_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*9 + 3, v_allowImportAll_416_);
return v___x_423_;
}
}
}
}
uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3(lean_object* v_x_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_427_ = stack[0].m_obj;
uint8_t v_res_429_;
v_res_429_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3(v_x_427_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3___boxed(lean_object* v_x_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3(v_x_430_);
lean_dec_ref(v_x_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg(){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = ((lean_object*)(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__4));
return v___x_443_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_444_;
v_res_444_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg();
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object* v___dummy_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg();
return v_res_446_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg();
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object* v_name_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object* v_name_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_450_);
lean_dec(v_name_450_);
return v_res_451_;
}
}
lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg(){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = lean_obj_once(&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0);
return v___x_453_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_454_;
v_res_454_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg();
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object* v___dummy_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object* v_name_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_obj_once(&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_name_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_459_);
lean_dec(v_name_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__0(lean_object* v_cfg_461_){
_start:
{
lean_object* v_needs_462_; 
v_needs_462_ = lean_ctor_get(v_cfg_461_, 5);
lean_inc_ref(v_needs_462_);
return v_needs_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__0___boxed(lean_object* v_cfg_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lake_LeanLibConfig_needs___proj___redArg___lam__0(v_cfg_463_);
lean_dec_ref(v_cfg_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__1(lean_object* v_val_465_, lean_object* v_cfg_466_){
_start:
{
lean_object* v_toLeanConfig_467_; lean_object* v_srcDir_468_; lean_object* v_roots_469_; lean_object* v_globs_470_; lean_object* v_libName_471_; uint8_t v_libPrefixOnWindows_472_; lean_object* v_extraDepTargets_473_; uint8_t v_precompileLibrary_474_; uint8_t v_precompileModules_475_; lean_object* v_defaultFacets_476_; lean_object* v_nativeFacets_477_; uint8_t v_allowImportAll_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_toLeanConfig_467_ = lean_ctor_get(v_cfg_466_, 0);
v_srcDir_468_ = lean_ctor_get(v_cfg_466_, 1);
v_roots_469_ = lean_ctor_get(v_cfg_466_, 2);
v_globs_470_ = lean_ctor_get(v_cfg_466_, 3);
v_libName_471_ = lean_ctor_get(v_cfg_466_, 4);
v_libPrefixOnWindows_472_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*9);
v_extraDepTargets_473_ = lean_ctor_get(v_cfg_466_, 6);
v_precompileLibrary_474_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*9 + 1);
v_precompileModules_475_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*9 + 2);
v_defaultFacets_476_ = lean_ctor_get(v_cfg_466_, 7);
v_nativeFacets_477_ = lean_ctor_get(v_cfg_466_, 8);
v_allowImportAll_478_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*9 + 3);
v_isSharedCheck_485_ = !lean_is_exclusive(v_cfg_466_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_cfg_466_, 5);
lean_dec(v_unused_486_);
v___x_480_ = v_cfg_466_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_nativeFacets_477_);
lean_inc(v_defaultFacets_476_);
lean_inc(v_extraDepTargets_473_);
lean_inc(v_libName_471_);
lean_inc(v_globs_470_);
lean_inc(v_roots_469_);
lean_inc(v_srcDir_468_);
lean_inc(v_toLeanConfig_467_);
lean_dec(v_cfg_466_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 5, v_val_465_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_toLeanConfig_467_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_srcDir_468_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_roots_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_globs_470_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_libName_471_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v_val_465_);
lean_ctor_set(v_reuseFailAlloc_484_, 6, v_extraDepTargets_473_);
lean_ctor_set(v_reuseFailAlloc_484_, 7, v_defaultFacets_476_);
lean_ctor_set(v_reuseFailAlloc_484_, 8, v_nativeFacets_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*9, v_libPrefixOnWindows_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*9 + 1, v_precompileLibrary_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*9 + 2, v_precompileModules_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*9 + 3, v_allowImportAll_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__2(lean_object* v_f_487_, lean_object* v_cfg_488_){
_start:
{
lean_object* v_toLeanConfig_489_; lean_object* v_srcDir_490_; lean_object* v_roots_491_; lean_object* v_globs_492_; lean_object* v_libName_493_; uint8_t v_libPrefixOnWindows_494_; lean_object* v_needs_495_; lean_object* v_extraDepTargets_496_; uint8_t v_precompileLibrary_497_; uint8_t v_precompileModules_498_; lean_object* v_defaultFacets_499_; lean_object* v_nativeFacets_500_; uint8_t v_allowImportAll_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_toLeanConfig_489_ = lean_ctor_get(v_cfg_488_, 0);
v_srcDir_490_ = lean_ctor_get(v_cfg_488_, 1);
v_roots_491_ = lean_ctor_get(v_cfg_488_, 2);
v_globs_492_ = lean_ctor_get(v_cfg_488_, 3);
v_libName_493_ = lean_ctor_get(v_cfg_488_, 4);
v_libPrefixOnWindows_494_ = lean_ctor_get_uint8(v_cfg_488_, sizeof(void*)*9);
v_needs_495_ = lean_ctor_get(v_cfg_488_, 5);
v_extraDepTargets_496_ = lean_ctor_get(v_cfg_488_, 6);
v_precompileLibrary_497_ = lean_ctor_get_uint8(v_cfg_488_, sizeof(void*)*9 + 1);
v_precompileModules_498_ = lean_ctor_get_uint8(v_cfg_488_, sizeof(void*)*9 + 2);
v_defaultFacets_499_ = lean_ctor_get(v_cfg_488_, 7);
v_nativeFacets_500_ = lean_ctor_get(v_cfg_488_, 8);
v_allowImportAll_501_ = lean_ctor_get_uint8(v_cfg_488_, sizeof(void*)*9 + 3);
v_isSharedCheck_509_ = !lean_is_exclusive(v_cfg_488_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v_cfg_488_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_nativeFacets_500_);
lean_inc(v_defaultFacets_499_);
lean_inc(v_extraDepTargets_496_);
lean_inc(v_needs_495_);
lean_inc(v_libName_493_);
lean_inc(v_globs_492_);
lean_inc(v_roots_491_);
lean_inc(v_srcDir_490_);
lean_inc(v_toLeanConfig_489_);
lean_dec(v_cfg_488_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_apply_1(v_f_487_, v_needs_495_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 5, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_toLeanConfig_489_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_srcDir_490_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_roots_491_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_globs_492_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_libName_493_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_extraDepTargets_496_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v_defaultFacets_499_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_nativeFacets_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_508_, sizeof(void*)*9, v_libPrefixOnWindows_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_508_, sizeof(void*)*9 + 1, v_precompileLibrary_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_508_, sizeof(void*)*9 + 2, v_precompileModules_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_508_, sizeof(void*)*9 + 3, v_allowImportAll_501_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__3(lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__3___boxed(lean_object* v_x_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_LeanLibConfig_needs___proj___redArg___lam__3(v_x_512_);
lean_dec_ref(v_x_512_);
return v_res_513_;
}
}
lean_object* l_Lake_LeanLibConfig_needs___proj___redArg(){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___redArg___closed__4));
return v___x_524_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_needs___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_525_;
v_res_525_ = l_Lake_LeanLibConfig_needs___proj___redArg();
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___boxed(lean_object* v___dummy_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lake_LeanLibConfig_needs___proj___redArg();
return v_res_527_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_needs___proj___closed__0(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lake_LeanLibConfig_needs___proj___redArg();
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object* v_name_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lake_LeanLibConfig_needs___proj___closed__0, &l_Lake_LeanLibConfig_needs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_needs___proj___closed__0);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object* v_name_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lake_LeanLibConfig_needs___proj(v_name_531_);
lean_dec(v_name_531_);
return v_res_532_;
}
}
lean_object* l_Lake_LeanLibConfig_needs_instConfigField___redArg(){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l_Lake_LeanLibConfig_needs___proj___closed__0, &l_Lake_LeanLibConfig_needs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_needs___proj___closed__0);
return v___x_534_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_needs_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_535_;
v_res_535_ = l_Lake_LeanLibConfig_needs_instConfigField___redArg();
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___redArg___boxed(lean_object* v___dummy_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lake_LeanLibConfig_needs_instConfigField___redArg();
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object* v_name_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lake_LeanLibConfig_needs___proj___closed__0, &l_Lake_LeanLibConfig_needs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_needs___proj___closed__0);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object* v_name_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_540_);
lean_dec(v_name_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0(lean_object* v_cfg_542_){
_start:
{
lean_object* v_extraDepTargets_543_; 
v_extraDepTargets_543_ = lean_ctor_get(v_cfg_542_, 6);
lean_inc_ref(v_extraDepTargets_543_);
return v_extraDepTargets_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object* v_cfg_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0(v_cfg_544_);
lean_dec_ref(v_cfg_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__1(lean_object* v_val_546_, lean_object* v_cfg_547_){
_start:
{
lean_object* v_toLeanConfig_548_; lean_object* v_srcDir_549_; lean_object* v_roots_550_; lean_object* v_globs_551_; lean_object* v_libName_552_; uint8_t v_libPrefixOnWindows_553_; lean_object* v_needs_554_; uint8_t v_precompileLibrary_555_; uint8_t v_precompileModules_556_; lean_object* v_defaultFacets_557_; lean_object* v_nativeFacets_558_; uint8_t v_allowImportAll_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_toLeanConfig_548_ = lean_ctor_get(v_cfg_547_, 0);
v_srcDir_549_ = lean_ctor_get(v_cfg_547_, 1);
v_roots_550_ = lean_ctor_get(v_cfg_547_, 2);
v_globs_551_ = lean_ctor_get(v_cfg_547_, 3);
v_libName_552_ = lean_ctor_get(v_cfg_547_, 4);
v_libPrefixOnWindows_553_ = lean_ctor_get_uint8(v_cfg_547_, sizeof(void*)*9);
v_needs_554_ = lean_ctor_get(v_cfg_547_, 5);
v_precompileLibrary_555_ = lean_ctor_get_uint8(v_cfg_547_, sizeof(void*)*9 + 1);
v_precompileModules_556_ = lean_ctor_get_uint8(v_cfg_547_, sizeof(void*)*9 + 2);
v_defaultFacets_557_ = lean_ctor_get(v_cfg_547_, 7);
v_nativeFacets_558_ = lean_ctor_get(v_cfg_547_, 8);
v_allowImportAll_559_ = lean_ctor_get_uint8(v_cfg_547_, sizeof(void*)*9 + 3);
v_isSharedCheck_566_ = !lean_is_exclusive(v_cfg_547_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_cfg_547_, 6);
lean_dec(v_unused_567_);
v___x_561_ = v_cfg_547_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_nativeFacets_558_);
lean_inc(v_defaultFacets_557_);
lean_inc(v_needs_554_);
lean_inc(v_libName_552_);
lean_inc(v_globs_551_);
lean_inc(v_roots_550_);
lean_inc(v_srcDir_549_);
lean_inc(v_toLeanConfig_548_);
lean_dec(v_cfg_547_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 6, v_val_546_);
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_toLeanConfig_548_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_srcDir_549_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_roots_550_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_globs_551_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_libName_552_);
lean_ctor_set(v_reuseFailAlloc_565_, 5, v_needs_554_);
lean_ctor_set(v_reuseFailAlloc_565_, 6, v_val_546_);
lean_ctor_set(v_reuseFailAlloc_565_, 7, v_defaultFacets_557_);
lean_ctor_set(v_reuseFailAlloc_565_, 8, v_nativeFacets_558_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*9, v_libPrefixOnWindows_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*9 + 1, v_precompileLibrary_555_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*9 + 2, v_precompileModules_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*9 + 3, v_allowImportAll_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__2(lean_object* v_f_568_, lean_object* v_cfg_569_){
_start:
{
lean_object* v_toLeanConfig_570_; lean_object* v_srcDir_571_; lean_object* v_roots_572_; lean_object* v_globs_573_; lean_object* v_libName_574_; uint8_t v_libPrefixOnWindows_575_; lean_object* v_needs_576_; lean_object* v_extraDepTargets_577_; uint8_t v_precompileLibrary_578_; uint8_t v_precompileModules_579_; lean_object* v_defaultFacets_580_; lean_object* v_nativeFacets_581_; uint8_t v_allowImportAll_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_toLeanConfig_570_ = lean_ctor_get(v_cfg_569_, 0);
v_srcDir_571_ = lean_ctor_get(v_cfg_569_, 1);
v_roots_572_ = lean_ctor_get(v_cfg_569_, 2);
v_globs_573_ = lean_ctor_get(v_cfg_569_, 3);
v_libName_574_ = lean_ctor_get(v_cfg_569_, 4);
v_libPrefixOnWindows_575_ = lean_ctor_get_uint8(v_cfg_569_, sizeof(void*)*9);
v_needs_576_ = lean_ctor_get(v_cfg_569_, 5);
v_extraDepTargets_577_ = lean_ctor_get(v_cfg_569_, 6);
v_precompileLibrary_578_ = lean_ctor_get_uint8(v_cfg_569_, sizeof(void*)*9 + 1);
v_precompileModules_579_ = lean_ctor_get_uint8(v_cfg_569_, sizeof(void*)*9 + 2);
v_defaultFacets_580_ = lean_ctor_get(v_cfg_569_, 7);
v_nativeFacets_581_ = lean_ctor_get(v_cfg_569_, 8);
v_allowImportAll_582_ = lean_ctor_get_uint8(v_cfg_569_, sizeof(void*)*9 + 3);
v_isSharedCheck_590_ = !lean_is_exclusive(v_cfg_569_);
if (v_isSharedCheck_590_ == 0)
{
v___x_584_ = v_cfg_569_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_nativeFacets_581_);
lean_inc(v_defaultFacets_580_);
lean_inc(v_extraDepTargets_577_);
lean_inc(v_needs_576_);
lean_inc(v_libName_574_);
lean_inc(v_globs_573_);
lean_inc(v_roots_572_);
lean_inc(v_srcDir_571_);
lean_inc(v_toLeanConfig_570_);
lean_dec(v_cfg_569_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_apply_1(v_f_568_, v_extraDepTargets_577_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 6, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_toLeanConfig_570_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_srcDir_571_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_roots_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_globs_573_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_libName_574_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_needs_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 6, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_589_, 7, v_defaultFacets_580_);
lean_ctor_set(v_reuseFailAlloc_589_, 8, v_nativeFacets_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*9, v_libPrefixOnWindows_575_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*9 + 1, v_precompileLibrary_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*9 + 2, v_precompileModules_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*9 + 3, v_allowImportAll_582_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3(lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___closed__0));
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object* v_x_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3(v_x_595_);
lean_dec_ref(v_x_595_);
return v_res_596_;
}
}
lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg(){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__4));
return v___x_607_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_extraDepTargets___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_608_;
v_res_608_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg();
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___boxed(lean_object* v___dummy_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg();
return v_res_610_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg();
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object* v_name_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0, &l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object* v_name_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_614_);
lean_dec(v_name_614_);
return v_res_615_;
}
}
lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg(){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0, &l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_618_;
v_res_618_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg();
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object* v___dummy_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg();
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object* v_name_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0, &l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object* v_name_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_623_);
lean_dec(v_name_623_);
return v_res_624_;
}
}
uint8_t l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0(lean_object* v_cfg_625_){
_start:
{
uint8_t v_precompileLibrary_626_; 
v_precompileLibrary_626_ = lean_ctor_get_uint8(v_cfg_625_, sizeof(void*)*9 + 1);
return v_precompileLibrary_626_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_625_ = stack[0].m_obj;
uint8_t v_res_627_;
v_res_627_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0(v_cfg_625_);
stack->m_num = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0___boxed(lean_object* v_cfg_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0(v_cfg_628_);
lean_dec_ref(v_cfg_628_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1(uint8_t v_val_631_, lean_object* v_cfg_632_){
_start:
{
lean_object* v_toLeanConfig_633_; lean_object* v_srcDir_634_; lean_object* v_roots_635_; lean_object* v_globs_636_; lean_object* v_libName_637_; uint8_t v_libPrefixOnWindows_638_; lean_object* v_needs_639_; lean_object* v_extraDepTargets_640_; uint8_t v_precompileModules_641_; lean_object* v_defaultFacets_642_; lean_object* v_nativeFacets_643_; uint8_t v_allowImportAll_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_toLeanConfig_633_ = lean_ctor_get(v_cfg_632_, 0);
v_srcDir_634_ = lean_ctor_get(v_cfg_632_, 1);
v_roots_635_ = lean_ctor_get(v_cfg_632_, 2);
v_globs_636_ = lean_ctor_get(v_cfg_632_, 3);
v_libName_637_ = lean_ctor_get(v_cfg_632_, 4);
v_libPrefixOnWindows_638_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*9);
v_needs_639_ = lean_ctor_get(v_cfg_632_, 5);
v_extraDepTargets_640_ = lean_ctor_get(v_cfg_632_, 6);
v_precompileModules_641_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*9 + 2);
v_defaultFacets_642_ = lean_ctor_get(v_cfg_632_, 7);
v_nativeFacets_643_ = lean_ctor_get(v_cfg_632_, 8);
v_allowImportAll_644_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*9 + 3);
v_isSharedCheck_651_ = !lean_is_exclusive(v_cfg_632_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v_cfg_632_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_nativeFacets_643_);
lean_inc(v_defaultFacets_642_);
lean_inc(v_extraDepTargets_640_);
lean_inc(v_needs_639_);
lean_inc(v_libName_637_);
lean_inc(v_globs_636_);
lean_inc(v_roots_635_);
lean_inc(v_srcDir_634_);
lean_inc(v_toLeanConfig_633_);
lean_dec(v_cfg_632_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_toLeanConfig_633_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_srcDir_634_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_roots_635_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_globs_636_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_libName_637_);
lean_ctor_set(v_reuseFailAlloc_650_, 5, v_needs_639_);
lean_ctor_set(v_reuseFailAlloc_650_, 6, v_extraDepTargets_640_);
lean_ctor_set(v_reuseFailAlloc_650_, 7, v_defaultFacets_642_);
lean_ctor_set(v_reuseFailAlloc_650_, 8, v_nativeFacets_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_650_, sizeof(void*)*9, v_libPrefixOnWindows_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_650_, sizeof(void*)*9 + 2, v_precompileModules_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_650_, sizeof(void*)*9 + 3, v_allowImportAll_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*9 + 1, v_val_631_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_631_ = stack[0].m_num;
lean_object* v_cfg_632_ = stack[1].m_obj;
lean_object* v_res_652_;
v_res_652_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1(v_val_631_, v_cfg_632_);
stack->m_obj
 = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1___boxed(lean_object* v_val_653_, lean_object* v_cfg_654_){
_start:
{
uint8_t v_val_77__boxed_655_; lean_object* v_res_656_; 
v_val_77__boxed_655_ = lean_unbox(v_val_653_);
v_res_656_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1(v_val_77__boxed_655_, v_cfg_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__2(lean_object* v_f_657_, lean_object* v_cfg_658_){
_start:
{
lean_object* v_toLeanConfig_659_; lean_object* v_srcDir_660_; lean_object* v_roots_661_; lean_object* v_globs_662_; lean_object* v_libName_663_; uint8_t v_libPrefixOnWindows_664_; lean_object* v_needs_665_; lean_object* v_extraDepTargets_666_; uint8_t v_precompileLibrary_667_; uint8_t v_precompileModules_668_; lean_object* v_defaultFacets_669_; lean_object* v_nativeFacets_670_; uint8_t v_allowImportAll_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_681_; 
v_toLeanConfig_659_ = lean_ctor_get(v_cfg_658_, 0);
v_srcDir_660_ = lean_ctor_get(v_cfg_658_, 1);
v_roots_661_ = lean_ctor_get(v_cfg_658_, 2);
v_globs_662_ = lean_ctor_get(v_cfg_658_, 3);
v_libName_663_ = lean_ctor_get(v_cfg_658_, 4);
v_libPrefixOnWindows_664_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*9);
v_needs_665_ = lean_ctor_get(v_cfg_658_, 5);
v_extraDepTargets_666_ = lean_ctor_get(v_cfg_658_, 6);
v_precompileLibrary_667_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*9 + 1);
v_precompileModules_668_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*9 + 2);
v_defaultFacets_669_ = lean_ctor_get(v_cfg_658_, 7);
v_nativeFacets_670_ = lean_ctor_get(v_cfg_658_, 8);
v_allowImportAll_671_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*9 + 3);
v_isSharedCheck_681_ = !lean_is_exclusive(v_cfg_658_);
if (v_isSharedCheck_681_ == 0)
{
v___x_673_ = v_cfg_658_;
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_nativeFacets_670_);
lean_inc(v_defaultFacets_669_);
lean_inc(v_extraDepTargets_666_);
lean_inc(v_needs_665_);
lean_inc(v_libName_663_);
lean_inc(v_globs_662_);
lean_inc(v_roots_661_);
lean_inc(v_srcDir_660_);
lean_inc(v_toLeanConfig_659_);
lean_dec(v_cfg_658_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_675_ = lean_box(v_precompileLibrary_667_);
v___x_676_ = lean_apply_1(v_f_657_, v___x_675_);
if (v_isShared_674_ == 0)
{
v___x_678_ = v___x_673_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_toLeanConfig_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_srcDir_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_roots_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_globs_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_libName_663_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v_needs_665_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_extraDepTargets_666_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_defaultFacets_669_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_nativeFacets_670_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*9, v_libPrefixOnWindows_664_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_unbox(v___x_676_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*9 + 1, v___x_679_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*9 + 2, v_precompileModules_668_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*9 + 3, v_allowImportAll_671_);
return v___x_678_;
}
}
}
}
lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg(){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__3));
return v___x_691_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileLibrary___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_692_;
v_res_692_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg();
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___boxed(lean_object* v___dummy_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg();
return v_res_694_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0(void){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg();
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj(lean_object* v_name_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0, &l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___boxed(lean_object* v_name_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lake_LeanLibConfig_precompileLibrary___proj(v_name_698_);
lean_dec(v_name_698_);
return v_res_699_;
}
}
lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg(){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0, &l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0);
return v___x_701_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_702_;
v_res_702_ = l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg();
stack->m_obj
 = v_res_702_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg___boxed(lean_object* v___dummy_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg();
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField(lean_object* v_name_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0, &l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___boxed(lean_object* v_name_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lake_LeanLibConfig_precompileLibrary_instConfigField(v_name_707_);
lean_dec(v_name_707_);
return v_res_708_;
}
}
uint8_t l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0(lean_object* v_cfg_709_){
_start:
{
uint8_t v_precompileModules_710_; 
v_precompileModules_710_ = lean_ctor_get_uint8(v_cfg_709_, sizeof(void*)*9 + 2);
return v_precompileModules_710_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_709_ = stack[0].m_obj;
uint8_t v_res_711_;
v_res_711_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0(v_cfg_709_);
stack->m_num = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object* v_cfg_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0(v_cfg_712_);
lean_dec_ref(v_cfg_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1(uint8_t v_val_715_, lean_object* v_cfg_716_){
_start:
{
lean_object* v_toLeanConfig_717_; lean_object* v_srcDir_718_; lean_object* v_roots_719_; lean_object* v_globs_720_; lean_object* v_libName_721_; uint8_t v_libPrefixOnWindows_722_; lean_object* v_needs_723_; lean_object* v_extraDepTargets_724_; uint8_t v_precompileLibrary_725_; lean_object* v_defaultFacets_726_; lean_object* v_nativeFacets_727_; uint8_t v_allowImportAll_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_toLeanConfig_717_ = lean_ctor_get(v_cfg_716_, 0);
v_srcDir_718_ = lean_ctor_get(v_cfg_716_, 1);
v_roots_719_ = lean_ctor_get(v_cfg_716_, 2);
v_globs_720_ = lean_ctor_get(v_cfg_716_, 3);
v_libName_721_ = lean_ctor_get(v_cfg_716_, 4);
v_libPrefixOnWindows_722_ = lean_ctor_get_uint8(v_cfg_716_, sizeof(void*)*9);
v_needs_723_ = lean_ctor_get(v_cfg_716_, 5);
v_extraDepTargets_724_ = lean_ctor_get(v_cfg_716_, 6);
v_precompileLibrary_725_ = lean_ctor_get_uint8(v_cfg_716_, sizeof(void*)*9 + 1);
v_defaultFacets_726_ = lean_ctor_get(v_cfg_716_, 7);
v_nativeFacets_727_ = lean_ctor_get(v_cfg_716_, 8);
v_allowImportAll_728_ = lean_ctor_get_uint8(v_cfg_716_, sizeof(void*)*9 + 3);
v_isSharedCheck_735_ = !lean_is_exclusive(v_cfg_716_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v_cfg_716_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_nativeFacets_727_);
lean_inc(v_defaultFacets_726_);
lean_inc(v_extraDepTargets_724_);
lean_inc(v_needs_723_);
lean_inc(v_libName_721_);
lean_inc(v_globs_720_);
lean_inc(v_roots_719_);
lean_inc(v_srcDir_718_);
lean_inc(v_toLeanConfig_717_);
lean_dec(v_cfg_716_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_toLeanConfig_717_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_srcDir_718_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_roots_719_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_globs_720_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_libName_721_);
lean_ctor_set(v_reuseFailAlloc_734_, 5, v_needs_723_);
lean_ctor_set(v_reuseFailAlloc_734_, 6, v_extraDepTargets_724_);
lean_ctor_set(v_reuseFailAlloc_734_, 7, v_defaultFacets_726_);
lean_ctor_set(v_reuseFailAlloc_734_, 8, v_nativeFacets_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, sizeof(void*)*9, v_libPrefixOnWindows_722_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, sizeof(void*)*9 + 1, v_precompileLibrary_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, sizeof(void*)*9 + 3, v_allowImportAll_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*9 + 2, v_val_715_);
return v___x_733_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_715_ = stack[0].m_num;
lean_object* v_cfg_716_ = stack[1].m_obj;
lean_object* v_res_736_;
v_res_736_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1(v_val_715_, v_cfg_716_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object* v_val_737_, lean_object* v_cfg_738_){
_start:
{
uint8_t v_val_77__boxed_739_; lean_object* v_res_740_; 
v_val_77__boxed_739_ = lean_unbox(v_val_737_);
v_res_740_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1(v_val_77__boxed_739_, v_cfg_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__2(lean_object* v_f_741_, lean_object* v_cfg_742_){
_start:
{
lean_object* v_toLeanConfig_743_; lean_object* v_srcDir_744_; lean_object* v_roots_745_; lean_object* v_globs_746_; lean_object* v_libName_747_; uint8_t v_libPrefixOnWindows_748_; lean_object* v_needs_749_; lean_object* v_extraDepTargets_750_; uint8_t v_precompileLibrary_751_; uint8_t v_precompileModules_752_; lean_object* v_defaultFacets_753_; lean_object* v_nativeFacets_754_; uint8_t v_allowImportAll_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_765_; 
v_toLeanConfig_743_ = lean_ctor_get(v_cfg_742_, 0);
v_srcDir_744_ = lean_ctor_get(v_cfg_742_, 1);
v_roots_745_ = lean_ctor_get(v_cfg_742_, 2);
v_globs_746_ = lean_ctor_get(v_cfg_742_, 3);
v_libName_747_ = lean_ctor_get(v_cfg_742_, 4);
v_libPrefixOnWindows_748_ = lean_ctor_get_uint8(v_cfg_742_, sizeof(void*)*9);
v_needs_749_ = lean_ctor_get(v_cfg_742_, 5);
v_extraDepTargets_750_ = lean_ctor_get(v_cfg_742_, 6);
v_precompileLibrary_751_ = lean_ctor_get_uint8(v_cfg_742_, sizeof(void*)*9 + 1);
v_precompileModules_752_ = lean_ctor_get_uint8(v_cfg_742_, sizeof(void*)*9 + 2);
v_defaultFacets_753_ = lean_ctor_get(v_cfg_742_, 7);
v_nativeFacets_754_ = lean_ctor_get(v_cfg_742_, 8);
v_allowImportAll_755_ = lean_ctor_get_uint8(v_cfg_742_, sizeof(void*)*9 + 3);
v_isSharedCheck_765_ = !lean_is_exclusive(v_cfg_742_);
if (v_isSharedCheck_765_ == 0)
{
v___x_757_ = v_cfg_742_;
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_nativeFacets_754_);
lean_inc(v_defaultFacets_753_);
lean_inc(v_extraDepTargets_750_);
lean_inc(v_needs_749_);
lean_inc(v_libName_747_);
lean_inc(v_globs_746_);
lean_inc(v_roots_745_);
lean_inc(v_srcDir_744_);
lean_inc(v_toLeanConfig_743_);
lean_dec(v_cfg_742_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_759_ = lean_box(v_precompileModules_752_);
v___x_760_ = lean_apply_1(v_f_741_, v___x_759_);
if (v_isShared_758_ == 0)
{
v___x_762_ = v___x_757_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_toLeanConfig_743_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_srcDir_744_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_roots_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_globs_746_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_libName_747_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v_needs_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_extraDepTargets_750_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_defaultFacets_753_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v_nativeFacets_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_764_, sizeof(void*)*9, v_libPrefixOnWindows_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_764_, sizeof(void*)*9 + 1, v_precompileLibrary_751_);
v___x_762_ = v_reuseFailAlloc_764_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_unbox(v___x_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*9 + 2, v___x_763_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*9 + 3, v_allowImportAll_755_);
return v___x_762_;
}
}
}
}
lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg(){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__3));
return v___x_775_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileModules___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_776_;
v_res_776_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg();
stack->m_obj
 = v_res_776_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___boxed(lean_object* v___dummy_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg();
return v_res_778_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0(void){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg();
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object* v_name_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileModules___proj___closed__0, &l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object* v_name_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_782_);
lean_dec(v_name_782_);
return v_res_783_;
}
}
lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg(){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileModules___proj___closed__0, &l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0);
return v___x_785_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_786_;
v_res_786_ = l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg();
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg___boxed(lean_object* v___dummy_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg();
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object* v_name_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileModules___proj___closed__0, &l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object* v_name_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_791_);
lean_dec(v_name_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0(lean_object* v_cfg_793_){
_start:
{
lean_object* v_defaultFacets_794_; 
v_defaultFacets_794_ = lean_ctor_get(v_cfg_793_, 7);
lean_inc_ref(v_defaultFacets_794_);
return v_defaultFacets_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0___boxed(lean_object* v_cfg_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0(v_cfg_795_);
lean_dec_ref(v_cfg_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__1(lean_object* v_val_797_, lean_object* v_cfg_798_){
_start:
{
lean_object* v_toLeanConfig_799_; lean_object* v_srcDir_800_; lean_object* v_roots_801_; lean_object* v_globs_802_; lean_object* v_libName_803_; uint8_t v_libPrefixOnWindows_804_; lean_object* v_needs_805_; lean_object* v_extraDepTargets_806_; uint8_t v_precompileLibrary_807_; uint8_t v_precompileModules_808_; lean_object* v_nativeFacets_809_; uint8_t v_allowImportAll_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_toLeanConfig_799_ = lean_ctor_get(v_cfg_798_, 0);
v_srcDir_800_ = lean_ctor_get(v_cfg_798_, 1);
v_roots_801_ = lean_ctor_get(v_cfg_798_, 2);
v_globs_802_ = lean_ctor_get(v_cfg_798_, 3);
v_libName_803_ = lean_ctor_get(v_cfg_798_, 4);
v_libPrefixOnWindows_804_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9);
v_needs_805_ = lean_ctor_get(v_cfg_798_, 5);
v_extraDepTargets_806_ = lean_ctor_get(v_cfg_798_, 6);
v_precompileLibrary_807_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9 + 1);
v_precompileModules_808_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9 + 2);
v_nativeFacets_809_ = lean_ctor_get(v_cfg_798_, 8);
v_allowImportAll_810_ = lean_ctor_get_uint8(v_cfg_798_, sizeof(void*)*9 + 3);
v_isSharedCheck_817_ = !lean_is_exclusive(v_cfg_798_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_cfg_798_, 7);
lean_dec(v_unused_818_);
v___x_812_ = v_cfg_798_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_nativeFacets_809_);
lean_inc(v_extraDepTargets_806_);
lean_inc(v_needs_805_);
lean_inc(v_libName_803_);
lean_inc(v_globs_802_);
lean_inc(v_roots_801_);
lean_inc(v_srcDir_800_);
lean_inc(v_toLeanConfig_799_);
lean_dec(v_cfg_798_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 7, v_val_797_);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_toLeanConfig_799_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_srcDir_800_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_roots_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_globs_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_libName_803_);
lean_ctor_set(v_reuseFailAlloc_816_, 5, v_needs_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 6, v_extraDepTargets_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 7, v_val_797_);
lean_ctor_set(v_reuseFailAlloc_816_, 8, v_nativeFacets_809_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*9, v_libPrefixOnWindows_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*9 + 1, v_precompileLibrary_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*9 + 2, v_precompileModules_808_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*9 + 3, v_allowImportAll_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__2(lean_object* v_f_819_, lean_object* v_cfg_820_){
_start:
{
lean_object* v_toLeanConfig_821_; lean_object* v_srcDir_822_; lean_object* v_roots_823_; lean_object* v_globs_824_; lean_object* v_libName_825_; uint8_t v_libPrefixOnWindows_826_; lean_object* v_needs_827_; lean_object* v_extraDepTargets_828_; uint8_t v_precompileLibrary_829_; uint8_t v_precompileModules_830_; lean_object* v_defaultFacets_831_; lean_object* v_nativeFacets_832_; uint8_t v_allowImportAll_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_toLeanConfig_821_ = lean_ctor_get(v_cfg_820_, 0);
v_srcDir_822_ = lean_ctor_get(v_cfg_820_, 1);
v_roots_823_ = lean_ctor_get(v_cfg_820_, 2);
v_globs_824_ = lean_ctor_get(v_cfg_820_, 3);
v_libName_825_ = lean_ctor_get(v_cfg_820_, 4);
v_libPrefixOnWindows_826_ = lean_ctor_get_uint8(v_cfg_820_, sizeof(void*)*9);
v_needs_827_ = lean_ctor_get(v_cfg_820_, 5);
v_extraDepTargets_828_ = lean_ctor_get(v_cfg_820_, 6);
v_precompileLibrary_829_ = lean_ctor_get_uint8(v_cfg_820_, sizeof(void*)*9 + 1);
v_precompileModules_830_ = lean_ctor_get_uint8(v_cfg_820_, sizeof(void*)*9 + 2);
v_defaultFacets_831_ = lean_ctor_get(v_cfg_820_, 7);
v_nativeFacets_832_ = lean_ctor_get(v_cfg_820_, 8);
v_allowImportAll_833_ = lean_ctor_get_uint8(v_cfg_820_, sizeof(void*)*9 + 3);
v_isSharedCheck_841_ = !lean_is_exclusive(v_cfg_820_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v_cfg_820_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_nativeFacets_832_);
lean_inc(v_defaultFacets_831_);
lean_inc(v_extraDepTargets_828_);
lean_inc(v_needs_827_);
lean_inc(v_libName_825_);
lean_inc(v_globs_824_);
lean_inc(v_roots_823_);
lean_inc(v_srcDir_822_);
lean_inc(v_toLeanConfig_821_);
lean_dec(v_cfg_820_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_apply_1(v_f_819_, v_defaultFacets_831_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 7, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_toLeanConfig_821_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_srcDir_822_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_roots_823_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_globs_824_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_libName_825_);
lean_ctor_set(v_reuseFailAlloc_840_, 5, v_needs_827_);
lean_ctor_set(v_reuseFailAlloc_840_, 6, v_extraDepTargets_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 7, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_840_, 8, v_nativeFacets_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*9, v_libPrefixOnWindows_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*9 + 1, v_precompileLibrary_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*9 + 2, v_precompileModules_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*9 + 3, v_allowImportAll_833_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3(lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_mk_empty_array_with_capacity(v___x_843_);
lean_dec_ref(v___x_844_);
v___x_845_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3___boxed(lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3(v_x_846_);
lean_dec_ref(v_x_846_);
return v_res_847_;
}
}
lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg(){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = ((lean_object*)(l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__4));
return v___x_858_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_defaultFacets___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_859_;
v_res_859_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg();
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___boxed(lean_object* v___dummy_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg();
return v_res_861_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0(void){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg();
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object* v_name_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object* v_name_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_865_);
lean_dec(v_name_865_);
return v_res_866_;
}
}
lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg(){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0);
return v___x_868_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_869_;
v_res_869_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg();
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg___boxed(lean_object* v___dummy_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg();
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object* v_name_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object* v_name_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_874_);
lean_dec(v_name_874_);
return v_res_875_;
}
}
lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0(lean_object* v_cfg_876_, uint8_t v___y_877_){
_start:
{
lean_object* v_nativeFacets_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_nativeFacets_878_ = lean_ctor_get(v_cfg_876_, 8);
lean_inc_ref(v_nativeFacets_878_);
lean_dec_ref(v_cfg_876_);
v___x_879_ = lean_box(v___y_877_);
v___x_880_ = lean_apply_1(v_nativeFacets_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_876_ = stack[0].m_obj;
uint8_t v___y_877_ = stack[1].m_num;
lean_object* v_res_881_;
v_res_881_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0(v_cfg_876_, v___y_877_);
stack->m_obj
 = v_res_881_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0___boxed(lean_object* v_cfg_882_, lean_object* v___y_883_){
_start:
{
uint8_t v___y_130__boxed_884_; lean_object* v_res_885_; 
v___y_130__boxed_884_ = lean_unbox(v___y_883_);
v_res_885_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0(v_cfg_882_, v___y_130__boxed_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__1(lean_object* v_val_886_, lean_object* v_cfg_887_){
_start:
{
lean_object* v_toLeanConfig_888_; lean_object* v_srcDir_889_; lean_object* v_roots_890_; lean_object* v_globs_891_; lean_object* v_libName_892_; uint8_t v_libPrefixOnWindows_893_; lean_object* v_needs_894_; lean_object* v_extraDepTargets_895_; uint8_t v_precompileLibrary_896_; uint8_t v_precompileModules_897_; lean_object* v_defaultFacets_898_; uint8_t v_allowImportAll_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_toLeanConfig_888_ = lean_ctor_get(v_cfg_887_, 0);
v_srcDir_889_ = lean_ctor_get(v_cfg_887_, 1);
v_roots_890_ = lean_ctor_get(v_cfg_887_, 2);
v_globs_891_ = lean_ctor_get(v_cfg_887_, 3);
v_libName_892_ = lean_ctor_get(v_cfg_887_, 4);
v_libPrefixOnWindows_893_ = lean_ctor_get_uint8(v_cfg_887_, sizeof(void*)*9);
v_needs_894_ = lean_ctor_get(v_cfg_887_, 5);
v_extraDepTargets_895_ = lean_ctor_get(v_cfg_887_, 6);
v_precompileLibrary_896_ = lean_ctor_get_uint8(v_cfg_887_, sizeof(void*)*9 + 1);
v_precompileModules_897_ = lean_ctor_get_uint8(v_cfg_887_, sizeof(void*)*9 + 2);
v_defaultFacets_898_ = lean_ctor_get(v_cfg_887_, 7);
v_allowImportAll_899_ = lean_ctor_get_uint8(v_cfg_887_, sizeof(void*)*9 + 3);
v_isSharedCheck_906_ = !lean_is_exclusive(v_cfg_887_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_cfg_887_, 8);
lean_dec(v_unused_907_);
v___x_901_ = v_cfg_887_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_defaultFacets_898_);
lean_inc(v_extraDepTargets_895_);
lean_inc(v_needs_894_);
lean_inc(v_libName_892_);
lean_inc(v_globs_891_);
lean_inc(v_roots_890_);
lean_inc(v_srcDir_889_);
lean_inc(v_toLeanConfig_888_);
lean_dec(v_cfg_887_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 8, v_val_886_);
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_toLeanConfig_888_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_srcDir_889_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_roots_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_globs_891_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_libName_892_);
lean_ctor_set(v_reuseFailAlloc_905_, 5, v_needs_894_);
lean_ctor_set(v_reuseFailAlloc_905_, 6, v_extraDepTargets_895_);
lean_ctor_set(v_reuseFailAlloc_905_, 7, v_defaultFacets_898_);
lean_ctor_set(v_reuseFailAlloc_905_, 8, v_val_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9, v_libPrefixOnWindows_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9 + 1, v_precompileLibrary_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9 + 2, v_precompileModules_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*9 + 3, v_allowImportAll_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__2(lean_object* v_f_908_, lean_object* v_cfg_909_){
_start:
{
lean_object* v_toLeanConfig_910_; lean_object* v_srcDir_911_; lean_object* v_roots_912_; lean_object* v_globs_913_; lean_object* v_libName_914_; uint8_t v_libPrefixOnWindows_915_; lean_object* v_needs_916_; lean_object* v_extraDepTargets_917_; uint8_t v_precompileLibrary_918_; uint8_t v_precompileModules_919_; lean_object* v_defaultFacets_920_; lean_object* v_nativeFacets_921_; uint8_t v_allowImportAll_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_toLeanConfig_910_ = lean_ctor_get(v_cfg_909_, 0);
v_srcDir_911_ = lean_ctor_get(v_cfg_909_, 1);
v_roots_912_ = lean_ctor_get(v_cfg_909_, 2);
v_globs_913_ = lean_ctor_get(v_cfg_909_, 3);
v_libName_914_ = lean_ctor_get(v_cfg_909_, 4);
v_libPrefixOnWindows_915_ = lean_ctor_get_uint8(v_cfg_909_, sizeof(void*)*9);
v_needs_916_ = lean_ctor_get(v_cfg_909_, 5);
v_extraDepTargets_917_ = lean_ctor_get(v_cfg_909_, 6);
v_precompileLibrary_918_ = lean_ctor_get_uint8(v_cfg_909_, sizeof(void*)*9 + 1);
v_precompileModules_919_ = lean_ctor_get_uint8(v_cfg_909_, sizeof(void*)*9 + 2);
v_defaultFacets_920_ = lean_ctor_get(v_cfg_909_, 7);
v_nativeFacets_921_ = lean_ctor_get(v_cfg_909_, 8);
v_allowImportAll_922_ = lean_ctor_get_uint8(v_cfg_909_, sizeof(void*)*9 + 3);
v_isSharedCheck_930_ = !lean_is_exclusive(v_cfg_909_);
if (v_isSharedCheck_930_ == 0)
{
v___x_924_ = v_cfg_909_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_nativeFacets_921_);
lean_inc(v_defaultFacets_920_);
lean_inc(v_extraDepTargets_917_);
lean_inc(v_needs_916_);
lean_inc(v_libName_914_);
lean_inc(v_globs_913_);
lean_inc(v_roots_912_);
lean_inc(v_srcDir_911_);
lean_inc(v_toLeanConfig_910_);
lean_dec(v_cfg_909_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_apply_1(v_f_908_, v_nativeFacets_921_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 8, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_toLeanConfig_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_srcDir_911_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_roots_912_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_globs_913_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_libName_914_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_needs_916_);
lean_ctor_set(v_reuseFailAlloc_929_, 6, v_extraDepTargets_917_);
lean_ctor_set(v_reuseFailAlloc_929_, 7, v_defaultFacets_920_);
lean_ctor_set(v_reuseFailAlloc_929_, 8, v___x_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*9, v_libPrefixOnWindows_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*9 + 1, v_precompileLibrary_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*9 + 2, v_precompileModules_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*9 + 3, v_allowImportAll_922_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3(lean_object* v_x_931_, uint8_t v___y_932_){
_start:
{
lean_object* v___y_934_; 
if (v___y_932_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = l_Lake_Module_oFacet;
v___y_934_ = v___x_938_;
goto v___jp_933_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = l_Lake_Module_oExportFacet;
v___y_934_ = v___x_939_;
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
lean_inc(v___y_934_);
v___x_937_ = lean_array_push(v___x_936_, v___y_934_);
return v___x_937_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_931_ = stack[0].m_obj;
uint8_t v___y_932_ = stack[1].m_num;
lean_object* v_res_940_;
v_res_940_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3(v_x_931_, v___y_932_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3___boxed(lean_object* v_x_941_, lean_object* v___y_942_){
_start:
{
uint8_t v___y_206__boxed_943_; lean_object* v_res_944_; 
v___y_206__boxed_943_ = lean_unbox(v___y_942_);
v_res_944_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3(v_x_941_, v___y_206__boxed_943_);
lean_dec_ref(v_x_941_);
return v_res_944_;
}
}
lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg(){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__4));
return v___x_955_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_nativeFacets___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_956_;
v_res_956_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg();
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___boxed(lean_object* v___dummy_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg();
return v_res_958_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg();
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object* v_name_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_obj_once(&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0, &l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object* v_name_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_962_);
lean_dec(v_name_962_);
return v_res_963_;
}
}
lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg(){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_obj_once(&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0, &l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0);
return v___x_965_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_966_;
v_res_966_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg();
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg___boxed(lean_object* v___dummy_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg();
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object* v_name_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0, &l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object* v_name_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_971_);
lean_dec(v_name_971_);
return v_res_972_;
}
}
uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0(lean_object* v_cfg_973_){
_start:
{
uint8_t v_allowImportAll_974_; 
v_allowImportAll_974_ = lean_ctor_get_uint8(v_cfg_973_, sizeof(void*)*9 + 3);
return v_allowImportAll_974_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_973_ = stack[0].m_obj;
uint8_t v_res_975_;
v_res_975_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0(v_cfg_973_);
stack->m_num = v_res_975_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object* v_cfg_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0(v_cfg_976_);
lean_dec_ref(v_cfg_976_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1(uint8_t v_val_979_, lean_object* v_cfg_980_){
_start:
{
lean_object* v_toLeanConfig_981_; lean_object* v_srcDir_982_; lean_object* v_roots_983_; lean_object* v_globs_984_; lean_object* v_libName_985_; uint8_t v_libPrefixOnWindows_986_; lean_object* v_needs_987_; lean_object* v_extraDepTargets_988_; uint8_t v_precompileLibrary_989_; uint8_t v_precompileModules_990_; lean_object* v_defaultFacets_991_; lean_object* v_nativeFacets_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_toLeanConfig_981_ = lean_ctor_get(v_cfg_980_, 0);
v_srcDir_982_ = lean_ctor_get(v_cfg_980_, 1);
v_roots_983_ = lean_ctor_get(v_cfg_980_, 2);
v_globs_984_ = lean_ctor_get(v_cfg_980_, 3);
v_libName_985_ = lean_ctor_get(v_cfg_980_, 4);
v_libPrefixOnWindows_986_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*9);
v_needs_987_ = lean_ctor_get(v_cfg_980_, 5);
v_extraDepTargets_988_ = lean_ctor_get(v_cfg_980_, 6);
v_precompileLibrary_989_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*9 + 1);
v_precompileModules_990_ = lean_ctor_get_uint8(v_cfg_980_, sizeof(void*)*9 + 2);
v_defaultFacets_991_ = lean_ctor_get(v_cfg_980_, 7);
v_nativeFacets_992_ = lean_ctor_get(v_cfg_980_, 8);
v_isSharedCheck_999_ = !lean_is_exclusive(v_cfg_980_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v_cfg_980_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_nativeFacets_992_);
lean_inc(v_defaultFacets_991_);
lean_inc(v_extraDepTargets_988_);
lean_inc(v_needs_987_);
lean_inc(v_libName_985_);
lean_inc(v_globs_984_);
lean_inc(v_roots_983_);
lean_inc(v_srcDir_982_);
lean_inc(v_toLeanConfig_981_);
lean_dec(v_cfg_980_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_toLeanConfig_981_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_srcDir_982_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_roots_983_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_globs_984_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_libName_985_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_needs_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 6, v_extraDepTargets_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 7, v_defaultFacets_991_);
lean_ctor_set(v_reuseFailAlloc_998_, 8, v_nativeFacets_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*9, v_libPrefixOnWindows_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*9 + 1, v_precompileLibrary_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*9 + 2, v_precompileModules_990_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*9 + 3, v_val_979_);
return v___x_997_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_979_ = stack[0].m_num;
lean_object* v_cfg_980_ = stack[1].m_obj;
lean_object* v_res_1000_;
v_res_1000_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1(v_val_979_, v_cfg_980_);
stack->m_obj
 = v_res_1000_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object* v_val_1001_, lean_object* v_cfg_1002_){
_start:
{
uint8_t v_val_77__boxed_1003_; lean_object* v_res_1004_; 
v_val_77__boxed_1003_ = lean_unbox(v_val_1001_);
v_res_1004_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1(v_val_77__boxed_1003_, v_cfg_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__2(lean_object* v_f_1005_, lean_object* v_cfg_1006_){
_start:
{
lean_object* v_toLeanConfig_1007_; lean_object* v_srcDir_1008_; lean_object* v_roots_1009_; lean_object* v_globs_1010_; lean_object* v_libName_1011_; uint8_t v_libPrefixOnWindows_1012_; lean_object* v_needs_1013_; lean_object* v_extraDepTargets_1014_; uint8_t v_precompileLibrary_1015_; uint8_t v_precompileModules_1016_; lean_object* v_defaultFacets_1017_; lean_object* v_nativeFacets_1018_; uint8_t v_allowImportAll_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_toLeanConfig_1007_ = lean_ctor_get(v_cfg_1006_, 0);
v_srcDir_1008_ = lean_ctor_get(v_cfg_1006_, 1);
v_roots_1009_ = lean_ctor_get(v_cfg_1006_, 2);
v_globs_1010_ = lean_ctor_get(v_cfg_1006_, 3);
v_libName_1011_ = lean_ctor_get(v_cfg_1006_, 4);
v_libPrefixOnWindows_1012_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*9);
v_needs_1013_ = lean_ctor_get(v_cfg_1006_, 5);
v_extraDepTargets_1014_ = lean_ctor_get(v_cfg_1006_, 6);
v_precompileLibrary_1015_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*9 + 1);
v_precompileModules_1016_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*9 + 2);
v_defaultFacets_1017_ = lean_ctor_get(v_cfg_1006_, 7);
v_nativeFacets_1018_ = lean_ctor_get(v_cfg_1006_, 8);
v_allowImportAll_1019_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*9 + 3);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_cfg_1006_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v_cfg_1006_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_nativeFacets_1018_);
lean_inc(v_defaultFacets_1017_);
lean_inc(v_extraDepTargets_1014_);
lean_inc(v_needs_1013_);
lean_inc(v_libName_1011_);
lean_inc(v_globs_1010_);
lean_inc(v_roots_1009_);
lean_inc(v_srcDir_1008_);
lean_inc(v_toLeanConfig_1007_);
lean_dec(v_cfg_1006_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1023_ = lean_box(v_allowImportAll_1019_);
v___x_1024_ = lean_apply_1(v_f_1005_, v___x_1023_);
if (v_isShared_1022_ == 0)
{
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_toLeanConfig_1007_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_srcDir_1008_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_roots_1009_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_globs_1010_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_libName_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 5, v_needs_1013_);
lean_ctor_set(v_reuseFailAlloc_1028_, 6, v_extraDepTargets_1014_);
lean_ctor_set(v_reuseFailAlloc_1028_, 7, v_defaultFacets_1017_);
lean_ctor_set(v_reuseFailAlloc_1028_, 8, v_nativeFacets_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*9, v_libPrefixOnWindows_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*9 + 1, v_precompileLibrary_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*9 + 2, v_precompileModules_1016_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_unbox(v___x_1024_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*9 + 3, v___x_1027_);
return v___x_1026_;
}
}
}
}
lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg(){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__3));
return v___x_1039_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_allowImportAll___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1040_;
v_res_1040_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg();
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___boxed(lean_object* v___dummy_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg();
return v_res_1042_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0(void){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg();
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object* v_name_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_obj_once(&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0, &l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object* v_name_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_1046_);
lean_dec(v_name_1046_);
return v_res_1047_;
}
}
lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg(){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0, &l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0);
return v___x_1049_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1050_;
v_res_1050_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg();
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg___boxed(lean_object* v___dummy_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg();
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object* v_name_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_obj_once(&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0, &l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object* v_name_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_1055_);
lean_dec(v_name_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0(lean_object* v_cfg_1057_){
_start:
{
lean_object* v_toLeanConfig_1058_; 
v_toLeanConfig_1058_ = lean_ctor_get(v_cfg_1057_, 0);
lean_inc_ref(v_toLeanConfig_1058_);
return v_toLeanConfig_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0(v_cfg_1059_);
lean_dec_ref(v_cfg_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__1(lean_object* v_val_1061_, lean_object* v_cfg_1062_){
_start:
{
lean_object* v_srcDir_1063_; lean_object* v_roots_1064_; lean_object* v_globs_1065_; lean_object* v_libName_1066_; uint8_t v_libPrefixOnWindows_1067_; lean_object* v_needs_1068_; lean_object* v_extraDepTargets_1069_; uint8_t v_precompileLibrary_1070_; uint8_t v_precompileModules_1071_; lean_object* v_defaultFacets_1072_; lean_object* v_nativeFacets_1073_; uint8_t v_allowImportAll_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_srcDir_1063_ = lean_ctor_get(v_cfg_1062_, 1);
v_roots_1064_ = lean_ctor_get(v_cfg_1062_, 2);
v_globs_1065_ = lean_ctor_get(v_cfg_1062_, 3);
v_libName_1066_ = lean_ctor_get(v_cfg_1062_, 4);
v_libPrefixOnWindows_1067_ = lean_ctor_get_uint8(v_cfg_1062_, sizeof(void*)*9);
v_needs_1068_ = lean_ctor_get(v_cfg_1062_, 5);
v_extraDepTargets_1069_ = lean_ctor_get(v_cfg_1062_, 6);
v_precompileLibrary_1070_ = lean_ctor_get_uint8(v_cfg_1062_, sizeof(void*)*9 + 1);
v_precompileModules_1071_ = lean_ctor_get_uint8(v_cfg_1062_, sizeof(void*)*9 + 2);
v_defaultFacets_1072_ = lean_ctor_get(v_cfg_1062_, 7);
v_nativeFacets_1073_ = lean_ctor_get(v_cfg_1062_, 8);
v_allowImportAll_1074_ = lean_ctor_get_uint8(v_cfg_1062_, sizeof(void*)*9 + 3);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_cfg_1062_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_cfg_1062_, 0);
lean_dec(v_unused_1082_);
v___x_1076_ = v_cfg_1062_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_nativeFacets_1073_);
lean_inc(v_defaultFacets_1072_);
lean_inc(v_extraDepTargets_1069_);
lean_inc(v_needs_1068_);
lean_inc(v_libName_1066_);
lean_inc(v_globs_1065_);
lean_inc(v_roots_1064_);
lean_inc(v_srcDir_1063_);
lean_dec(v_cfg_1062_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_val_1061_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_val_1061_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_srcDir_1063_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_roots_1064_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_globs_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_libName_1066_);
lean_ctor_set(v_reuseFailAlloc_1080_, 5, v_needs_1068_);
lean_ctor_set(v_reuseFailAlloc_1080_, 6, v_extraDepTargets_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 7, v_defaultFacets_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 8, v_nativeFacets_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*9, v_libPrefixOnWindows_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*9 + 1, v_precompileLibrary_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*9 + 2, v_precompileModules_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*9 + 3, v_allowImportAll_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__2(lean_object* v_f_1083_, lean_object* v_cfg_1084_){
_start:
{
lean_object* v_toLeanConfig_1085_; lean_object* v_srcDir_1086_; lean_object* v_roots_1087_; lean_object* v_globs_1088_; lean_object* v_libName_1089_; uint8_t v_libPrefixOnWindows_1090_; lean_object* v_needs_1091_; lean_object* v_extraDepTargets_1092_; uint8_t v_precompileLibrary_1093_; uint8_t v_precompileModules_1094_; lean_object* v_defaultFacets_1095_; lean_object* v_nativeFacets_1096_; uint8_t v_allowImportAll_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1105_; 
v_toLeanConfig_1085_ = lean_ctor_get(v_cfg_1084_, 0);
v_srcDir_1086_ = lean_ctor_get(v_cfg_1084_, 1);
v_roots_1087_ = lean_ctor_get(v_cfg_1084_, 2);
v_globs_1088_ = lean_ctor_get(v_cfg_1084_, 3);
v_libName_1089_ = lean_ctor_get(v_cfg_1084_, 4);
v_libPrefixOnWindows_1090_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*9);
v_needs_1091_ = lean_ctor_get(v_cfg_1084_, 5);
v_extraDepTargets_1092_ = lean_ctor_get(v_cfg_1084_, 6);
v_precompileLibrary_1093_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*9 + 1);
v_precompileModules_1094_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*9 + 2);
v_defaultFacets_1095_ = lean_ctor_get(v_cfg_1084_, 7);
v_nativeFacets_1096_ = lean_ctor_get(v_cfg_1084_, 8);
v_allowImportAll_1097_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*9 + 3);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_cfg_1084_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1099_ = v_cfg_1084_;
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_nativeFacets_1096_);
lean_inc(v_defaultFacets_1095_);
lean_inc(v_extraDepTargets_1092_);
lean_inc(v_needs_1091_);
lean_inc(v_libName_1089_);
lean_inc(v_globs_1088_);
lean_inc(v_roots_1087_);
lean_inc(v_srcDir_1086_);
lean_inc(v_toLeanConfig_1085_);
lean_dec(v_cfg_1084_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = lean_apply_1(v_f_1083_, v_toLeanConfig_1085_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_srcDir_1086_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_roots_1087_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_globs_1088_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_libName_1089_);
lean_ctor_set(v_reuseFailAlloc_1104_, 5, v_needs_1091_);
lean_ctor_set(v_reuseFailAlloc_1104_, 6, v_extraDepTargets_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 7, v_defaultFacets_1095_);
lean_ctor_set(v_reuseFailAlloc_1104_, 8, v_nativeFacets_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*9, v_libPrefixOnWindows_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*9 + 1, v_precompileLibrary_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*9 + 2, v_precompileModules_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*9 + 3, v_allowImportAll_1097_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3(lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3(v_x_1116_);
lean_dec_ref(v_x_1116_);
return v_res_1117_;
}
}
lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg(){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__4));
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_toLeanConfig___proj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1129_;
v_res_1129_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg();
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___boxed(lean_object* v___dummy_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg();
return v_res_1131_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg();
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object* v_name_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0, &l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object* v_name_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_1135_);
lean_dec(v_name_1135_);
return v_res_1136_;
}
}
lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0, &l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0);
return v___x_1138_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1139_;
v_res_1139_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg();
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg();
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(lean_object* v_name_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_obj_once(&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0, &l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_name_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(v_name_1144_);
lean_dec(v_name_1144_);
return v_res_1145_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__3));
v___x_1156_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__0));
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__7));
v___x_1166_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__4, &l_Lake_LeanLibConfig___fields___closed__4_once, _init_l_Lake_LeanLibConfig___fields___closed__4);
v___x_1167_ = lean_array_push(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__11));
v___x_1176_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__8, &l_Lake_LeanLibConfig___fields___closed__8_once, _init_l_Lake_LeanLibConfig___fields___closed__8);
v___x_1177_ = lean_array_push(v___x_1176_, v___x_1175_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__15));
v___x_1186_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__12, &l_Lake_LeanLibConfig___fields___closed__12_once, _init_l_Lake_LeanLibConfig___fields___closed__12);
v___x_1187_ = lean_array_push(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__19));
v___x_1196_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__16, &l_Lake_LeanLibConfig___fields___closed__16_once, _init_l_Lake_LeanLibConfig___fields___closed__16);
v___x_1197_ = lean_array_push(v___x_1196_, v___x_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__23));
v___x_1206_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__20, &l_Lake_LeanLibConfig___fields___closed__20_once, _init_l_Lake_LeanLibConfig___fields___closed__20);
v___x_1207_ = lean_array_push(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__27));
v___x_1216_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__24, &l_Lake_LeanLibConfig___fields___closed__24_once, _init_l_Lake_LeanLibConfig___fields___closed__24);
v___x_1217_ = lean_array_push(v___x_1216_, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__31));
v___x_1226_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__28, &l_Lake_LeanLibConfig___fields___closed__28_once, _init_l_Lake_LeanLibConfig___fields___closed__28);
v___x_1227_ = lean_array_push(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__35));
v___x_1236_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__32, &l_Lake_LeanLibConfig___fields___closed__32_once, _init_l_Lake_LeanLibConfig___fields___closed__32);
v___x_1237_ = lean_array_push(v___x_1236_, v___x_1235_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__39));
v___x_1246_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__36, &l_Lake_LeanLibConfig___fields___closed__36_once, _init_l_Lake_LeanLibConfig___fields___closed__36);
v___x_1247_ = lean_array_push(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__43));
v___x_1256_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__40, &l_Lake_LeanLibConfig___fields___closed__40_once, _init_l_Lake_LeanLibConfig___fields___closed__40);
v___x_1257_ = lean_array_push(v___x_1256_, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__47));
v___x_1266_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__44, &l_Lake_LeanLibConfig___fields___closed__44_once, _init_l_Lake_LeanLibConfig___fields___closed__44);
v___x_1267_ = lean_array_push(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__49(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = l_Lake_LeanConfig___fields;
v___x_1269_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__48, &l_Lake_LeanLibConfig___fields___closed__48_once, _init_l_Lake_LeanLibConfig___fields___closed__48);
v___x_1270_ = l_Array_append___redArg(v___x_1269_, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__53(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__52));
v___x_1279_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__49, &l_Lake_LeanLibConfig___fields___closed__49_once, _init_l_Lake_LeanLibConfig___fields___closed__49);
v___x_1280_ = lean_array_push(v___x_1279_, v___x_1278_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields(void){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__53, &l_Lake_LeanLibConfig___fields___closed__53_once, _init_l_Lake_LeanLibConfig___fields___closed__53);
return v___x_1281_;
}
}
lean_object* l_Lake_LeanLibConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lake_LeanLibConfig___fields;
return v___x_1283_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_instConfigFields___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1284_;
v_res_1284_ = l_Lake_LeanLibConfig_instConfigFields___redArg();
stack->m_obj
 = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lake_LeanLibConfig_instConfigFields___redArg();
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields(lean_object* v_name_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lake_LeanLibConfig___fields;
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___boxed(lean_object* v_name_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lake_LeanLibConfig_instConfigFields(v_name_1289_);
lean_dec(v_name_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo___lam__0(lean_object* v_x1_1291_, lean_object* v_x2_1292_){
_start:
{
lean_object* v_name_1293_; lean_object* v___x_1294_; 
v_name_1293_ = lean_ctor_get(v_x2_1292_, 0);
lean_inc(v_name_1293_);
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1293_, v_x2_1292_, v_x1_1291_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = l_Lake_LeanLibConfig___fields;
v___x_1296_ = lean_array_get_size(v___x_1295_);
return v___x_1296_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_nat_dec_lt(v___x_1317_, v___x_1316_);
return v___x_1318_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1321_ = lean_nat_dec_le(v___x_1320_, v___x_1320_);
return v___x_1321_;
}
}
static size_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_1322_; size_t v___x_1323_; 
v___x_1322_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1323_ = lean_usize_of_nat(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1324_ = lean_box(1);
v___x_1325_ = lean_usize_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__14, &l_Lake_LeanLibConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14);
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = l_Lake_LeanLibConfig___fields;
v___f_1328_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__12));
v___x_1329_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1329_, v___f_1328_, v___x_1327_, v___x_1326_, v___x_1325_, v___x_1324_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___y_1333_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1331_ = l_Lake_LeanLibConfig___fields;
v___x_1336_ = lean_box(1);
v___x_1337_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__11, &l_Lake_LeanLibConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11);
if (v___x_1337_ == 0)
{
v___y_1333_ = v___x_1336_;
goto v___jp_1332_;
}
else
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__13, &l_Lake_LeanLibConfig_instConfigInfo___closed__13_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13);
if (v___x_1338_ == 0)
{
if (v___x_1337_ == 0)
{
v___y_1333_ = v___x_1336_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1333_ = v___x_1339_;
goto v___jp_1332_;
}
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1333_ = v___x_1340_;
goto v___jp_1332_;
}
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_1333_);
v___x_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1331_);
lean_ctor_set(v___x_1335_, 1, v___y_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__0(lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection(lean_object* v_name_1344_){
_start:
{
lean_object* v___f_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___f_1345_ = ((lean_object*)(l_Lake_LeanLibConfig_instEmptyCollection___closed__0));
v___f_1346_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_1347_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0));
v___x_1348_ = 0;
v___x_1349_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
v___x_1350_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_mk_empty_array_with_capacity(v___x_1351_);
v___x_1353_ = lean_array_push(v___x_1352_, v_name_1344_);
v___x_1354_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v_sz_1355_ = lean_array_size(v___x_1353_);
v___x_1356_ = ((size_t)0ULL);
lean_inc_ref(v___x_1353_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1354_, v___f_1345_, v_sz_1355_, v___x_1356_, v___x_1353_);
v___x_1358_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_1359_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
v___x_1360_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v___x_1360_, 0, v___x_1349_);
lean_ctor_set(v___x_1360_, 1, v___x_1350_);
lean_ctor_set(v___x_1360_, 2, v___x_1353_);
lean_ctor_set(v___x_1360_, 3, v___x_1357_);
lean_ctor_set(v___x_1360_, 4, v___x_1358_);
lean_ctor_set(v___x_1360_, 5, v___x_1347_);
lean_ctor_set(v___x_1360_, 6, v___x_1347_);
lean_ctor_set(v___x_1360_, 7, v___x_1359_);
lean_ctor_set(v___x_1360_, 8, v___f_1346_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*9, v___x_1348_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*9 + 1, v___x_1348_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*9 + 2, v___x_1348_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*9 + 3, v___x_1348_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg(lean_object* v_n_1361_){
_start:
{
lean_inc(v_n_1361_);
return v_n_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg___boxed(lean_object* v_n_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lake_LeanLibConfig_name___redArg(v_n_1362_);
lean_dec(v_n_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name(lean_object* v_n_1364_, lean_object* v_x_1365_){
_start:
{
lean_inc(v_n_1364_);
return v_n_1364_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___boxed(lean_object* v_n_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lake_LeanLibConfig_name(v_n_1366_, v_x_1367_);
lean_dec_ref(v_x_1367_);
lean_dec(v_n_1366_);
return v_res_1368_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(lean_object* v_mod_1369_, lean_object* v_as_1370_, size_t v_i_1371_, size_t v_stop_1372_){
_start:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_usize_dec_eq(v_i_1371_, v_stop_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_array_uget_borrowed(v_as_1370_, v_i_1371_);
v___x_1375_ = l_Lake_Glob_matches(v_mod_1369_, v___x_1374_);
if (v___x_1375_ == 0)
{
size_t v___x_1376_; size_t v___x_1377_; 
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1371_, v___x_1376_);
v_i_1371_ = v___x_1377_;
goto _start;
}
else
{
return v___x_1375_;
}
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = 0;
return v___x_1379_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1369_ = stack[0].m_obj;
lean_object* v_as_1370_ = stack[1].m_obj;
size_t v_i_1371_ = stack[2].m_num;
size_t v_stop_1372_ = stack[3].m_num;
uint8_t v_res_1380_;
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1369_, v_as_1370_, v_i_1371_, v_stop_1372_);
stack->m_num = v_res_1380_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(lean_object* v_mod_1381_, lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_stop_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1384_);
lean_dec(v_stop_1384_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1381_, v_as_1382_, v_i_boxed_1385_, v_stop_boxed_1386_);
lean_dec_ref(v_as_1382_);
lean_dec(v_mod_1381_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(lean_object* v_mod_1389_, lean_object* v_as_1390_, size_t v_i_1391_, size_t v_stop_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_eq(v_i_1391_, v_stop_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_array_uget_borrowed(v_as_1390_, v_i_1391_);
v___x_1395_ = l_Lean_Name_isPrefixOf(v___x_1394_, v_mod_1389_);
if (v___x_1395_ == 0)
{
size_t v___x_1396_; size_t v___x_1397_; 
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_add(v_i_1391_, v___x_1396_);
v_i_1391_ = v___x_1397_;
goto _start;
}
else
{
return v___x_1395_;
}
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = 0;
return v___x_1399_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1389_ = stack[0].m_obj;
lean_object* v_as_1390_ = stack[1].m_obj;
size_t v_i_1391_ = stack[2].m_num;
size_t v_stop_1392_ = stack[3].m_num;
uint8_t v_res_1400_;
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1389_, v_as_1390_, v_i_1391_, v_stop_1392_);
stack->m_num = v_res_1400_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(lean_object* v_mod_1401_, lean_object* v_as_1402_, lean_object* v_i_1403_, lean_object* v_stop_1404_){
_start:
{
size_t v_i_boxed_1405_; size_t v_stop_boxed_1406_; uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_i_boxed_1405_ = lean_unbox_usize(v_i_1403_);
lean_dec(v_i_1403_);
v_stop_boxed_1406_ = lean_unbox_usize(v_stop_1404_);
lean_dec(v_stop_1404_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1401_, v_as_1402_, v_i_boxed_1405_, v_stop_boxed_1406_);
lean_dec_ref(v_as_1402_);
lean_dec(v_mod_1401_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object* v_mod_1409_, lean_object* v_self_1410_){
_start:
{
lean_object* v_roots_1411_; lean_object* v_globs_1412_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_roots_1411_ = lean_ctor_get(v_self_1410_, 2);
v_globs_1412_ = lean_ctor_get(v_self_1410_, 3);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_array_get_size(v_roots_1411_);
v___x_1422_ = lean_nat_dec_lt(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
goto v___jp_1413_;
}
else
{
if (v___x_1422_ == 0)
{
goto v___jp_1413_;
}
else
{
size_t v___x_1423_; size_t v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1421_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1409_, v_roots_1411_, v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
goto v___jp_1413_;
}
else
{
return v___x_1425_;
}
}
}
v___jp_1413_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_globs_1412_);
v___x_1416_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
return v___x_1416_;
}
else
{
if (v___x_1416_ == 0)
{
return v___x_1416_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1415_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1409_, v_globs_1412_, v___x_1417_, v___x_1418_);
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_isLocalModule___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1409_ = stack[0].m_obj;
lean_object* v_self_1410_ = stack[1].m_obj;
uint8_t v_res_1426_;
v_res_1426_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1409_, v_self_1410_);
stack->m_num = v_res_1426_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(lean_object* v_mod_1427_, lean_object* v_self_1428_){
_start:
{
uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_res_1429_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1427_, v_self_1428_);
lean_dec_ref(v_self_1428_);
lean_dec(v_mod_1427_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object* v_n_1431_, lean_object* v_mod_1432_, lean_object* v_self_1433_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1432_, v_self_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_isLocalModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1431_ = stack[0].m_obj;
lean_object* v_mod_1432_ = stack[1].m_obj;
lean_object* v_self_1433_ = stack[2].m_obj;
uint8_t v_res_1435_;
v_res_1435_ = l_Lake_LeanLibConfig_isLocalModule(v_n_1431_, v_mod_1432_, v_self_1433_);
stack->m_num = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___boxed(lean_object* v_n_1436_, lean_object* v_mod_1437_, lean_object* v_self_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l_Lake_LeanLibConfig_isLocalModule(v_n_1436_, v_mod_1437_, v_self_1438_);
lean_dec_ref(v_self_1438_);
lean_dec(v_mod_1437_);
lean_dec(v_n_1436_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(lean_object* v_mod_1441_, lean_object* v_self_1442_, lean_object* v_as_1443_, size_t v_i_1444_, size_t v_stop_1445_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_usize_dec_eq(v_i_1444_, v_stop_1445_);
if (v___x_1450_ == 0)
{
uint8_t v___x_1451_; uint8_t v___y_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1451_ = 1;
v___x_1454_ = lean_array_uget_borrowed(v_as_1443_, v_i_1444_);
v___x_1455_ = l_Lean_Name_isPrefixOf(v___x_1454_, v_mod_1441_);
if (v___x_1455_ == 0)
{
v___y_1453_ = v___x_1455_;
goto v___jp_1452_;
}
else
{
lean_object* v_globs_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_globs_1456_ = lean_ctor_get(v_self_1442_, 3);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_array_get_size(v_globs_1456_);
v___x_1459_ = lean_nat_dec_lt(v___x_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
goto v___jp_1446_;
}
else
{
if (v___x_1459_ == 0)
{
goto v___jp_1446_;
}
else
{
size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = lean_usize_of_nat(v___x_1458_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v___x_1454_, v_globs_1456_, v___x_1460_, v___x_1461_);
v___y_1453_ = v___x_1462_;
goto v___jp_1452_;
}
}
}
v___jp_1452_:
{
if (v___y_1453_ == 0)
{
goto v___jp_1446_;
}
else
{
return v___x_1451_;
}
}
}
else
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
v___jp_1446_:
{
size_t v___x_1447_; size_t v___x_1448_; 
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_add(v_i_1444_, v___x_1447_);
v_i_1444_ = v___x_1448_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1441_ = stack[0].m_obj;
lean_object* v_self_1442_ = stack[1].m_obj;
lean_object* v_as_1443_ = stack[2].m_obj;
size_t v_i_1444_ = stack[3].m_num;
size_t v_stop_1445_ = stack[4].m_num;
uint8_t v_res_1464_;
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1441_, v_self_1442_, v_as_1443_, v_i_1444_, v_stop_1445_);
stack->m_num = v_res_1464_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(lean_object* v_mod_1465_, lean_object* v_self_1466_, lean_object* v_as_1467_, lean_object* v_i_1468_, lean_object* v_stop_1469_){
_start:
{
size_t v_i_boxed_1470_; size_t v_stop_boxed_1471_; uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_i_boxed_1470_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_stop_boxed_1471_ = lean_unbox_usize(v_stop_1469_);
lean_dec(v_stop_1469_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1465_, v_self_1466_, v_as_1467_, v_i_boxed_1470_, v_stop_boxed_1471_);
lean_dec_ref(v_as_1467_);
lean_dec_ref(v_self_1466_);
lean_dec(v_mod_1465_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object* v_mod_1474_, lean_object* v_self_1475_){
_start:
{
lean_object* v_roots_1476_; lean_object* v_globs_1477_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_roots_1476_ = lean_ctor_get(v_self_1475_, 2);
v_globs_1477_ = lean_ctor_get(v_self_1475_, 3);
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_array_get_size(v_globs_1477_);
v___x_1487_ = lean_nat_dec_lt(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
goto v___jp_1478_;
}
else
{
if (v___x_1487_ == 0)
{
goto v___jp_1478_;
}
else
{
size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1486_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1474_, v_globs_1477_, v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
goto v___jp_1478_;
}
else
{
return v___x_1490_;
}
}
}
v___jp_1478_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_array_get_size(v_roots_1476_);
v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
return v___x_1481_;
}
else
{
if (v___x_1481_ == 0)
{
return v___x_1481_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1480_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1474_, v_self_1475_, v_roots_1476_, v___x_1482_, v___x_1483_);
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_isBuildableModule___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1474_ = stack[0].m_obj;
lean_object* v_self_1475_ = stack[1].m_obj;
uint8_t v_res_1491_;
v_res_1491_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1474_, v_self_1475_);
stack->m_num = v_res_1491_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(lean_object* v_mod_1492_, lean_object* v_self_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1492_, v_self_1493_);
lean_dec_ref(v_self_1493_);
lean_dec(v_mod_1492_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object* v_n_1496_, lean_object* v_mod_1497_, lean_object* v_self_1498_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1497_, v_self_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT void l_Lake_LeanLibConfig_isBuildableModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1496_ = stack[0].m_obj;
lean_object* v_mod_1497_ = stack[1].m_obj;
lean_object* v_self_1498_ = stack[2].m_obj;
uint8_t v_res_1500_;
v_res_1500_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_1496_, v_mod_1497_, v_self_1498_);
stack->m_num = v_res_1500_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___boxed(lean_object* v_n_1501_, lean_object* v_mod_1502_, lean_object* v_self_1503_){
_start:
{
uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_res_1504_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_1501_, v_mod_1502_, v_self_1503_);
lean_dec_ref(v_self_1503_);
lean_dec(v_mod_1502_);
lean_dec(v_n_1501_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
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
