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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0(lean_object* v_cfg_56_){
_start:
{
lean_object* v_srcDir_57_; 
v_srcDir_57_ = lean_ctor_get(v_cfg_56_, 1);
lean_inc_ref(v_srcDir_57_);
return v_srcDir_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__0(v_cfg_58_);
lean_dec_ref(v_cfg_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__1(lean_object* v_val_60_, lean_object* v_cfg_61_){
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__2(lean_object* v_f_82_, lean_object* v_cfg_83_){
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3(lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3___boxed(lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lake_LeanLibConfig_srcDir___proj___redArg___lam__3(v_x_107_);
lean_dec_ref(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg(){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lake_LeanLibConfig_srcDir___proj___redArg___closed__4));
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___redArg___boxed(lean_object* v___dummy_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lake_LeanLibConfig_srcDir___proj___redArg();
return v_res_121_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lake_LeanLibConfig_srcDir___proj___redArg();
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object* v_name_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lake_LeanLibConfig_srcDir___proj___closed__0, &l_Lake_LeanLibConfig_srcDir___proj___closed__0_once, _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir___proj___boxed(lean_object* v_name_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_125_);
lean_dec(v_name_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lake_LeanLibConfig_srcDir___proj___closed__0, &l_Lake_LeanLibConfig_srcDir___proj___closed__0_once, _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___redArg___boxed(lean_object* v___dummy_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_LeanLibConfig_srcDir_instConfigField___redArg();
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField(lean_object* v_name_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lake_LeanLibConfig_srcDir___proj___closed__0, &l_Lake_LeanLibConfig_srcDir___proj___closed__0_once, _init_l_Lake_LeanLibConfig_srcDir___proj___closed__0);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(lean_object* v_name_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_133_);
lean_dec(v_name_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0(lean_object* v_cfg_135_){
_start:
{
lean_object* v_roots_136_; 
v_roots_136_ = lean_ctor_get(v_cfg_135_, 2);
lean_inc_ref(v_roots_136_);
return v_roots_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(lean_object* v_cfg_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_137_);
lean_dec_ref(v_cfg_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__1(lean_object* v_val_139_, lean_object* v_cfg_140_){
_start:
{
lean_object* v_toLeanConfig_141_; lean_object* v_srcDir_142_; lean_object* v_globs_143_; lean_object* v_libName_144_; uint8_t v_libPrefixOnWindows_145_; lean_object* v_needs_146_; lean_object* v_extraDepTargets_147_; uint8_t v_precompileLibrary_148_; uint8_t v_precompileModules_149_; lean_object* v_defaultFacets_150_; lean_object* v_nativeFacets_151_; uint8_t v_allowImportAll_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_toLeanConfig_141_ = lean_ctor_get(v_cfg_140_, 0);
v_srcDir_142_ = lean_ctor_get(v_cfg_140_, 1);
v_globs_143_ = lean_ctor_get(v_cfg_140_, 3);
v_libName_144_ = lean_ctor_get(v_cfg_140_, 4);
v_libPrefixOnWindows_145_ = lean_ctor_get_uint8(v_cfg_140_, sizeof(void*)*9);
v_needs_146_ = lean_ctor_get(v_cfg_140_, 5);
v_extraDepTargets_147_ = lean_ctor_get(v_cfg_140_, 6);
v_precompileLibrary_148_ = lean_ctor_get_uint8(v_cfg_140_, sizeof(void*)*9 + 1);
v_precompileModules_149_ = lean_ctor_get_uint8(v_cfg_140_, sizeof(void*)*9 + 2);
v_defaultFacets_150_ = lean_ctor_get(v_cfg_140_, 7);
v_nativeFacets_151_ = lean_ctor_get(v_cfg_140_, 8);
v_allowImportAll_152_ = lean_ctor_get_uint8(v_cfg_140_, sizeof(void*)*9 + 3);
v_isSharedCheck_159_ = !lean_is_exclusive(v_cfg_140_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_cfg_140_, 2);
lean_dec(v_unused_160_);
v___x_154_ = v_cfg_140_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_nativeFacets_151_);
lean_inc(v_defaultFacets_150_);
lean_inc(v_extraDepTargets_147_);
lean_inc(v_needs_146_);
lean_inc(v_libName_144_);
lean_inc(v_globs_143_);
lean_inc(v_srcDir_142_);
lean_inc(v_toLeanConfig_141_);
lean_dec(v_cfg_140_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 2, v_val_139_);
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_toLeanConfig_141_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_srcDir_142_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_val_139_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_globs_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v_libName_144_);
lean_ctor_set(v_reuseFailAlloc_158_, 5, v_needs_146_);
lean_ctor_set(v_reuseFailAlloc_158_, 6, v_extraDepTargets_147_);
lean_ctor_set(v_reuseFailAlloc_158_, 7, v_defaultFacets_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 8, v_nativeFacets_151_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*9, v_libPrefixOnWindows_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*9 + 1, v_precompileLibrary_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*9 + 2, v_precompileModules_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*9 + 3, v_allowImportAll_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__2(lean_object* v_f_161_, lean_object* v_cfg_162_){
_start:
{
lean_object* v_toLeanConfig_163_; lean_object* v_srcDir_164_; lean_object* v_roots_165_; lean_object* v_globs_166_; lean_object* v_libName_167_; uint8_t v_libPrefixOnWindows_168_; lean_object* v_needs_169_; lean_object* v_extraDepTargets_170_; uint8_t v_precompileLibrary_171_; uint8_t v_precompileModules_172_; lean_object* v_defaultFacets_173_; lean_object* v_nativeFacets_174_; uint8_t v_allowImportAll_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_toLeanConfig_163_ = lean_ctor_get(v_cfg_162_, 0);
v_srcDir_164_ = lean_ctor_get(v_cfg_162_, 1);
v_roots_165_ = lean_ctor_get(v_cfg_162_, 2);
v_globs_166_ = lean_ctor_get(v_cfg_162_, 3);
v_libName_167_ = lean_ctor_get(v_cfg_162_, 4);
v_libPrefixOnWindows_168_ = lean_ctor_get_uint8(v_cfg_162_, sizeof(void*)*9);
v_needs_169_ = lean_ctor_get(v_cfg_162_, 5);
v_extraDepTargets_170_ = lean_ctor_get(v_cfg_162_, 6);
v_precompileLibrary_171_ = lean_ctor_get_uint8(v_cfg_162_, sizeof(void*)*9 + 1);
v_precompileModules_172_ = lean_ctor_get_uint8(v_cfg_162_, sizeof(void*)*9 + 2);
v_defaultFacets_173_ = lean_ctor_get(v_cfg_162_, 7);
v_nativeFacets_174_ = lean_ctor_get(v_cfg_162_, 8);
v_allowImportAll_175_ = lean_ctor_get_uint8(v_cfg_162_, sizeof(void*)*9 + 3);
v_isSharedCheck_183_ = !lean_is_exclusive(v_cfg_162_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v_cfg_162_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_nativeFacets_174_);
lean_inc(v_defaultFacets_173_);
lean_inc(v_extraDepTargets_170_);
lean_inc(v_needs_169_);
lean_inc(v_libName_167_);
lean_inc(v_globs_166_);
lean_inc(v_roots_165_);
lean_inc(v_srcDir_164_);
lean_inc(v_toLeanConfig_163_);
lean_dec(v_cfg_162_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_apply_1(v_f_161_, v_roots_165_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 2, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_toLeanConfig_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_srcDir_164_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_globs_166_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_libName_167_);
lean_ctor_set(v_reuseFailAlloc_182_, 5, v_needs_169_);
lean_ctor_set(v_reuseFailAlloc_182_, 6, v_extraDepTargets_170_);
lean_ctor_set(v_reuseFailAlloc_182_, 7, v_defaultFacets_173_);
lean_ctor_set(v_reuseFailAlloc_182_, 8, v_nativeFacets_174_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9, v_libPrefixOnWindows_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9 + 1, v_precompileLibrary_171_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9 + 2, v_precompileModules_172_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*9 + 3, v_allowImportAll_175_);
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
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3(lean_object* v_name_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
v___x_188_ = lean_array_push(v___x_187_, v_name_184_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(lean_object* v_name_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_189_, v_x_190_);
lean_dec_ref(v_x_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object* v_name_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; 
v___f_196_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__0));
v___f_197_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__1));
v___f_198_ = ((lean_object*)(l_Lake_LeanLibConfig_roots___proj___closed__2));
v___f_199_ = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_roots___proj___lam__3___boxed), 2, 1);
lean_closure_set(v___f_199_, 0, v_name_195_);
v___x_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_200_, 0, v___f_196_);
lean_ctor_set(v___x_200_, 1, v___f_197_);
lean_ctor_set(v___x_200_, 2, v___f_198_);
lean_ctor_set(v___x_200_, 3, v___f_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_roots_instConfigField(lean_object* v_name_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lake_LeanLibConfig_roots___proj(v_name_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__0(lean_object* v_cfg_203_){
_start:
{
lean_object* v_globs_204_; 
v_globs_204_ = lean_ctor_get(v_cfg_203_, 3);
lean_inc_ref(v_globs_204_);
return v_globs_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__0___boxed(lean_object* v_cfg_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_LeanLibConfig_globs___proj___redArg___lam__0(v_cfg_205_);
lean_dec_ref(v_cfg_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__1(lean_object* v_val_207_, lean_object* v_cfg_208_){
_start:
{
lean_object* v_toLeanConfig_209_; lean_object* v_srcDir_210_; lean_object* v_roots_211_; lean_object* v_libName_212_; uint8_t v_libPrefixOnWindows_213_; lean_object* v_needs_214_; lean_object* v_extraDepTargets_215_; uint8_t v_precompileLibrary_216_; uint8_t v_precompileModules_217_; lean_object* v_defaultFacets_218_; lean_object* v_nativeFacets_219_; uint8_t v_allowImportAll_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_toLeanConfig_209_ = lean_ctor_get(v_cfg_208_, 0);
v_srcDir_210_ = lean_ctor_get(v_cfg_208_, 1);
v_roots_211_ = lean_ctor_get(v_cfg_208_, 2);
v_libName_212_ = lean_ctor_get(v_cfg_208_, 4);
v_libPrefixOnWindows_213_ = lean_ctor_get_uint8(v_cfg_208_, sizeof(void*)*9);
v_needs_214_ = lean_ctor_get(v_cfg_208_, 5);
v_extraDepTargets_215_ = lean_ctor_get(v_cfg_208_, 6);
v_precompileLibrary_216_ = lean_ctor_get_uint8(v_cfg_208_, sizeof(void*)*9 + 1);
v_precompileModules_217_ = lean_ctor_get_uint8(v_cfg_208_, sizeof(void*)*9 + 2);
v_defaultFacets_218_ = lean_ctor_get(v_cfg_208_, 7);
v_nativeFacets_219_ = lean_ctor_get(v_cfg_208_, 8);
v_allowImportAll_220_ = lean_ctor_get_uint8(v_cfg_208_, sizeof(void*)*9 + 3);
v_isSharedCheck_227_ = !lean_is_exclusive(v_cfg_208_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_cfg_208_, 3);
lean_dec(v_unused_228_);
v___x_222_ = v_cfg_208_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_nativeFacets_219_);
lean_inc(v_defaultFacets_218_);
lean_inc(v_extraDepTargets_215_);
lean_inc(v_needs_214_);
lean_inc(v_libName_212_);
lean_inc(v_roots_211_);
lean_inc(v_srcDir_210_);
lean_inc(v_toLeanConfig_209_);
lean_dec(v_cfg_208_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 3, v_val_207_);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_toLeanConfig_209_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_srcDir_210_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_roots_211_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_val_207_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_libName_212_);
lean_ctor_set(v_reuseFailAlloc_226_, 5, v_needs_214_);
lean_ctor_set(v_reuseFailAlloc_226_, 6, v_extraDepTargets_215_);
lean_ctor_set(v_reuseFailAlloc_226_, 7, v_defaultFacets_218_);
lean_ctor_set(v_reuseFailAlloc_226_, 8, v_nativeFacets_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*9, v_libPrefixOnWindows_213_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*9 + 1, v_precompileLibrary_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*9 + 2, v_precompileModules_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*9 + 3, v_allowImportAll_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__2(lean_object* v_f_229_, lean_object* v_cfg_230_){
_start:
{
lean_object* v_toLeanConfig_231_; lean_object* v_srcDir_232_; lean_object* v_roots_233_; lean_object* v_globs_234_; lean_object* v_libName_235_; uint8_t v_libPrefixOnWindows_236_; lean_object* v_needs_237_; lean_object* v_extraDepTargets_238_; uint8_t v_precompileLibrary_239_; uint8_t v_precompileModules_240_; lean_object* v_defaultFacets_241_; lean_object* v_nativeFacets_242_; uint8_t v_allowImportAll_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v_toLeanConfig_231_ = lean_ctor_get(v_cfg_230_, 0);
v_srcDir_232_ = lean_ctor_get(v_cfg_230_, 1);
v_roots_233_ = lean_ctor_get(v_cfg_230_, 2);
v_globs_234_ = lean_ctor_get(v_cfg_230_, 3);
v_libName_235_ = lean_ctor_get(v_cfg_230_, 4);
v_libPrefixOnWindows_236_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*9);
v_needs_237_ = lean_ctor_get(v_cfg_230_, 5);
v_extraDepTargets_238_ = lean_ctor_get(v_cfg_230_, 6);
v_precompileLibrary_239_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*9 + 1);
v_precompileModules_240_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*9 + 2);
v_defaultFacets_241_ = lean_ctor_get(v_cfg_230_, 7);
v_nativeFacets_242_ = lean_ctor_get(v_cfg_230_, 8);
v_allowImportAll_243_ = lean_ctor_get_uint8(v_cfg_230_, sizeof(void*)*9 + 3);
v_isSharedCheck_251_ = !lean_is_exclusive(v_cfg_230_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v_cfg_230_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_nativeFacets_242_);
lean_inc(v_defaultFacets_241_);
lean_inc(v_extraDepTargets_238_);
lean_inc(v_needs_237_);
lean_inc(v_libName_235_);
lean_inc(v_globs_234_);
lean_inc(v_roots_233_);
lean_inc(v_srcDir_232_);
lean_inc(v_toLeanConfig_231_);
lean_dec(v_cfg_230_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_apply_1(v_f_229_, v_globs_234_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 3, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_toLeanConfig_231_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_srcDir_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_roots_233_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_libName_235_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_needs_237_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v_extraDepTargets_238_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_defaultFacets_241_);
lean_ctor_set(v_reuseFailAlloc_250_, 8, v_nativeFacets_242_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*9, v_libPrefixOnWindows_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*9 + 1, v_precompileLibrary_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*9 + 2, v_precompileModules_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*9 + 3, v_allowImportAll_243_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___lam__3(lean_object* v_x_252_){
_start:
{
lean_object* v_roots_253_; size_t v_sz_254_; size_t v___x_255_; lean_object* v___x_256_; 
v_roots_253_ = lean_ctor_get(v_x_252_, 2);
lean_inc_ref(v_roots_253_);
lean_dec_ref(v_x_252_);
v_sz_254_ = lean_array_size(v_roots_253_);
v___x_255_ = ((size_t)0ULL);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_254_, v___x_255_, v_roots_253_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg(){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Lake_LeanLibConfig_globs___proj___redArg___closed__4));
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___redArg___boxed(lean_object* v___dummy_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_LeanLibConfig_globs___proj___redArg();
return v_res_269_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_globs___proj___closed__0(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lake_LeanLibConfig_globs___proj___redArg();
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object* v_name_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lake_LeanLibConfig_globs___proj___closed__0, &l_Lake_LeanLibConfig_globs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_globs___proj___closed__0);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs___proj___boxed(lean_object* v_name_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_LeanLibConfig_globs___proj(v_name_273_);
lean_dec(v_name_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___redArg(){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lake_LeanLibConfig_globs___proj___closed__0, &l_Lake_LeanLibConfig_globs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_globs___proj___closed__0);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___redArg___boxed(lean_object* v___dummy_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lake_LeanLibConfig_globs_instConfigField___redArg();
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField(lean_object* v_name_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lake_LeanLibConfig_globs___proj___closed__0, &l_Lake_LeanLibConfig_globs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_globs___proj___closed__0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_globs_instConfigField___boxed(lean_object* v_name_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_281_);
lean_dec(v_name_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__0(lean_object* v_cfg_283_){
_start:
{
lean_object* v_libName_284_; 
v_libName_284_ = lean_ctor_get(v_cfg_283_, 4);
lean_inc_ref(v_libName_284_);
return v_libName_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__0___boxed(lean_object* v_cfg_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lake_LeanLibConfig_libName___proj___redArg___lam__0(v_cfg_285_);
lean_dec_ref(v_cfg_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__1(lean_object* v_val_287_, lean_object* v_cfg_288_){
_start:
{
lean_object* v_toLeanConfig_289_; lean_object* v_srcDir_290_; lean_object* v_roots_291_; lean_object* v_globs_292_; uint8_t v_libPrefixOnWindows_293_; lean_object* v_needs_294_; lean_object* v_extraDepTargets_295_; uint8_t v_precompileLibrary_296_; uint8_t v_precompileModules_297_; lean_object* v_defaultFacets_298_; lean_object* v_nativeFacets_299_; uint8_t v_allowImportAll_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_toLeanConfig_289_ = lean_ctor_get(v_cfg_288_, 0);
v_srcDir_290_ = lean_ctor_get(v_cfg_288_, 1);
v_roots_291_ = lean_ctor_get(v_cfg_288_, 2);
v_globs_292_ = lean_ctor_get(v_cfg_288_, 3);
v_libPrefixOnWindows_293_ = lean_ctor_get_uint8(v_cfg_288_, sizeof(void*)*9);
v_needs_294_ = lean_ctor_get(v_cfg_288_, 5);
v_extraDepTargets_295_ = lean_ctor_get(v_cfg_288_, 6);
v_precompileLibrary_296_ = lean_ctor_get_uint8(v_cfg_288_, sizeof(void*)*9 + 1);
v_precompileModules_297_ = lean_ctor_get_uint8(v_cfg_288_, sizeof(void*)*9 + 2);
v_defaultFacets_298_ = lean_ctor_get(v_cfg_288_, 7);
v_nativeFacets_299_ = lean_ctor_get(v_cfg_288_, 8);
v_allowImportAll_300_ = lean_ctor_get_uint8(v_cfg_288_, sizeof(void*)*9 + 3);
v_isSharedCheck_307_ = !lean_is_exclusive(v_cfg_288_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_cfg_288_, 4);
lean_dec(v_unused_308_);
v___x_302_ = v_cfg_288_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_nativeFacets_299_);
lean_inc(v_defaultFacets_298_);
lean_inc(v_extraDepTargets_295_);
lean_inc(v_needs_294_);
lean_inc(v_globs_292_);
lean_inc(v_roots_291_);
lean_inc(v_srcDir_290_);
lean_inc(v_toLeanConfig_289_);
lean_dec(v_cfg_288_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_val_287_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_toLeanConfig_289_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_srcDir_290_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_roots_291_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_globs_292_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_val_287_);
lean_ctor_set(v_reuseFailAlloc_306_, 5, v_needs_294_);
lean_ctor_set(v_reuseFailAlloc_306_, 6, v_extraDepTargets_295_);
lean_ctor_set(v_reuseFailAlloc_306_, 7, v_defaultFacets_298_);
lean_ctor_set(v_reuseFailAlloc_306_, 8, v_nativeFacets_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*9, v_libPrefixOnWindows_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*9 + 1, v_precompileLibrary_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*9 + 2, v_precompileModules_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*9 + 3, v_allowImportAll_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__2(lean_object* v_f_309_, lean_object* v_cfg_310_){
_start:
{
lean_object* v_toLeanConfig_311_; lean_object* v_srcDir_312_; lean_object* v_roots_313_; lean_object* v_globs_314_; lean_object* v_libName_315_; uint8_t v_libPrefixOnWindows_316_; lean_object* v_needs_317_; lean_object* v_extraDepTargets_318_; uint8_t v_precompileLibrary_319_; uint8_t v_precompileModules_320_; lean_object* v_defaultFacets_321_; lean_object* v_nativeFacets_322_; uint8_t v_allowImportAll_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_toLeanConfig_311_ = lean_ctor_get(v_cfg_310_, 0);
v_srcDir_312_ = lean_ctor_get(v_cfg_310_, 1);
v_roots_313_ = lean_ctor_get(v_cfg_310_, 2);
v_globs_314_ = lean_ctor_get(v_cfg_310_, 3);
v_libName_315_ = lean_ctor_get(v_cfg_310_, 4);
v_libPrefixOnWindows_316_ = lean_ctor_get_uint8(v_cfg_310_, sizeof(void*)*9);
v_needs_317_ = lean_ctor_get(v_cfg_310_, 5);
v_extraDepTargets_318_ = lean_ctor_get(v_cfg_310_, 6);
v_precompileLibrary_319_ = lean_ctor_get_uint8(v_cfg_310_, sizeof(void*)*9 + 1);
v_precompileModules_320_ = lean_ctor_get_uint8(v_cfg_310_, sizeof(void*)*9 + 2);
v_defaultFacets_321_ = lean_ctor_get(v_cfg_310_, 7);
v_nativeFacets_322_ = lean_ctor_get(v_cfg_310_, 8);
v_allowImportAll_323_ = lean_ctor_get_uint8(v_cfg_310_, sizeof(void*)*9 + 3);
v_isSharedCheck_331_ = !lean_is_exclusive(v_cfg_310_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v_cfg_310_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_nativeFacets_322_);
lean_inc(v_defaultFacets_321_);
lean_inc(v_extraDepTargets_318_);
lean_inc(v_needs_317_);
lean_inc(v_libName_315_);
lean_inc(v_globs_314_);
lean_inc(v_roots_313_);
lean_inc(v_srcDir_312_);
lean_inc(v_toLeanConfig_311_);
lean_dec(v_cfg_310_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_apply_1(v_f_309_, v_libName_315_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v___x_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_toLeanConfig_311_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_srcDir_312_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_roots_313_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_globs_314_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v_needs_317_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_extraDepTargets_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_defaultFacets_321_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_nativeFacets_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*9, v_libPrefixOnWindows_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*9 + 1, v_precompileLibrary_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*9 + 2, v_precompileModules_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*9 + 3, v_allowImportAll_323_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__3(lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___lam__3___boxed(lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_LeanLibConfig_libName___proj___redArg___lam__3(v_x_334_);
lean_dec_ref(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg(){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = ((lean_object*)(l_Lake_LeanLibConfig_libName___proj___redArg___closed__4));
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___redArg___boxed(lean_object* v___dummy_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lake_LeanLibConfig_libName___proj___redArg();
return v_res_348_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_libName___proj___closed__0(void){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lake_LeanLibConfig_libName___proj___redArg();
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object* v_name_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lake_LeanLibConfig_libName___proj___closed__0, &l_Lake_LeanLibConfig_libName___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libName___proj___closed__0);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName___proj___boxed(lean_object* v_name_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lake_LeanLibConfig_libName___proj(v_name_352_);
lean_dec(v_name_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___redArg(){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l_Lake_LeanLibConfig_libName___proj___closed__0, &l_Lake_LeanLibConfig_libName___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libName___proj___closed__0);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___redArg___boxed(lean_object* v___dummy_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lake_LeanLibConfig_libName_instConfigField___redArg();
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField(lean_object* v_name_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Lake_LeanLibConfig_libName___proj___closed__0, &l_Lake_LeanLibConfig_libName___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libName___proj___closed__0);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libName_instConfigField___boxed(lean_object* v_name_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_360_);
lean_dec(v_name_360_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object* v_cfg_362_){
_start:
{
uint8_t v_libPrefixOnWindows_363_; 
v_libPrefixOnWindows_363_ = lean_ctor_get_uint8(v_cfg_362_, sizeof(void*)*9);
return v_libPrefixOnWindows_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object* v_cfg_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_364_);
lean_dec_ref(v_cfg_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t v_val_367_, lean_object* v_cfg_368_){
_start:
{
lean_object* v_toLeanConfig_369_; lean_object* v_srcDir_370_; lean_object* v_roots_371_; lean_object* v_globs_372_; lean_object* v_libName_373_; lean_object* v_needs_374_; lean_object* v_extraDepTargets_375_; uint8_t v_precompileLibrary_376_; uint8_t v_precompileModules_377_; lean_object* v_defaultFacets_378_; lean_object* v_nativeFacets_379_; uint8_t v_allowImportAll_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_toLeanConfig_369_ = lean_ctor_get(v_cfg_368_, 0);
v_srcDir_370_ = lean_ctor_get(v_cfg_368_, 1);
v_roots_371_ = lean_ctor_get(v_cfg_368_, 2);
v_globs_372_ = lean_ctor_get(v_cfg_368_, 3);
v_libName_373_ = lean_ctor_get(v_cfg_368_, 4);
v_needs_374_ = lean_ctor_get(v_cfg_368_, 5);
v_extraDepTargets_375_ = lean_ctor_get(v_cfg_368_, 6);
v_precompileLibrary_376_ = lean_ctor_get_uint8(v_cfg_368_, sizeof(void*)*9 + 1);
v_precompileModules_377_ = lean_ctor_get_uint8(v_cfg_368_, sizeof(void*)*9 + 2);
v_defaultFacets_378_ = lean_ctor_get(v_cfg_368_, 7);
v_nativeFacets_379_ = lean_ctor_get(v_cfg_368_, 8);
v_allowImportAll_380_ = lean_ctor_get_uint8(v_cfg_368_, sizeof(void*)*9 + 3);
v_isSharedCheck_387_ = !lean_is_exclusive(v_cfg_368_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v_cfg_368_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_nativeFacets_379_);
lean_inc(v_defaultFacets_378_);
lean_inc(v_extraDepTargets_375_);
lean_inc(v_needs_374_);
lean_inc(v_libName_373_);
lean_inc(v_globs_372_);
lean_inc(v_roots_371_);
lean_inc(v_srcDir_370_);
lean_inc(v_toLeanConfig_369_);
lean_dec(v_cfg_368_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_toLeanConfig_369_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_srcDir_370_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_roots_371_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_globs_372_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v_libName_373_);
lean_ctor_set(v_reuseFailAlloc_386_, 5, v_needs_374_);
lean_ctor_set(v_reuseFailAlloc_386_, 6, v_extraDepTargets_375_);
lean_ctor_set(v_reuseFailAlloc_386_, 7, v_defaultFacets_378_);
lean_ctor_set(v_reuseFailAlloc_386_, 8, v_nativeFacets_379_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, sizeof(void*)*9 + 1, v_precompileLibrary_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, sizeof(void*)*9 + 2, v_precompileModules_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, sizeof(void*)*9 + 3, v_allowImportAll_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*9, v_val_367_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object* v_val_388_, lean_object* v_cfg_389_){
_start:
{
uint8_t v_val_75__boxed_390_; lean_object* v_res_391_; 
v_val_75__boxed_390_ = lean_unbox(v_val_388_);
v_res_391_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_75__boxed_390_, v_cfg_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object* v_f_392_, lean_object* v_cfg_393_){
_start:
{
lean_object* v_toLeanConfig_394_; lean_object* v_srcDir_395_; lean_object* v_roots_396_; lean_object* v_globs_397_; lean_object* v_libName_398_; uint8_t v_libPrefixOnWindows_399_; lean_object* v_needs_400_; lean_object* v_extraDepTargets_401_; uint8_t v_precompileLibrary_402_; uint8_t v_precompileModules_403_; lean_object* v_defaultFacets_404_; lean_object* v_nativeFacets_405_; uint8_t v_allowImportAll_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
v_toLeanConfig_394_ = lean_ctor_get(v_cfg_393_, 0);
v_srcDir_395_ = lean_ctor_get(v_cfg_393_, 1);
v_roots_396_ = lean_ctor_get(v_cfg_393_, 2);
v_globs_397_ = lean_ctor_get(v_cfg_393_, 3);
v_libName_398_ = lean_ctor_get(v_cfg_393_, 4);
v_libPrefixOnWindows_399_ = lean_ctor_get_uint8(v_cfg_393_, sizeof(void*)*9);
v_needs_400_ = lean_ctor_get(v_cfg_393_, 5);
v_extraDepTargets_401_ = lean_ctor_get(v_cfg_393_, 6);
v_precompileLibrary_402_ = lean_ctor_get_uint8(v_cfg_393_, sizeof(void*)*9 + 1);
v_precompileModules_403_ = lean_ctor_get_uint8(v_cfg_393_, sizeof(void*)*9 + 2);
v_defaultFacets_404_ = lean_ctor_get(v_cfg_393_, 7);
v_nativeFacets_405_ = lean_ctor_get(v_cfg_393_, 8);
v_allowImportAll_406_ = lean_ctor_get_uint8(v_cfg_393_, sizeof(void*)*9 + 3);
v_isSharedCheck_416_ = !lean_is_exclusive(v_cfg_393_);
if (v_isSharedCheck_416_ == 0)
{
v___x_408_ = v_cfg_393_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_nativeFacets_405_);
lean_inc(v_defaultFacets_404_);
lean_inc(v_extraDepTargets_401_);
lean_inc(v_needs_400_);
lean_inc(v_libName_398_);
lean_inc(v_globs_397_);
lean_inc(v_roots_396_);
lean_inc(v_srcDir_395_);
lean_inc(v_toLeanConfig_394_);
lean_dec(v_cfg_393_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_410_ = lean_box(v_libPrefixOnWindows_399_);
v___x_411_ = lean_apply_1(v_f_392_, v___x_410_);
if (v_isShared_409_ == 0)
{
v___x_413_ = v___x_408_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_toLeanConfig_394_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_srcDir_395_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_roots_396_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_globs_397_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v_libName_398_);
lean_ctor_set(v_reuseFailAlloc_415_, 5, v_needs_400_);
lean_ctor_set(v_reuseFailAlloc_415_, 6, v_extraDepTargets_401_);
lean_ctor_set(v_reuseFailAlloc_415_, 7, v_defaultFacets_404_);
lean_ctor_set(v_reuseFailAlloc_415_, 8, v_nativeFacets_405_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
uint8_t v___x_414_; 
v___x_414_ = lean_unbox(v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*9, v___x_414_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*9 + 1, v_precompileLibrary_402_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*9 + 2, v_precompileModules_403_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*9 + 3, v_allowImportAll_406_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3(lean_object* v_x_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3___boxed(lean_object* v_x_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___lam__3(v_x_419_);
lean_dec_ref(v_x_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg(){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___closed__4));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object* v___dummy_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg();
return v_res_434_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0(void){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___redArg();
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object* v_name_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(lean_object* v_name_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_438_);
lean_dec(v_name_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg(){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object* v___dummy_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___redArg();
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(lean_object* v_name_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_name_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_446_);
lean_dec(v_name_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__0(lean_object* v_cfg_448_){
_start:
{
lean_object* v_needs_449_; 
v_needs_449_ = lean_ctor_get(v_cfg_448_, 5);
lean_inc_ref(v_needs_449_);
return v_needs_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__0___boxed(lean_object* v_cfg_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_LeanLibConfig_needs___proj___redArg___lam__0(v_cfg_450_);
lean_dec_ref(v_cfg_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__1(lean_object* v_val_452_, lean_object* v_cfg_453_){
_start:
{
lean_object* v_toLeanConfig_454_; lean_object* v_srcDir_455_; lean_object* v_roots_456_; lean_object* v_globs_457_; lean_object* v_libName_458_; uint8_t v_libPrefixOnWindows_459_; lean_object* v_extraDepTargets_460_; uint8_t v_precompileLibrary_461_; uint8_t v_precompileModules_462_; lean_object* v_defaultFacets_463_; lean_object* v_nativeFacets_464_; uint8_t v_allowImportAll_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_toLeanConfig_454_ = lean_ctor_get(v_cfg_453_, 0);
v_srcDir_455_ = lean_ctor_get(v_cfg_453_, 1);
v_roots_456_ = lean_ctor_get(v_cfg_453_, 2);
v_globs_457_ = lean_ctor_get(v_cfg_453_, 3);
v_libName_458_ = lean_ctor_get(v_cfg_453_, 4);
v_libPrefixOnWindows_459_ = lean_ctor_get_uint8(v_cfg_453_, sizeof(void*)*9);
v_extraDepTargets_460_ = lean_ctor_get(v_cfg_453_, 6);
v_precompileLibrary_461_ = lean_ctor_get_uint8(v_cfg_453_, sizeof(void*)*9 + 1);
v_precompileModules_462_ = lean_ctor_get_uint8(v_cfg_453_, sizeof(void*)*9 + 2);
v_defaultFacets_463_ = lean_ctor_get(v_cfg_453_, 7);
v_nativeFacets_464_ = lean_ctor_get(v_cfg_453_, 8);
v_allowImportAll_465_ = lean_ctor_get_uint8(v_cfg_453_, sizeof(void*)*9 + 3);
v_isSharedCheck_472_ = !lean_is_exclusive(v_cfg_453_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_cfg_453_, 5);
lean_dec(v_unused_473_);
v___x_467_ = v_cfg_453_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_nativeFacets_464_);
lean_inc(v_defaultFacets_463_);
lean_inc(v_extraDepTargets_460_);
lean_inc(v_libName_458_);
lean_inc(v_globs_457_);
lean_inc(v_roots_456_);
lean_inc(v_srcDir_455_);
lean_inc(v_toLeanConfig_454_);
lean_dec(v_cfg_453_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 5, v_val_452_);
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_toLeanConfig_454_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_srcDir_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_roots_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_globs_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_libName_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_val_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v_extraDepTargets_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_defaultFacets_463_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_nativeFacets_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*9, v_libPrefixOnWindows_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*9 + 1, v_precompileLibrary_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*9 + 2, v_precompileModules_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*9 + 3, v_allowImportAll_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__2(lean_object* v_f_474_, lean_object* v_cfg_475_){
_start:
{
lean_object* v_toLeanConfig_476_; lean_object* v_srcDir_477_; lean_object* v_roots_478_; lean_object* v_globs_479_; lean_object* v_libName_480_; uint8_t v_libPrefixOnWindows_481_; lean_object* v_needs_482_; lean_object* v_extraDepTargets_483_; uint8_t v_precompileLibrary_484_; uint8_t v_precompileModules_485_; lean_object* v_defaultFacets_486_; lean_object* v_nativeFacets_487_; uint8_t v_allowImportAll_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_toLeanConfig_476_ = lean_ctor_get(v_cfg_475_, 0);
v_srcDir_477_ = lean_ctor_get(v_cfg_475_, 1);
v_roots_478_ = lean_ctor_get(v_cfg_475_, 2);
v_globs_479_ = lean_ctor_get(v_cfg_475_, 3);
v_libName_480_ = lean_ctor_get(v_cfg_475_, 4);
v_libPrefixOnWindows_481_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9);
v_needs_482_ = lean_ctor_get(v_cfg_475_, 5);
v_extraDepTargets_483_ = lean_ctor_get(v_cfg_475_, 6);
v_precompileLibrary_484_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9 + 1);
v_precompileModules_485_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9 + 2);
v_defaultFacets_486_ = lean_ctor_get(v_cfg_475_, 7);
v_nativeFacets_487_ = lean_ctor_get(v_cfg_475_, 8);
v_allowImportAll_488_ = lean_ctor_get_uint8(v_cfg_475_, sizeof(void*)*9 + 3);
v_isSharedCheck_496_ = !lean_is_exclusive(v_cfg_475_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v_cfg_475_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_nativeFacets_487_);
lean_inc(v_defaultFacets_486_);
lean_inc(v_extraDepTargets_483_);
lean_inc(v_needs_482_);
lean_inc(v_libName_480_);
lean_inc(v_globs_479_);
lean_inc(v_roots_478_);
lean_inc(v_srcDir_477_);
lean_inc(v_toLeanConfig_476_);
lean_dec(v_cfg_475_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_apply_1(v_f_474_, v_needs_482_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 5, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_toLeanConfig_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_srcDir_477_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_roots_478_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_globs_479_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_libName_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 5, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 6, v_extraDepTargets_483_);
lean_ctor_set(v_reuseFailAlloc_495_, 7, v_defaultFacets_486_);
lean_ctor_set(v_reuseFailAlloc_495_, 8, v_nativeFacets_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*9, v_libPrefixOnWindows_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*9 + 1, v_precompileLibrary_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*9 + 2, v_precompileModules_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*9 + 3, v_allowImportAll_488_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__3(lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__3));
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___lam__3___boxed(lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lake_LeanLibConfig_needs___proj___redArg___lam__3(v_x_499_);
lean_dec_ref(v_x_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg(){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Lake_LeanLibConfig_needs___proj___redArg___closed__4));
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___redArg___boxed(lean_object* v___dummy_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_LeanLibConfig_needs___proj___redArg();
return v_res_513_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_needs___proj___closed__0(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lake_LeanLibConfig_needs___proj___redArg();
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object* v_name_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lake_LeanLibConfig_needs___proj___closed__0, &l_Lake_LeanLibConfig_needs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_needs___proj___closed__0);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs___proj___boxed(lean_object* v_name_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lake_LeanLibConfig_needs___proj(v_name_517_);
lean_dec(v_name_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___redArg(){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_Lake_LeanLibConfig_needs___proj___closed__0, &l_Lake_LeanLibConfig_needs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_needs___proj___closed__0);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___redArg___boxed(lean_object* v___dummy_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lake_LeanLibConfig_needs_instConfigField___redArg();
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField(lean_object* v_name_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Lake_LeanLibConfig_needs___proj___closed__0, &l_Lake_LeanLibConfig_needs___proj___closed__0_once, _init_l_Lake_LeanLibConfig_needs___proj___closed__0);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_needs_instConfigField___boxed(lean_object* v_name_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_525_);
lean_dec(v_name_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0(lean_object* v_cfg_527_){
_start:
{
lean_object* v_extraDepTargets_528_; 
v_extraDepTargets_528_ = lean_ctor_get(v_cfg_527_, 6);
lean_inc_ref(v_extraDepTargets_528_);
return v_extraDepTargets_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object* v_cfg_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__0(v_cfg_529_);
lean_dec_ref(v_cfg_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__1(lean_object* v_val_531_, lean_object* v_cfg_532_){
_start:
{
lean_object* v_toLeanConfig_533_; lean_object* v_srcDir_534_; lean_object* v_roots_535_; lean_object* v_globs_536_; lean_object* v_libName_537_; uint8_t v_libPrefixOnWindows_538_; lean_object* v_needs_539_; uint8_t v_precompileLibrary_540_; uint8_t v_precompileModules_541_; lean_object* v_defaultFacets_542_; lean_object* v_nativeFacets_543_; uint8_t v_allowImportAll_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_toLeanConfig_533_ = lean_ctor_get(v_cfg_532_, 0);
v_srcDir_534_ = lean_ctor_get(v_cfg_532_, 1);
v_roots_535_ = lean_ctor_get(v_cfg_532_, 2);
v_globs_536_ = lean_ctor_get(v_cfg_532_, 3);
v_libName_537_ = lean_ctor_get(v_cfg_532_, 4);
v_libPrefixOnWindows_538_ = lean_ctor_get_uint8(v_cfg_532_, sizeof(void*)*9);
v_needs_539_ = lean_ctor_get(v_cfg_532_, 5);
v_precompileLibrary_540_ = lean_ctor_get_uint8(v_cfg_532_, sizeof(void*)*9 + 1);
v_precompileModules_541_ = lean_ctor_get_uint8(v_cfg_532_, sizeof(void*)*9 + 2);
v_defaultFacets_542_ = lean_ctor_get(v_cfg_532_, 7);
v_nativeFacets_543_ = lean_ctor_get(v_cfg_532_, 8);
v_allowImportAll_544_ = lean_ctor_get_uint8(v_cfg_532_, sizeof(void*)*9 + 3);
v_isSharedCheck_551_ = !lean_is_exclusive(v_cfg_532_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_cfg_532_, 6);
lean_dec(v_unused_552_);
v___x_546_ = v_cfg_532_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_nativeFacets_543_);
lean_inc(v_defaultFacets_542_);
lean_inc(v_needs_539_);
lean_inc(v_libName_537_);
lean_inc(v_globs_536_);
lean_inc(v_roots_535_);
lean_inc(v_srcDir_534_);
lean_inc(v_toLeanConfig_533_);
lean_dec(v_cfg_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 6, v_val_531_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_toLeanConfig_533_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_srcDir_534_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_roots_535_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_globs_536_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_libName_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v_needs_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_val_531_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_defaultFacets_542_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_nativeFacets_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*9, v_libPrefixOnWindows_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*9 + 1, v_precompileLibrary_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*9 + 2, v_precompileModules_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*9 + 3, v_allowImportAll_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__2(lean_object* v_f_553_, lean_object* v_cfg_554_){
_start:
{
lean_object* v_toLeanConfig_555_; lean_object* v_srcDir_556_; lean_object* v_roots_557_; lean_object* v_globs_558_; lean_object* v_libName_559_; uint8_t v_libPrefixOnWindows_560_; lean_object* v_needs_561_; lean_object* v_extraDepTargets_562_; uint8_t v_precompileLibrary_563_; uint8_t v_precompileModules_564_; lean_object* v_defaultFacets_565_; lean_object* v_nativeFacets_566_; uint8_t v_allowImportAll_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_toLeanConfig_555_ = lean_ctor_get(v_cfg_554_, 0);
v_srcDir_556_ = lean_ctor_get(v_cfg_554_, 1);
v_roots_557_ = lean_ctor_get(v_cfg_554_, 2);
v_globs_558_ = lean_ctor_get(v_cfg_554_, 3);
v_libName_559_ = lean_ctor_get(v_cfg_554_, 4);
v_libPrefixOnWindows_560_ = lean_ctor_get_uint8(v_cfg_554_, sizeof(void*)*9);
v_needs_561_ = lean_ctor_get(v_cfg_554_, 5);
v_extraDepTargets_562_ = lean_ctor_get(v_cfg_554_, 6);
v_precompileLibrary_563_ = lean_ctor_get_uint8(v_cfg_554_, sizeof(void*)*9 + 1);
v_precompileModules_564_ = lean_ctor_get_uint8(v_cfg_554_, sizeof(void*)*9 + 2);
v_defaultFacets_565_ = lean_ctor_get(v_cfg_554_, 7);
v_nativeFacets_566_ = lean_ctor_get(v_cfg_554_, 8);
v_allowImportAll_567_ = lean_ctor_get_uint8(v_cfg_554_, sizeof(void*)*9 + 3);
v_isSharedCheck_575_ = !lean_is_exclusive(v_cfg_554_);
if (v_isSharedCheck_575_ == 0)
{
v___x_569_ = v_cfg_554_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_nativeFacets_566_);
lean_inc(v_defaultFacets_565_);
lean_inc(v_extraDepTargets_562_);
lean_inc(v_needs_561_);
lean_inc(v_libName_559_);
lean_inc(v_globs_558_);
lean_inc(v_roots_557_);
lean_inc(v_srcDir_556_);
lean_inc(v_toLeanConfig_555_);
lean_dec(v_cfg_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_apply_1(v_f_553_, v_extraDepTargets_562_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 6, v___x_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_toLeanConfig_555_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_srcDir_556_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_roots_557_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v_globs_558_);
lean_ctor_set(v_reuseFailAlloc_574_, 4, v_libName_559_);
lean_ctor_set(v_reuseFailAlloc_574_, 5, v_needs_561_);
lean_ctor_set(v_reuseFailAlloc_574_, 6, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 7, v_defaultFacets_565_);
lean_ctor_set(v_reuseFailAlloc_574_, 8, v_nativeFacets_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_574_, sizeof(void*)*9, v_libPrefixOnWindows_560_);
lean_ctor_set_uint8(v_reuseFailAlloc_574_, sizeof(void*)*9 + 1, v_precompileLibrary_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_574_, sizeof(void*)*9 + 2, v_precompileModules_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_574_, sizeof(void*)*9 + 3, v_allowImportAll_567_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3(lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___closed__0));
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object* v_x_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___lam__3(v_x_580_);
lean_dec_ref(v_x_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg(){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___closed__4));
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___redArg___boxed(lean_object* v___dummy_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg();
return v_res_594_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lake_LeanLibConfig_extraDepTargets___proj___redArg();
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object* v_name_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0, &l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(lean_object* v_name_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_598_);
lean_dec(v_name_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg(){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0, &l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object* v___dummy_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField___redArg();
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField(lean_object* v_name_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0, &l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(lean_object* v_name_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_606_);
lean_dec(v_name_606_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0(lean_object* v_cfg_608_){
_start:
{
uint8_t v_precompileLibrary_609_; 
v_precompileLibrary_609_ = lean_ctor_get_uint8(v_cfg_608_, sizeof(void*)*9 + 1);
return v_precompileLibrary_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0___boxed(lean_object* v_cfg_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__0(v_cfg_610_);
lean_dec_ref(v_cfg_610_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1(uint8_t v_val_613_, lean_object* v_cfg_614_){
_start:
{
lean_object* v_toLeanConfig_615_; lean_object* v_srcDir_616_; lean_object* v_roots_617_; lean_object* v_globs_618_; lean_object* v_libName_619_; uint8_t v_libPrefixOnWindows_620_; lean_object* v_needs_621_; lean_object* v_extraDepTargets_622_; uint8_t v_precompileModules_623_; lean_object* v_defaultFacets_624_; lean_object* v_nativeFacets_625_; uint8_t v_allowImportAll_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_toLeanConfig_615_ = lean_ctor_get(v_cfg_614_, 0);
v_srcDir_616_ = lean_ctor_get(v_cfg_614_, 1);
v_roots_617_ = lean_ctor_get(v_cfg_614_, 2);
v_globs_618_ = lean_ctor_get(v_cfg_614_, 3);
v_libName_619_ = lean_ctor_get(v_cfg_614_, 4);
v_libPrefixOnWindows_620_ = lean_ctor_get_uint8(v_cfg_614_, sizeof(void*)*9);
v_needs_621_ = lean_ctor_get(v_cfg_614_, 5);
v_extraDepTargets_622_ = lean_ctor_get(v_cfg_614_, 6);
v_precompileModules_623_ = lean_ctor_get_uint8(v_cfg_614_, sizeof(void*)*9 + 2);
v_defaultFacets_624_ = lean_ctor_get(v_cfg_614_, 7);
v_nativeFacets_625_ = lean_ctor_get(v_cfg_614_, 8);
v_allowImportAll_626_ = lean_ctor_get_uint8(v_cfg_614_, sizeof(void*)*9 + 3);
v_isSharedCheck_633_ = !lean_is_exclusive(v_cfg_614_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v_cfg_614_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_nativeFacets_625_);
lean_inc(v_defaultFacets_624_);
lean_inc(v_extraDepTargets_622_);
lean_inc(v_needs_621_);
lean_inc(v_libName_619_);
lean_inc(v_globs_618_);
lean_inc(v_roots_617_);
lean_inc(v_srcDir_616_);
lean_inc(v_toLeanConfig_615_);
lean_dec(v_cfg_614_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_toLeanConfig_615_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_srcDir_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_roots_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_globs_618_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_libName_619_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_needs_621_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_extraDepTargets_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_defaultFacets_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 8, v_nativeFacets_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*9, v_libPrefixOnWindows_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*9 + 2, v_precompileModules_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*9 + 3, v_allowImportAll_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*9 + 1, v_val_613_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1___boxed(lean_object* v_val_634_, lean_object* v_cfg_635_){
_start:
{
uint8_t v_val_75__boxed_636_; lean_object* v_res_637_; 
v_val_75__boxed_636_ = lean_unbox(v_val_634_);
v_res_637_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__1(v_val_75__boxed_636_, v_cfg_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___lam__2(lean_object* v_f_638_, lean_object* v_cfg_639_){
_start:
{
lean_object* v_toLeanConfig_640_; lean_object* v_srcDir_641_; lean_object* v_roots_642_; lean_object* v_globs_643_; lean_object* v_libName_644_; uint8_t v_libPrefixOnWindows_645_; lean_object* v_needs_646_; lean_object* v_extraDepTargets_647_; uint8_t v_precompileLibrary_648_; uint8_t v_precompileModules_649_; lean_object* v_defaultFacets_650_; lean_object* v_nativeFacets_651_; uint8_t v_allowImportAll_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_662_; 
v_toLeanConfig_640_ = lean_ctor_get(v_cfg_639_, 0);
v_srcDir_641_ = lean_ctor_get(v_cfg_639_, 1);
v_roots_642_ = lean_ctor_get(v_cfg_639_, 2);
v_globs_643_ = lean_ctor_get(v_cfg_639_, 3);
v_libName_644_ = lean_ctor_get(v_cfg_639_, 4);
v_libPrefixOnWindows_645_ = lean_ctor_get_uint8(v_cfg_639_, sizeof(void*)*9);
v_needs_646_ = lean_ctor_get(v_cfg_639_, 5);
v_extraDepTargets_647_ = lean_ctor_get(v_cfg_639_, 6);
v_precompileLibrary_648_ = lean_ctor_get_uint8(v_cfg_639_, sizeof(void*)*9 + 1);
v_precompileModules_649_ = lean_ctor_get_uint8(v_cfg_639_, sizeof(void*)*9 + 2);
v_defaultFacets_650_ = lean_ctor_get(v_cfg_639_, 7);
v_nativeFacets_651_ = lean_ctor_get(v_cfg_639_, 8);
v_allowImportAll_652_ = lean_ctor_get_uint8(v_cfg_639_, sizeof(void*)*9 + 3);
v_isSharedCheck_662_ = !lean_is_exclusive(v_cfg_639_);
if (v_isSharedCheck_662_ == 0)
{
v___x_654_ = v_cfg_639_;
v_isShared_655_ = v_isSharedCheck_662_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_nativeFacets_651_);
lean_inc(v_defaultFacets_650_);
lean_inc(v_extraDepTargets_647_);
lean_inc(v_needs_646_);
lean_inc(v_libName_644_);
lean_inc(v_globs_643_);
lean_inc(v_roots_642_);
lean_inc(v_srcDir_641_);
lean_inc(v_toLeanConfig_640_);
lean_dec(v_cfg_639_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_662_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = lean_box(v_precompileLibrary_648_);
v___x_657_ = lean_apply_1(v_f_638_, v___x_656_);
if (v_isShared_655_ == 0)
{
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_toLeanConfig_640_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_srcDir_641_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_roots_642_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_globs_643_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_libName_644_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v_needs_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 6, v_extraDepTargets_647_);
lean_ctor_set(v_reuseFailAlloc_661_, 7, v_defaultFacets_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 8, v_nativeFacets_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*9, v_libPrefixOnWindows_645_);
v___x_659_ = v_reuseFailAlloc_661_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
uint8_t v___x_660_; 
v___x_660_ = lean_unbox(v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*9 + 1, v___x_660_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*9 + 2, v_precompileModules_649_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*9 + 3, v_allowImportAll_652_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg(){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___closed__3));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___redArg___boxed(lean_object* v___dummy_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg();
return v_res_674_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lake_LeanLibConfig_precompileLibrary___proj___redArg();
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj(lean_object* v_name_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0, &l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary___proj___boxed(lean_object* v_name_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lake_LeanLibConfig_precompileLibrary___proj(v_name_678_);
lean_dec(v_name_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg(){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0, &l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg___boxed(lean_object* v___dummy_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lake_LeanLibConfig_precompileLibrary_instConfigField___redArg();
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField(lean_object* v_name_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0, &l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileLibrary___proj___closed__0);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileLibrary_instConfigField___boxed(lean_object* v_name_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lake_LeanLibConfig_precompileLibrary_instConfigField(v_name_686_);
lean_dec(v_name_686_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0(lean_object* v_cfg_688_){
_start:
{
uint8_t v_precompileModules_689_; 
v_precompileModules_689_ = lean_ctor_get_uint8(v_cfg_688_, sizeof(void*)*9 + 2);
return v_precompileModules_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object* v_cfg_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__0(v_cfg_690_);
lean_dec_ref(v_cfg_690_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1(uint8_t v_val_693_, lean_object* v_cfg_694_){
_start:
{
lean_object* v_toLeanConfig_695_; lean_object* v_srcDir_696_; lean_object* v_roots_697_; lean_object* v_globs_698_; lean_object* v_libName_699_; uint8_t v_libPrefixOnWindows_700_; lean_object* v_needs_701_; lean_object* v_extraDepTargets_702_; uint8_t v_precompileLibrary_703_; lean_object* v_defaultFacets_704_; lean_object* v_nativeFacets_705_; uint8_t v_allowImportAll_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_toLeanConfig_695_ = lean_ctor_get(v_cfg_694_, 0);
v_srcDir_696_ = lean_ctor_get(v_cfg_694_, 1);
v_roots_697_ = lean_ctor_get(v_cfg_694_, 2);
v_globs_698_ = lean_ctor_get(v_cfg_694_, 3);
v_libName_699_ = lean_ctor_get(v_cfg_694_, 4);
v_libPrefixOnWindows_700_ = lean_ctor_get_uint8(v_cfg_694_, sizeof(void*)*9);
v_needs_701_ = lean_ctor_get(v_cfg_694_, 5);
v_extraDepTargets_702_ = lean_ctor_get(v_cfg_694_, 6);
v_precompileLibrary_703_ = lean_ctor_get_uint8(v_cfg_694_, sizeof(void*)*9 + 1);
v_defaultFacets_704_ = lean_ctor_get(v_cfg_694_, 7);
v_nativeFacets_705_ = lean_ctor_get(v_cfg_694_, 8);
v_allowImportAll_706_ = lean_ctor_get_uint8(v_cfg_694_, sizeof(void*)*9 + 3);
v_isSharedCheck_713_ = !lean_is_exclusive(v_cfg_694_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v_cfg_694_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_nativeFacets_705_);
lean_inc(v_defaultFacets_704_);
lean_inc(v_extraDepTargets_702_);
lean_inc(v_needs_701_);
lean_inc(v_libName_699_);
lean_inc(v_globs_698_);
lean_inc(v_roots_697_);
lean_inc(v_srcDir_696_);
lean_inc(v_toLeanConfig_695_);
lean_dec(v_cfg_694_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_toLeanConfig_695_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_srcDir_696_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_roots_697_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_globs_698_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_libName_699_);
lean_ctor_set(v_reuseFailAlloc_712_, 5, v_needs_701_);
lean_ctor_set(v_reuseFailAlloc_712_, 6, v_extraDepTargets_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 7, v_defaultFacets_704_);
lean_ctor_set(v_reuseFailAlloc_712_, 8, v_nativeFacets_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*9, v_libPrefixOnWindows_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*9 + 1, v_precompileLibrary_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*9 + 3, v_allowImportAll_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*9 + 2, v_val_693_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object* v_val_714_, lean_object* v_cfg_715_){
_start:
{
uint8_t v_val_75__boxed_716_; lean_object* v_res_717_; 
v_val_75__boxed_716_ = lean_unbox(v_val_714_);
v_res_717_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__1(v_val_75__boxed_716_, v_cfg_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___lam__2(lean_object* v_f_718_, lean_object* v_cfg_719_){
_start:
{
lean_object* v_toLeanConfig_720_; lean_object* v_srcDir_721_; lean_object* v_roots_722_; lean_object* v_globs_723_; lean_object* v_libName_724_; uint8_t v_libPrefixOnWindows_725_; lean_object* v_needs_726_; lean_object* v_extraDepTargets_727_; uint8_t v_precompileLibrary_728_; uint8_t v_precompileModules_729_; lean_object* v_defaultFacets_730_; lean_object* v_nativeFacets_731_; uint8_t v_allowImportAll_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_742_; 
v_toLeanConfig_720_ = lean_ctor_get(v_cfg_719_, 0);
v_srcDir_721_ = lean_ctor_get(v_cfg_719_, 1);
v_roots_722_ = lean_ctor_get(v_cfg_719_, 2);
v_globs_723_ = lean_ctor_get(v_cfg_719_, 3);
v_libName_724_ = lean_ctor_get(v_cfg_719_, 4);
v_libPrefixOnWindows_725_ = lean_ctor_get_uint8(v_cfg_719_, sizeof(void*)*9);
v_needs_726_ = lean_ctor_get(v_cfg_719_, 5);
v_extraDepTargets_727_ = lean_ctor_get(v_cfg_719_, 6);
v_precompileLibrary_728_ = lean_ctor_get_uint8(v_cfg_719_, sizeof(void*)*9 + 1);
v_precompileModules_729_ = lean_ctor_get_uint8(v_cfg_719_, sizeof(void*)*9 + 2);
v_defaultFacets_730_ = lean_ctor_get(v_cfg_719_, 7);
v_nativeFacets_731_ = lean_ctor_get(v_cfg_719_, 8);
v_allowImportAll_732_ = lean_ctor_get_uint8(v_cfg_719_, sizeof(void*)*9 + 3);
v_isSharedCheck_742_ = !lean_is_exclusive(v_cfg_719_);
if (v_isSharedCheck_742_ == 0)
{
v___x_734_ = v_cfg_719_;
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_nativeFacets_731_);
lean_inc(v_defaultFacets_730_);
lean_inc(v_extraDepTargets_727_);
lean_inc(v_needs_726_);
lean_inc(v_libName_724_);
lean_inc(v_globs_723_);
lean_inc(v_roots_722_);
lean_inc(v_srcDir_721_);
lean_inc(v_toLeanConfig_720_);
lean_dec(v_cfg_719_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_736_ = lean_box(v_precompileModules_729_);
v___x_737_ = lean_apply_1(v_f_718_, v___x_736_);
if (v_isShared_735_ == 0)
{
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_toLeanConfig_720_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_srcDir_721_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_roots_722_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_globs_723_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_libName_724_);
lean_ctor_set(v_reuseFailAlloc_741_, 5, v_needs_726_);
lean_ctor_set(v_reuseFailAlloc_741_, 6, v_extraDepTargets_727_);
lean_ctor_set(v_reuseFailAlloc_741_, 7, v_defaultFacets_730_);
lean_ctor_set(v_reuseFailAlloc_741_, 8, v_nativeFacets_731_);
lean_ctor_set_uint8(v_reuseFailAlloc_741_, sizeof(void*)*9, v_libPrefixOnWindows_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_741_, sizeof(void*)*9 + 1, v_precompileLibrary_728_);
v___x_739_ = v_reuseFailAlloc_741_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
uint8_t v___x_740_; 
v___x_740_ = lean_unbox(v___x_737_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*9 + 2, v___x_740_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*9 + 3, v_allowImportAll_732_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg(){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = ((lean_object*)(l_Lake_LeanLibConfig_precompileModules___proj___redArg___closed__3));
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___redArg___boxed(lean_object* v___dummy_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg();
return v_res_754_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lake_LeanLibConfig_precompileModules___proj___redArg();
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object* v_name_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileModules___proj___closed__0, &l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules___proj___boxed(lean_object* v_name_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_758_);
lean_dec(v_name_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg(){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileModules___proj___closed__0, &l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg___boxed(lean_object* v___dummy_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_LeanLibConfig_precompileModules_instConfigField___redArg();
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField(lean_object* v_name_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_obj_once(&l_Lake_LeanLibConfig_precompileModules___proj___closed__0, &l_Lake_LeanLibConfig_precompileModules___proj___closed__0_once, _init_l_Lake_LeanLibConfig_precompileModules___proj___closed__0);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(lean_object* v_name_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_766_);
lean_dec(v_name_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0(lean_object* v_cfg_768_){
_start:
{
lean_object* v_defaultFacets_769_; 
v_defaultFacets_769_ = lean_ctor_get(v_cfg_768_, 7);
lean_inc_ref(v_defaultFacets_769_);
return v_defaultFacets_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0___boxed(lean_object* v_cfg_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__0(v_cfg_770_);
lean_dec_ref(v_cfg_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__1(lean_object* v_val_772_, lean_object* v_cfg_773_){
_start:
{
lean_object* v_toLeanConfig_774_; lean_object* v_srcDir_775_; lean_object* v_roots_776_; lean_object* v_globs_777_; lean_object* v_libName_778_; uint8_t v_libPrefixOnWindows_779_; lean_object* v_needs_780_; lean_object* v_extraDepTargets_781_; uint8_t v_precompileLibrary_782_; uint8_t v_precompileModules_783_; lean_object* v_nativeFacets_784_; uint8_t v_allowImportAll_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_toLeanConfig_774_ = lean_ctor_get(v_cfg_773_, 0);
v_srcDir_775_ = lean_ctor_get(v_cfg_773_, 1);
v_roots_776_ = lean_ctor_get(v_cfg_773_, 2);
v_globs_777_ = lean_ctor_get(v_cfg_773_, 3);
v_libName_778_ = lean_ctor_get(v_cfg_773_, 4);
v_libPrefixOnWindows_779_ = lean_ctor_get_uint8(v_cfg_773_, sizeof(void*)*9);
v_needs_780_ = lean_ctor_get(v_cfg_773_, 5);
v_extraDepTargets_781_ = lean_ctor_get(v_cfg_773_, 6);
v_precompileLibrary_782_ = lean_ctor_get_uint8(v_cfg_773_, sizeof(void*)*9 + 1);
v_precompileModules_783_ = lean_ctor_get_uint8(v_cfg_773_, sizeof(void*)*9 + 2);
v_nativeFacets_784_ = lean_ctor_get(v_cfg_773_, 8);
v_allowImportAll_785_ = lean_ctor_get_uint8(v_cfg_773_, sizeof(void*)*9 + 3);
v_isSharedCheck_792_ = !lean_is_exclusive(v_cfg_773_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_cfg_773_, 7);
lean_dec(v_unused_793_);
v___x_787_ = v_cfg_773_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_nativeFacets_784_);
lean_inc(v_extraDepTargets_781_);
lean_inc(v_needs_780_);
lean_inc(v_libName_778_);
lean_inc(v_globs_777_);
lean_inc(v_roots_776_);
lean_inc(v_srcDir_775_);
lean_inc(v_toLeanConfig_774_);
lean_dec(v_cfg_773_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 7, v_val_772_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_toLeanConfig_774_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_srcDir_775_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_roots_776_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_globs_777_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_libName_778_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v_needs_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_extraDepTargets_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v_val_772_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_nativeFacets_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*9, v_libPrefixOnWindows_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*9 + 1, v_precompileLibrary_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*9 + 2, v_precompileModules_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*9 + 3, v_allowImportAll_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__2(lean_object* v_f_794_, lean_object* v_cfg_795_){
_start:
{
lean_object* v_toLeanConfig_796_; lean_object* v_srcDir_797_; lean_object* v_roots_798_; lean_object* v_globs_799_; lean_object* v_libName_800_; uint8_t v_libPrefixOnWindows_801_; lean_object* v_needs_802_; lean_object* v_extraDepTargets_803_; uint8_t v_precompileLibrary_804_; uint8_t v_precompileModules_805_; lean_object* v_defaultFacets_806_; lean_object* v_nativeFacets_807_; uint8_t v_allowImportAll_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_816_; 
v_toLeanConfig_796_ = lean_ctor_get(v_cfg_795_, 0);
v_srcDir_797_ = lean_ctor_get(v_cfg_795_, 1);
v_roots_798_ = lean_ctor_get(v_cfg_795_, 2);
v_globs_799_ = lean_ctor_get(v_cfg_795_, 3);
v_libName_800_ = lean_ctor_get(v_cfg_795_, 4);
v_libPrefixOnWindows_801_ = lean_ctor_get_uint8(v_cfg_795_, sizeof(void*)*9);
v_needs_802_ = lean_ctor_get(v_cfg_795_, 5);
v_extraDepTargets_803_ = lean_ctor_get(v_cfg_795_, 6);
v_precompileLibrary_804_ = lean_ctor_get_uint8(v_cfg_795_, sizeof(void*)*9 + 1);
v_precompileModules_805_ = lean_ctor_get_uint8(v_cfg_795_, sizeof(void*)*9 + 2);
v_defaultFacets_806_ = lean_ctor_get(v_cfg_795_, 7);
v_nativeFacets_807_ = lean_ctor_get(v_cfg_795_, 8);
v_allowImportAll_808_ = lean_ctor_get_uint8(v_cfg_795_, sizeof(void*)*9 + 3);
v_isSharedCheck_816_ = !lean_is_exclusive(v_cfg_795_);
if (v_isSharedCheck_816_ == 0)
{
v___x_810_ = v_cfg_795_;
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_nativeFacets_807_);
lean_inc(v_defaultFacets_806_);
lean_inc(v_extraDepTargets_803_);
lean_inc(v_needs_802_);
lean_inc(v_libName_800_);
lean_inc(v_globs_799_);
lean_inc(v_roots_798_);
lean_inc(v_srcDir_797_);
lean_inc(v_toLeanConfig_796_);
lean_dec(v_cfg_795_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_apply_1(v_f_794_, v_defaultFacets_806_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 7, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_toLeanConfig_796_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_srcDir_797_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_roots_798_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_globs_799_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_libName_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 5, v_needs_802_);
lean_ctor_set(v_reuseFailAlloc_815_, 6, v_extraDepTargets_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 7, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_815_, 8, v_nativeFacets_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_815_, sizeof(void*)*9, v_libPrefixOnWindows_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_815_, sizeof(void*)*9 + 1, v_precompileLibrary_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_815_, sizeof(void*)*9 + 2, v_precompileModules_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_815_, sizeof(void*)*9 + 3, v_allowImportAll_808_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3(lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_818_);
lean_dec_ref(v___x_819_);
v___x_820_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3___boxed(lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg___lam__3(v_x_821_);
lean_dec_ref(v_x_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg(){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = ((lean_object*)(l_Lake_LeanLibConfig_defaultFacets___proj___redArg___closed__4));
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___redArg___boxed(lean_object* v___dummy_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg();
return v_res_835_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lake_LeanLibConfig_defaultFacets___proj___redArg();
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object* v_name_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets___proj___boxed(lean_object* v_name_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_839_);
lean_dec(v_name_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg(){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg___boxed(lean_object* v___dummy_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField___redArg();
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField(lean_object* v_name_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_Lake_LeanLibConfig_defaultFacets___proj___closed__0, &l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_defaultFacets___proj___closed__0);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(lean_object* v_name_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_847_);
lean_dec(v_name_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0(lean_object* v_cfg_849_, uint8_t v___y_850_){
_start:
{
lean_object* v_nativeFacets_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_nativeFacets_851_ = lean_ctor_get(v_cfg_849_, 8);
lean_inc_ref(v_nativeFacets_851_);
lean_dec_ref(v_cfg_849_);
v___x_852_ = lean_box(v___y_850_);
v___x_853_ = lean_apply_1(v_nativeFacets_851_, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0___boxed(lean_object* v_cfg_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___y_130__boxed_856_; lean_object* v_res_857_; 
v___y_130__boxed_856_ = lean_unbox(v___y_855_);
v_res_857_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__0(v_cfg_854_, v___y_130__boxed_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__1(lean_object* v_val_858_, lean_object* v_cfg_859_){
_start:
{
lean_object* v_toLeanConfig_860_; lean_object* v_srcDir_861_; lean_object* v_roots_862_; lean_object* v_globs_863_; lean_object* v_libName_864_; uint8_t v_libPrefixOnWindows_865_; lean_object* v_needs_866_; lean_object* v_extraDepTargets_867_; uint8_t v_precompileLibrary_868_; uint8_t v_precompileModules_869_; lean_object* v_defaultFacets_870_; uint8_t v_allowImportAll_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_toLeanConfig_860_ = lean_ctor_get(v_cfg_859_, 0);
v_srcDir_861_ = lean_ctor_get(v_cfg_859_, 1);
v_roots_862_ = lean_ctor_get(v_cfg_859_, 2);
v_globs_863_ = lean_ctor_get(v_cfg_859_, 3);
v_libName_864_ = lean_ctor_get(v_cfg_859_, 4);
v_libPrefixOnWindows_865_ = lean_ctor_get_uint8(v_cfg_859_, sizeof(void*)*9);
v_needs_866_ = lean_ctor_get(v_cfg_859_, 5);
v_extraDepTargets_867_ = lean_ctor_get(v_cfg_859_, 6);
v_precompileLibrary_868_ = lean_ctor_get_uint8(v_cfg_859_, sizeof(void*)*9 + 1);
v_precompileModules_869_ = lean_ctor_get_uint8(v_cfg_859_, sizeof(void*)*9 + 2);
v_defaultFacets_870_ = lean_ctor_get(v_cfg_859_, 7);
v_allowImportAll_871_ = lean_ctor_get_uint8(v_cfg_859_, sizeof(void*)*9 + 3);
v_isSharedCheck_878_ = !lean_is_exclusive(v_cfg_859_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_cfg_859_, 8);
lean_dec(v_unused_879_);
v___x_873_ = v_cfg_859_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_defaultFacets_870_);
lean_inc(v_extraDepTargets_867_);
lean_inc(v_needs_866_);
lean_inc(v_libName_864_);
lean_inc(v_globs_863_);
lean_inc(v_roots_862_);
lean_inc(v_srcDir_861_);
lean_inc(v_toLeanConfig_860_);
lean_dec(v_cfg_859_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 8, v_val_858_);
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_toLeanConfig_860_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_srcDir_861_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_roots_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_globs_863_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_libName_864_);
lean_ctor_set(v_reuseFailAlloc_877_, 5, v_needs_866_);
lean_ctor_set(v_reuseFailAlloc_877_, 6, v_extraDepTargets_867_);
lean_ctor_set(v_reuseFailAlloc_877_, 7, v_defaultFacets_870_);
lean_ctor_set(v_reuseFailAlloc_877_, 8, v_val_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*9, v_libPrefixOnWindows_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*9 + 1, v_precompileLibrary_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*9 + 2, v_precompileModules_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*9 + 3, v_allowImportAll_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__2(lean_object* v_f_880_, lean_object* v_cfg_881_){
_start:
{
lean_object* v_toLeanConfig_882_; lean_object* v_srcDir_883_; lean_object* v_roots_884_; lean_object* v_globs_885_; lean_object* v_libName_886_; uint8_t v_libPrefixOnWindows_887_; lean_object* v_needs_888_; lean_object* v_extraDepTargets_889_; uint8_t v_precompileLibrary_890_; uint8_t v_precompileModules_891_; lean_object* v_defaultFacets_892_; lean_object* v_nativeFacets_893_; uint8_t v_allowImportAll_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_902_; 
v_toLeanConfig_882_ = lean_ctor_get(v_cfg_881_, 0);
v_srcDir_883_ = lean_ctor_get(v_cfg_881_, 1);
v_roots_884_ = lean_ctor_get(v_cfg_881_, 2);
v_globs_885_ = lean_ctor_get(v_cfg_881_, 3);
v_libName_886_ = lean_ctor_get(v_cfg_881_, 4);
v_libPrefixOnWindows_887_ = lean_ctor_get_uint8(v_cfg_881_, sizeof(void*)*9);
v_needs_888_ = lean_ctor_get(v_cfg_881_, 5);
v_extraDepTargets_889_ = lean_ctor_get(v_cfg_881_, 6);
v_precompileLibrary_890_ = lean_ctor_get_uint8(v_cfg_881_, sizeof(void*)*9 + 1);
v_precompileModules_891_ = lean_ctor_get_uint8(v_cfg_881_, sizeof(void*)*9 + 2);
v_defaultFacets_892_ = lean_ctor_get(v_cfg_881_, 7);
v_nativeFacets_893_ = lean_ctor_get(v_cfg_881_, 8);
v_allowImportAll_894_ = lean_ctor_get_uint8(v_cfg_881_, sizeof(void*)*9 + 3);
v_isSharedCheck_902_ = !lean_is_exclusive(v_cfg_881_);
if (v_isSharedCheck_902_ == 0)
{
v___x_896_ = v_cfg_881_;
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_nativeFacets_893_);
lean_inc(v_defaultFacets_892_);
lean_inc(v_extraDepTargets_889_);
lean_inc(v_needs_888_);
lean_inc(v_libName_886_);
lean_inc(v_globs_885_);
lean_inc(v_roots_884_);
lean_inc(v_srcDir_883_);
lean_inc(v_toLeanConfig_882_);
lean_dec(v_cfg_881_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_apply_1(v_f_880_, v_nativeFacets_893_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 8, v___x_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_toLeanConfig_882_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_srcDir_883_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_roots_884_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_globs_885_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_libName_886_);
lean_ctor_set(v_reuseFailAlloc_901_, 5, v_needs_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 6, v_extraDepTargets_889_);
lean_ctor_set(v_reuseFailAlloc_901_, 7, v_defaultFacets_892_);
lean_ctor_set(v_reuseFailAlloc_901_, 8, v___x_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*9, v_libPrefixOnWindows_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*9 + 1, v_precompileLibrary_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*9 + 2, v_precompileModules_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*9 + 3, v_allowImportAll_894_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3(lean_object* v_x_903_, uint8_t v___y_904_){
_start:
{
lean_object* v___y_906_; 
if (v___y_904_ == 0)
{
lean_object* v___x_910_; 
v___x_910_ = l_Lake_Module_oFacet;
v___y_906_ = v___x_910_;
goto v___jp_905_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = l_Lake_Module_oExportFacet;
v___y_906_ = v___x_911_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_mk_empty_array_with_capacity(v___x_907_);
lean_inc(v___y_906_);
v___x_909_ = lean_array_push(v___x_908_, v___y_906_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3___boxed(lean_object* v_x_912_, lean_object* v___y_913_){
_start:
{
uint8_t v___y_180__boxed_914_; lean_object* v_res_915_; 
v___y_180__boxed_914_ = lean_unbox(v___y_913_);
v_res_915_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg___lam__3(v_x_912_, v___y_180__boxed_914_);
lean_dec_ref(v_x_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg(){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = ((lean_object*)(l_Lake_LeanLibConfig_nativeFacets___proj___redArg___closed__4));
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___redArg___boxed(lean_object* v___dummy_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg();
return v_res_928_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lake_LeanLibConfig_nativeFacets___proj___redArg();
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj(lean_object* v_name_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_obj_once(&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0, &l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets___proj___boxed(lean_object* v_name_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_932_);
lean_dec(v_name_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg(){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_obj_once(&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0, &l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg___boxed(lean_object* v___dummy_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField___redArg();
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField(lean_object* v_name_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_obj_once(&l_Lake_LeanLibConfig_nativeFacets___proj___closed__0, &l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_once, _init_l_Lake_LeanLibConfig_nativeFacets___proj___closed__0);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(lean_object* v_name_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_940_);
lean_dec(v_name_940_);
return v_res_941_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0(lean_object* v_cfg_942_){
_start:
{
uint8_t v_allowImportAll_943_; 
v_allowImportAll_943_ = lean_ctor_get_uint8(v_cfg_942_, sizeof(void*)*9 + 3);
return v_allowImportAll_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object* v_cfg_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__0(v_cfg_944_);
lean_dec_ref(v_cfg_944_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1(uint8_t v_val_947_, lean_object* v_cfg_948_){
_start:
{
lean_object* v_toLeanConfig_949_; lean_object* v_srcDir_950_; lean_object* v_roots_951_; lean_object* v_globs_952_; lean_object* v_libName_953_; uint8_t v_libPrefixOnWindows_954_; lean_object* v_needs_955_; lean_object* v_extraDepTargets_956_; uint8_t v_precompileLibrary_957_; uint8_t v_precompileModules_958_; lean_object* v_defaultFacets_959_; lean_object* v_nativeFacets_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_toLeanConfig_949_ = lean_ctor_get(v_cfg_948_, 0);
v_srcDir_950_ = lean_ctor_get(v_cfg_948_, 1);
v_roots_951_ = lean_ctor_get(v_cfg_948_, 2);
v_globs_952_ = lean_ctor_get(v_cfg_948_, 3);
v_libName_953_ = lean_ctor_get(v_cfg_948_, 4);
v_libPrefixOnWindows_954_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*9);
v_needs_955_ = lean_ctor_get(v_cfg_948_, 5);
v_extraDepTargets_956_ = lean_ctor_get(v_cfg_948_, 6);
v_precompileLibrary_957_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*9 + 1);
v_precompileModules_958_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*9 + 2);
v_defaultFacets_959_ = lean_ctor_get(v_cfg_948_, 7);
v_nativeFacets_960_ = lean_ctor_get(v_cfg_948_, 8);
v_isSharedCheck_967_ = !lean_is_exclusive(v_cfg_948_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v_cfg_948_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_nativeFacets_960_);
lean_inc(v_defaultFacets_959_);
lean_inc(v_extraDepTargets_956_);
lean_inc(v_needs_955_);
lean_inc(v_libName_953_);
lean_inc(v_globs_952_);
lean_inc(v_roots_951_);
lean_inc(v_srcDir_950_);
lean_inc(v_toLeanConfig_949_);
lean_dec(v_cfg_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_toLeanConfig_949_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_srcDir_950_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_roots_951_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_globs_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_libName_953_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_needs_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 6, v_extraDepTargets_956_);
lean_ctor_set(v_reuseFailAlloc_966_, 7, v_defaultFacets_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 8, v_nativeFacets_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*9, v_libPrefixOnWindows_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*9 + 1, v_precompileLibrary_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*9 + 2, v_precompileModules_958_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*9 + 3, v_val_947_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object* v_val_968_, lean_object* v_cfg_969_){
_start:
{
uint8_t v_val_75__boxed_970_; lean_object* v_res_971_; 
v_val_75__boxed_970_ = lean_unbox(v_val_968_);
v_res_971_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__1(v_val_75__boxed_970_, v_cfg_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___lam__2(lean_object* v_f_972_, lean_object* v_cfg_973_){
_start:
{
lean_object* v_toLeanConfig_974_; lean_object* v_srcDir_975_; lean_object* v_roots_976_; lean_object* v_globs_977_; lean_object* v_libName_978_; uint8_t v_libPrefixOnWindows_979_; lean_object* v_needs_980_; lean_object* v_extraDepTargets_981_; uint8_t v_precompileLibrary_982_; uint8_t v_precompileModules_983_; lean_object* v_defaultFacets_984_; lean_object* v_nativeFacets_985_; uint8_t v_allowImportAll_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_996_; 
v_toLeanConfig_974_ = lean_ctor_get(v_cfg_973_, 0);
v_srcDir_975_ = lean_ctor_get(v_cfg_973_, 1);
v_roots_976_ = lean_ctor_get(v_cfg_973_, 2);
v_globs_977_ = lean_ctor_get(v_cfg_973_, 3);
v_libName_978_ = lean_ctor_get(v_cfg_973_, 4);
v_libPrefixOnWindows_979_ = lean_ctor_get_uint8(v_cfg_973_, sizeof(void*)*9);
v_needs_980_ = lean_ctor_get(v_cfg_973_, 5);
v_extraDepTargets_981_ = lean_ctor_get(v_cfg_973_, 6);
v_precompileLibrary_982_ = lean_ctor_get_uint8(v_cfg_973_, sizeof(void*)*9 + 1);
v_precompileModules_983_ = lean_ctor_get_uint8(v_cfg_973_, sizeof(void*)*9 + 2);
v_defaultFacets_984_ = lean_ctor_get(v_cfg_973_, 7);
v_nativeFacets_985_ = lean_ctor_get(v_cfg_973_, 8);
v_allowImportAll_986_ = lean_ctor_get_uint8(v_cfg_973_, sizeof(void*)*9 + 3);
v_isSharedCheck_996_ = !lean_is_exclusive(v_cfg_973_);
if (v_isSharedCheck_996_ == 0)
{
v___x_988_ = v_cfg_973_;
v_isShared_989_ = v_isSharedCheck_996_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_nativeFacets_985_);
lean_inc(v_defaultFacets_984_);
lean_inc(v_extraDepTargets_981_);
lean_inc(v_needs_980_);
lean_inc(v_libName_978_);
lean_inc(v_globs_977_);
lean_inc(v_roots_976_);
lean_inc(v_srcDir_975_);
lean_inc(v_toLeanConfig_974_);
lean_dec(v_cfg_973_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_996_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = lean_box(v_allowImportAll_986_);
v___x_991_ = lean_apply_1(v_f_972_, v___x_990_);
if (v_isShared_989_ == 0)
{
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_toLeanConfig_974_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_srcDir_975_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_roots_976_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_globs_977_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_libName_978_);
lean_ctor_set(v_reuseFailAlloc_995_, 5, v_needs_980_);
lean_ctor_set(v_reuseFailAlloc_995_, 6, v_extraDepTargets_981_);
lean_ctor_set(v_reuseFailAlloc_995_, 7, v_defaultFacets_984_);
lean_ctor_set(v_reuseFailAlloc_995_, 8, v_nativeFacets_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_995_, sizeof(void*)*9, v_libPrefixOnWindows_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_995_, sizeof(void*)*9 + 1, v_precompileLibrary_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_995_, sizeof(void*)*9 + 2, v_precompileModules_983_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_unbox(v___x_991_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*9 + 3, v___x_994_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg(){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Lake_LeanLibConfig_allowImportAll___proj___redArg___closed__3));
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___redArg___boxed(lean_object* v___dummy_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg();
return v_res_1008_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lake_LeanLibConfig_allowImportAll___proj___redArg();
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object* v_name_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_obj_once(&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0, &l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll___proj___boxed(lean_object* v_name_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_1012_);
lean_dec(v_name_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg(){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_obj_once(&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0, &l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg___boxed(lean_object* v___dummy_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField___redArg();
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField(lean_object* v_name_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_once(&l_Lake_LeanLibConfig_allowImportAll___proj___closed__0, &l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_LeanLibConfig_allowImportAll___proj___closed__0);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(lean_object* v_name_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_1020_);
lean_dec(v_name_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0(lean_object* v_cfg_1022_){
_start:
{
lean_object* v_toLeanConfig_1023_; 
v_toLeanConfig_1023_ = lean_ctor_get(v_cfg_1022_, 0);
lean_inc_ref(v_toLeanConfig_1023_);
return v_toLeanConfig_1023_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__0(v_cfg_1024_);
lean_dec_ref(v_cfg_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__1(lean_object* v_val_1026_, lean_object* v_cfg_1027_){
_start:
{
lean_object* v_srcDir_1028_; lean_object* v_roots_1029_; lean_object* v_globs_1030_; lean_object* v_libName_1031_; uint8_t v_libPrefixOnWindows_1032_; lean_object* v_needs_1033_; lean_object* v_extraDepTargets_1034_; uint8_t v_precompileLibrary_1035_; uint8_t v_precompileModules_1036_; lean_object* v_defaultFacets_1037_; lean_object* v_nativeFacets_1038_; uint8_t v_allowImportAll_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_srcDir_1028_ = lean_ctor_get(v_cfg_1027_, 1);
v_roots_1029_ = lean_ctor_get(v_cfg_1027_, 2);
v_globs_1030_ = lean_ctor_get(v_cfg_1027_, 3);
v_libName_1031_ = lean_ctor_get(v_cfg_1027_, 4);
v_libPrefixOnWindows_1032_ = lean_ctor_get_uint8(v_cfg_1027_, sizeof(void*)*9);
v_needs_1033_ = lean_ctor_get(v_cfg_1027_, 5);
v_extraDepTargets_1034_ = lean_ctor_get(v_cfg_1027_, 6);
v_precompileLibrary_1035_ = lean_ctor_get_uint8(v_cfg_1027_, sizeof(void*)*9 + 1);
v_precompileModules_1036_ = lean_ctor_get_uint8(v_cfg_1027_, sizeof(void*)*9 + 2);
v_defaultFacets_1037_ = lean_ctor_get(v_cfg_1027_, 7);
v_nativeFacets_1038_ = lean_ctor_get(v_cfg_1027_, 8);
v_allowImportAll_1039_ = lean_ctor_get_uint8(v_cfg_1027_, sizeof(void*)*9 + 3);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_cfg_1027_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_cfg_1027_, 0);
lean_dec(v_unused_1047_);
v___x_1041_ = v_cfg_1027_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_nativeFacets_1038_);
lean_inc(v_defaultFacets_1037_);
lean_inc(v_extraDepTargets_1034_);
lean_inc(v_needs_1033_);
lean_inc(v_libName_1031_);
lean_inc(v_globs_1030_);
lean_inc(v_roots_1029_);
lean_inc(v_srcDir_1028_);
lean_dec(v_cfg_1027_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_val_1026_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_val_1026_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_srcDir_1028_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_roots_1029_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_globs_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_libName_1031_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_needs_1033_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_extraDepTargets_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_defaultFacets_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_nativeFacets_1038_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*9, v_libPrefixOnWindows_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*9 + 1, v_precompileLibrary_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*9 + 2, v_precompileModules_1036_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*9 + 3, v_allowImportAll_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__2(lean_object* v_f_1048_, lean_object* v_cfg_1049_){
_start:
{
lean_object* v_toLeanConfig_1050_; lean_object* v_srcDir_1051_; lean_object* v_roots_1052_; lean_object* v_globs_1053_; lean_object* v_libName_1054_; uint8_t v_libPrefixOnWindows_1055_; lean_object* v_needs_1056_; lean_object* v_extraDepTargets_1057_; uint8_t v_precompileLibrary_1058_; uint8_t v_precompileModules_1059_; lean_object* v_defaultFacets_1060_; lean_object* v_nativeFacets_1061_; uint8_t v_allowImportAll_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_toLeanConfig_1050_ = lean_ctor_get(v_cfg_1049_, 0);
v_srcDir_1051_ = lean_ctor_get(v_cfg_1049_, 1);
v_roots_1052_ = lean_ctor_get(v_cfg_1049_, 2);
v_globs_1053_ = lean_ctor_get(v_cfg_1049_, 3);
v_libName_1054_ = lean_ctor_get(v_cfg_1049_, 4);
v_libPrefixOnWindows_1055_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*9);
v_needs_1056_ = lean_ctor_get(v_cfg_1049_, 5);
v_extraDepTargets_1057_ = lean_ctor_get(v_cfg_1049_, 6);
v_precompileLibrary_1058_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*9 + 1);
v_precompileModules_1059_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*9 + 2);
v_defaultFacets_1060_ = lean_ctor_get(v_cfg_1049_, 7);
v_nativeFacets_1061_ = lean_ctor_get(v_cfg_1049_, 8);
v_allowImportAll_1062_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*9 + 3);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_cfg_1049_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1064_ = v_cfg_1049_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_nativeFacets_1061_);
lean_inc(v_defaultFacets_1060_);
lean_inc(v_extraDepTargets_1057_);
lean_inc(v_needs_1056_);
lean_inc(v_libName_1054_);
lean_inc(v_globs_1053_);
lean_inc(v_roots_1052_);
lean_inc(v_srcDir_1051_);
lean_inc(v_toLeanConfig_1050_);
lean_dec(v_cfg_1049_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_apply_1(v_f_1048_, v_toLeanConfig_1050_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_srcDir_1051_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_roots_1052_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_globs_1053_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_libName_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_needs_1056_);
lean_ctor_set(v_reuseFailAlloc_1069_, 6, v_extraDepTargets_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 7, v_defaultFacets_1060_);
lean_ctor_set(v_reuseFailAlloc_1069_, 8, v_nativeFacets_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*9, v_libPrefixOnWindows_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*9 + 1, v_precompileLibrary_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*9 + 2, v_precompileModules_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*9 + 3, v_allowImportAll_1062_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3(lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object* v_x_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3(v_x_1081_);
lean_dec_ref(v_x_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg(){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___closed__4));
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___boxed(lean_object* v___dummy_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg();
return v_res_1095_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lake_LeanLibConfig_toLeanConfig___proj___redArg();
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object* v_name_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_obj_once(&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0, &l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(lean_object* v_name_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_1099_);
lean_dec(v_name_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_obj_once(&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0, &l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___redArg();
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(lean_object* v_name_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0, &l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_name_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(v_name_1107_);
lean_dec(v_name_1107_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__3));
v___x_1119_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__0));
v___x_1120_ = lean_array_push(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__7));
v___x_1129_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__4, &l_Lake_LeanLibConfig___fields___closed__4_once, _init_l_Lake_LeanLibConfig___fields___closed__4);
v___x_1130_ = lean_array_push(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__11));
v___x_1139_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__8, &l_Lake_LeanLibConfig___fields___closed__8_once, _init_l_Lake_LeanLibConfig___fields___closed__8);
v___x_1140_ = lean_array_push(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__15));
v___x_1149_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__12, &l_Lake_LeanLibConfig___fields___closed__12_once, _init_l_Lake_LeanLibConfig___fields___closed__12);
v___x_1150_ = lean_array_push(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__19));
v___x_1159_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__16, &l_Lake_LeanLibConfig___fields___closed__16_once, _init_l_Lake_LeanLibConfig___fields___closed__16);
v___x_1160_ = lean_array_push(v___x_1159_, v___x_1158_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__23));
v___x_1169_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__20, &l_Lake_LeanLibConfig___fields___closed__20_once, _init_l_Lake_LeanLibConfig___fields___closed__20);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__27));
v___x_1179_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__24, &l_Lake_LeanLibConfig___fields___closed__24_once, _init_l_Lake_LeanLibConfig___fields___closed__24);
v___x_1180_ = lean_array_push(v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__31));
v___x_1189_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__28, &l_Lake_LeanLibConfig___fields___closed__28_once, _init_l_Lake_LeanLibConfig___fields___closed__28);
v___x_1190_ = lean_array_push(v___x_1189_, v___x_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__35));
v___x_1199_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__32, &l_Lake_LeanLibConfig___fields___closed__32_once, _init_l_Lake_LeanLibConfig___fields___closed__32);
v___x_1200_ = lean_array_push(v___x_1199_, v___x_1198_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__39));
v___x_1209_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__36, &l_Lake_LeanLibConfig___fields___closed__36_once, _init_l_Lake_LeanLibConfig___fields___closed__36);
v___x_1210_ = lean_array_push(v___x_1209_, v___x_1208_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__43));
v___x_1219_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__40, &l_Lake_LeanLibConfig___fields___closed__40_once, _init_l_Lake_LeanLibConfig___fields___closed__40);
v___x_1220_ = lean_array_push(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__47));
v___x_1229_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__44, &l_Lake_LeanLibConfig___fields___closed__44_once, _init_l_Lake_LeanLibConfig___fields___closed__44);
v___x_1230_ = lean_array_push(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__49(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = l_Lake_LeanConfig___fields;
v___x_1232_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__48, &l_Lake_LeanLibConfig___fields___closed__48_once, _init_l_Lake_LeanLibConfig___fields___closed__48);
v___x_1233_ = l_Array_append___redArg(v___x_1232_, v___x_1231_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields___closed__53(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l_Lake_LeanLibConfig___fields___closed__52));
v___x_1242_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__49, &l_Lake_LeanLibConfig___fields___closed__49_once, _init_l_Lake_LeanLibConfig___fields___closed__49);
v___x_1243_ = lean_array_push(v___x_1242_, v___x_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig___fields(void){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_obj_once(&l_Lake_LeanLibConfig___fields___closed__53, &l_Lake_LeanLibConfig___fields___closed__53_once, _init_l_Lake_LeanLibConfig___fields___closed__53);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lake_LeanLibConfig___fields;
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lake_LeanLibConfig_instConfigFields___redArg();
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields(lean_object* v_name_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lake_LeanLibConfig___fields;
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigFields___boxed(lean_object* v_name_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lake_LeanLibConfig_instConfigFields(v_name_1251_);
lean_dec(v_name_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instConfigInfo___lam__0(lean_object* v_x1_1253_, lean_object* v_x2_1254_){
_start:
{
lean_object* v_name_1255_; lean_object* v___x_1256_; 
v_name_1255_ = lean_ctor_get(v_x2_1254_, 0);
lean_inc(v_name_1255_);
v___x_1256_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1255_, v_x2_1254_, v_x1_1253_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = l_Lake_LeanLibConfig___fields;
v___x_1258_ = lean_array_get_size(v___x_1257_);
return v___x_1258_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1278_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_nat_dec_lt(v___x_1279_, v___x_1278_);
return v___x_1280_;
}
}
static uint8_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1283_ = lean_nat_dec_le(v___x_1282_, v___x_1282_);
return v___x_1283_;
}
}
static size_t _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_1284_; size_t v___x_1285_; 
v___x_1284_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__0, &l_Lake_LeanLibConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0);
v___x_1285_ = lean_usize_of_nat(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1286_ = lean_box(1);
v___x_1287_ = lean_usize_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__14, &l_Lake_LeanLibConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14);
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = l_Lake_LeanLibConfig___fields;
v___f_1290_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__12));
v___x_1291_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1291_, v___f_1290_, v___x_1289_, v___x_1288_, v___x_1287_, v___x_1286_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___y_1295_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1293_ = l_Lake_LeanLibConfig___fields;
v___x_1298_ = lean_box(1);
v___x_1299_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__11, &l_Lake_LeanLibConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11);
if (v___x_1299_ == 0)
{
v___y_1295_ = v___x_1298_;
goto v___jp_1294_;
}
else
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_uint8_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__13, &l_Lake_LeanLibConfig_instConfigInfo___closed__13_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13);
if (v___x_1300_ == 0)
{
if (v___x_1299_ == 0)
{
v___y_1295_ = v___x_1298_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1295_ = v___x_1301_;
goto v___jp_1294_;
}
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_obj_once(&l_Lake_LeanLibConfig_instConfigInfo___closed__15, &l_Lake_LeanLibConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15);
v___y_1295_ = v___x_1302_;
goto v___jp_1294_;
}
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_1295_);
v___x_1297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1293_);
lean_ctor_set(v___x_1297_, 1, v___y_1295_);
lean_ctor_set(v___x_1297_, 2, v___x_1296_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection___lam__0(lean_object* v_x_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_instEmptyCollection(lean_object* v_name_1306_){
_start:
{
lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; size_t v_sz_1317_; size_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___f_1307_ = ((lean_object*)(l_Lake_LeanLibConfig_instEmptyCollection___closed__0));
v___f_1308_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__0));
v___x_1309_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__0));
v___x_1310_ = 0;
v___x_1311_ = ((lean_object*)(l_Lake_LeanLibConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
v___x_1312_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__1));
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_mk_empty_array_with_capacity(v___x_1313_);
v___x_1315_ = lean_array_push(v___x_1314_, v_name_1306_);
v___x_1316_ = ((lean_object*)(l_Lake_LeanLibConfig_instConfigInfo___closed__10));
v_sz_1317_ = lean_array_size(v___x_1315_);
v___x_1318_ = ((size_t)0ULL);
lean_inc_ref(v___x_1315_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1316_, v___f_1307_, v_sz_1317_, v___x_1318_, v___x_1315_);
v___x_1320_ = ((lean_object*)(l_Lake_instInhabitedLeanLibConfig_default___closed__2));
v___x_1321_ = lean_obj_once(&l_Lake_instInhabitedLeanLibConfig_default___closed__4, &l_Lake_instInhabitedLeanLibConfig_default___closed__4_once, _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4);
v___x_1322_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v___x_1322_, 0, v___x_1311_);
lean_ctor_set(v___x_1322_, 1, v___x_1312_);
lean_ctor_set(v___x_1322_, 2, v___x_1315_);
lean_ctor_set(v___x_1322_, 3, v___x_1319_);
lean_ctor_set(v___x_1322_, 4, v___x_1320_);
lean_ctor_set(v___x_1322_, 5, v___x_1309_);
lean_ctor_set(v___x_1322_, 6, v___x_1309_);
lean_ctor_set(v___x_1322_, 7, v___x_1321_);
lean_ctor_set(v___x_1322_, 8, v___f_1308_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*9, v___x_1310_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*9 + 1, v___x_1310_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*9 + 2, v___x_1310_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*9 + 3, v___x_1310_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg(lean_object* v_n_1323_){
_start:
{
lean_inc(v_n_1323_);
return v_n_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___redArg___boxed(lean_object* v_n_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lake_LeanLibConfig_name___redArg(v_n_1324_);
lean_dec(v_n_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name(lean_object* v_n_1326_, lean_object* v_x_1327_){
_start:
{
lean_inc(v_n_1326_);
return v_n_1326_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_name___boxed(lean_object* v_n_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lake_LeanLibConfig_name(v_n_1328_, v_x_1329_);
lean_dec_ref(v_x_1329_);
lean_dec(v_n_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(lean_object* v_mod_1331_, lean_object* v_as_1332_, size_t v_i_1333_, size_t v_stop_1334_){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_usize_dec_eq(v_i_1333_, v_stop_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_array_uget_borrowed(v_as_1332_, v_i_1333_);
v___x_1337_ = l_Lake_Glob_matches(v_mod_1331_, v___x_1336_);
if (v___x_1337_ == 0)
{
size_t v___x_1338_; size_t v___x_1339_; 
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1333_, v___x_1338_);
v_i_1333_ = v___x_1339_;
goto _start;
}
else
{
return v___x_1337_;
}
}
else
{
uint8_t v___x_1341_; 
v___x_1341_ = 0;
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(lean_object* v_mod_1342_, lean_object* v_as_1343_, lean_object* v_i_1344_, lean_object* v_stop_1345_){
_start:
{
size_t v_i_boxed_1346_; size_t v_stop_boxed_1347_; uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_i_boxed_1346_ = lean_unbox_usize(v_i_1344_);
lean_dec(v_i_1344_);
v_stop_boxed_1347_ = lean_unbox_usize(v_stop_1345_);
lean_dec(v_stop_1345_);
v_res_1348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1342_, v_as_1343_, v_i_boxed_1346_, v_stop_boxed_1347_);
lean_dec_ref(v_as_1343_);
lean_dec(v_mod_1342_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(lean_object* v_mod_1350_, lean_object* v_as_1351_, size_t v_i_1352_, size_t v_stop_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_eq(v_i_1352_, v_stop_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_array_uget_borrowed(v_as_1351_, v_i_1352_);
v___x_1356_ = l_Lean_Name_isPrefixOf(v___x_1355_, v_mod_1350_);
if (v___x_1356_ == 0)
{
size_t v___x_1357_; size_t v___x_1358_; 
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_add(v_i_1352_, v___x_1357_);
v_i_1352_ = v___x_1358_;
goto _start;
}
else
{
return v___x_1356_;
}
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = 0;
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(lean_object* v_mod_1361_, lean_object* v_as_1362_, lean_object* v_i_1363_, lean_object* v_stop_1364_){
_start:
{
size_t v_i_boxed_1365_; size_t v_stop_boxed_1366_; uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_i_boxed_1365_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_stop_boxed_1366_ = lean_unbox_usize(v_stop_1364_);
lean_dec(v_stop_1364_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1361_, v_as_1362_, v_i_boxed_1365_, v_stop_boxed_1366_);
lean_dec_ref(v_as_1362_);
lean_dec(v_mod_1361_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object* v_mod_1369_, lean_object* v_self_1370_){
_start:
{
lean_object* v_roots_1371_; lean_object* v_globs_1372_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_roots_1371_ = lean_ctor_get(v_self_1370_, 2);
v_globs_1372_ = lean_ctor_get(v_self_1370_, 3);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_array_get_size(v_roots_1371_);
v___x_1382_ = lean_nat_dec_lt(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
goto v___jp_1373_;
}
else
{
if (v___x_1382_ == 0)
{
goto v___jp_1373_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = lean_usize_of_nat(v___x_1381_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_1369_, v_roots_1371_, v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
goto v___jp_1373_;
}
else
{
return v___x_1385_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_array_get_size(v_globs_1372_);
v___x_1376_ = lean_nat_dec_lt(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
return v___x_1376_;
}
else
{
if (v___x_1376_ == 0)
{
return v___x_1376_;
}
else
{
size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_of_nat(v___x_1375_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1369_, v_globs_1372_, v___x_1377_, v___x_1378_);
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(lean_object* v_mod_1386_, lean_object* v_self_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1386_, v_self_1387_);
lean_dec_ref(v_self_1387_);
lean_dec(v_mod_1386_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object* v_n_1390_, lean_object* v_mod_1391_, lean_object* v_self_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1391_, v_self_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isLocalModule___boxed(lean_object* v_n_1394_, lean_object* v_mod_1395_, lean_object* v_self_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Lake_LeanLibConfig_isLocalModule(v_n_1394_, v_mod_1395_, v_self_1396_);
lean_dec_ref(v_self_1396_);
lean_dec(v_mod_1395_);
lean_dec(v_n_1394_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(lean_object* v_mod_1399_, lean_object* v_self_1400_, lean_object* v_as_1401_, size_t v_i_1402_, size_t v_stop_1403_){
_start:
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_usize_dec_eq(v_i_1402_, v_stop_1403_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; uint8_t v___y_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1409_ = 1;
v___x_1412_ = lean_array_uget_borrowed(v_as_1401_, v_i_1402_);
v___x_1413_ = l_Lean_Name_isPrefixOf(v___x_1412_, v_mod_1399_);
if (v___x_1413_ == 0)
{
v___y_1411_ = v___x_1413_;
goto v___jp_1410_;
}
else
{
lean_object* v_globs_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_globs_1414_ = lean_ctor_get(v_self_1400_, 3);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_globs_1414_);
v___x_1417_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
goto v___jp_1404_;
}
else
{
if (v___x_1417_ == 0)
{
goto v___jp_1404_;
}
else
{
size_t v___x_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = lean_usize_of_nat(v___x_1416_);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v___x_1412_, v_globs_1414_, v___x_1418_, v___x_1419_);
v___y_1411_ = v___x_1420_;
goto v___jp_1410_;
}
}
}
v___jp_1410_:
{
if (v___y_1411_ == 0)
{
goto v___jp_1404_;
}
else
{
return v___x_1409_;
}
}
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
v___jp_1404_:
{
size_t v___x_1405_; size_t v___x_1406_; 
v___x_1405_ = ((size_t)1ULL);
v___x_1406_ = lean_usize_add(v_i_1402_, v___x_1405_);
v_i_1402_ = v___x_1406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(lean_object* v_mod_1422_, lean_object* v_self_1423_, lean_object* v_as_1424_, lean_object* v_i_1425_, lean_object* v_stop_1426_){
_start:
{
size_t v_i_boxed_1427_; size_t v_stop_boxed_1428_; uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_i_boxed_1427_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_stop_boxed_1428_ = lean_unbox_usize(v_stop_1426_);
lean_dec(v_stop_1426_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1422_, v_self_1423_, v_as_1424_, v_i_boxed_1427_, v_stop_boxed_1428_);
lean_dec_ref(v_as_1424_);
lean_dec_ref(v_self_1423_);
lean_dec(v_mod_1422_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object* v_mod_1431_, lean_object* v_self_1432_){
_start:
{
lean_object* v_roots_1433_; lean_object* v_globs_1434_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_roots_1433_ = lean_ctor_get(v_self_1432_, 2);
v_globs_1434_ = lean_ctor_get(v_self_1432_, 3);
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_array_get_size(v_globs_1434_);
v___x_1444_ = lean_nat_dec_lt(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
goto v___jp_1435_;
}
else
{
if (v___x_1444_ == 0)
{
goto v___jp_1435_;
}
else
{
size_t v___x_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = lean_usize_of_nat(v___x_1443_);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_1431_, v_globs_1434_, v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
goto v___jp_1435_;
}
else
{
return v___x_1447_;
}
}
}
v___jp_1435_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_array_get_size(v_roots_1433_);
v___x_1438_ = lean_nat_dec_lt(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
return v___x_1438_;
}
else
{
if (v___x_1438_ == 0)
{
return v___x_1438_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = lean_usize_of_nat(v___x_1437_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_1431_, v_self_1432_, v_roots_1433_, v___x_1439_, v___x_1440_);
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(lean_object* v_mod_1448_, lean_object* v_self_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1448_, v_self_1449_);
lean_dec_ref(v_self_1449_);
lean_dec(v_mod_1448_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object* v_n_1452_, lean_object* v_mod_1453_, lean_object* v_self_1454_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1453_, v_self_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_isBuildableModule___boxed(lean_object* v_n_1456_, lean_object* v_mod_1457_, lean_object* v_self_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_1456_, v_mod_1457_, v_self_1458_);
lean_dec_ref(v_self_1458_);
lean_dec(v_mod_1457_);
lean_dec(v_n_1456_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
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
