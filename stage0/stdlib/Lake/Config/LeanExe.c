// Lean compiler output
// Module: Lake.Config.LeanExe
// Imports: public import Lake.Config.Module
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_LeanLib_findModuleBySrc_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern uint8_t l_System_Platform_isWindows;
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Package_findModule_x3f(lean_object*, lean_object*);
uint8_t lean_strict_and(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_leanExes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanExes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Package_leanExes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_leanExes___closed__0 = (const lean_object*)&l_Lake_Package_leanExes___closed__0_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__1 = (const lean_object*)&l_Lake_Package_leanExes___closed__1_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__2 = (const lean_object*)&l_Lake_Package_leanExes___closed__2_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__3 = (const lean_object*)&l_Lake_Package_leanExes___closed__3_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__4 = (const lean_object*)&l_Lake_Package_leanExes___closed__4_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__5 = (const lean_object*)&l_Lake_Package_leanExes___closed__5_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__6 = (const lean_object*)&l_Lake_Package_leanExes___closed__6_value;
static const lean_closure_object l_Lake_Package_leanExes___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanExes___closed__7 = (const lean_object*)&l_Lake_Package_leanExes___closed__7_value;
static const lean_ctor_object l_Lake_Package_leanExes___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_leanExes___closed__1_value),((lean_object*)&l_Lake_Package_leanExes___closed__2_value)}};
static const lean_object* l_Lake_Package_leanExes___closed__8 = (const lean_object*)&l_Lake_Package_leanExes___closed__8_value;
static const lean_ctor_object l_Lake_Package_leanExes___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_leanExes___closed__8_value),((lean_object*)&l_Lake_Package_leanExes___closed__3_value),((lean_object*)&l_Lake_Package_leanExes___closed__4_value),((lean_object*)&l_Lake_Package_leanExes___closed__5_value),((lean_object*)&l_Lake_Package_leanExes___closed__6_value)}};
static const lean_object* l_Lake_Package_leanExes___closed__9 = (const lean_object*)&l_Lake_Package_leanExes___closed__9_value;
static const lean_ctor_object l_Lake_Package_leanExes___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_leanExes___closed__9_value),((lean_object*)&l_Lake_Package_leanExes___closed__7_value)}};
static const lean_object* l_Lake_Package_leanExes___closed__10 = (const lean_object*)&l_Lake_Package_leanExes___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Package_leanExes(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findLeanExe_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0 = (const lean_object*)&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1;
static lean_once_cell_t l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2;
static lean_once_cell_t l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_config(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_config___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_toLeanLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_root(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_LeanExe_isRootSrc_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_LeanExe_isRootSrc_x3f___closed__0 = (const lean_object*)&l_Lake_LeanExe_isRootSrc_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRootSrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_fileName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_file(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanExe_supportInterpreter(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_supportInterpreter___boxed(lean_object*);
static const lean_array_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__0 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__0_value;
static const lean_string_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-rdynamic"};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__1 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__1_value;
static const lean_array_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__1_value)}};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__2 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__2_value;
static const lean_string_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "-Wl,--whole-archive"};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__3 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__3_value;
static const lean_string_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "-lleanmanifest"};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__4 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__4_value;
static const lean_string_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-Wl,--no-whole-archive"};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__5 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__5_value;
static const lean_array_object l_Lake_LeanExe_exeOnlyLinkArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__3_value),((lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__4_value),((lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__5_value)}};
static const lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___closed__6 = (const lean_object*)&l_Lake_LeanExe_exeOnlyLinkArgs___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeOnlyLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanExe_sharedLean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_sharedLean___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_weakLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanExes___lam__0(lean_object* v___x_1_, lean_object* v_self_2_, lean_object* v_x1_3_, lean_object* v_x2_4_){
_start:
{
lean_object* v_name_5_; lean_object* v_kind_6_; lean_object* v_config_7_; uint8_t v___x_8_; 
v_name_5_ = lean_ctor_get(v_x2_4_, 1);
v_kind_6_ = lean_ctor_get(v_x2_4_, 2);
v_config_7_ = lean_ctor_get(v_x2_4_, 3);
v___x_8_ = lean_name_eq(v_kind_6_, v___x_1_);
if (v___x_8_ == 0)
{
lean_dec_ref(v_self_2_);
return v_x1_3_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc(v_config_7_);
lean_inc(v_name_5_);
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v_self_2_);
lean_ctor_set(v___x_9_, 1, v_name_5_);
lean_ctor_set(v___x_9_, 2, v_config_7_);
v___x_10_ = lean_array_push(v_x1_3_, v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanExes___lam__0___boxed(lean_object* v___x_11_, lean_object* v_self_12_, lean_object* v_x1_13_, lean_object* v_x2_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_Package_leanExes___lam__0(v___x_11_, v_self_12_, v_x1_13_, v_x2_14_);
lean_dec_ref(v_x2_14_);
lean_dec(v___x_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanExes(lean_object* v_self_37_){
_start:
{
lean_object* v_targetDecls_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_targetDecls_38_ = lean_ctor_get(v_self_37_, 15);
lean_inc_ref(v_targetDecls_38_);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_41_ = lean_array_get_size(v_targetDecls_38_);
v___x_42_ = ((lean_object*)(l_Lake_Package_leanExes___closed__10));
v___x_43_ = lean_nat_dec_lt(v___x_39_, v___x_41_);
if (v___x_43_ == 0)
{
lean_dec_ref(v_targetDecls_38_);
lean_dec_ref(v_self_37_);
return v___x_40_;
}
else
{
lean_object* v___x_44_; lean_object* v___f_45_; size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; 
v___x_44_ = l_Lake_LeanExe_keyword;
v___f_45_ = lean_alloc_closure((void*)(l_Lake_Package_leanExes___lam__0___boxed), 4, 2);
lean_closure_set(v___f_45_, 0, v___x_44_);
lean_closure_set(v___f_45_, 1, v_self_37_);
v___x_46_ = ((size_t)0ULL);
v___x_47_ = lean_usize_of_nat(v___x_41_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_42_, v___f_45_, v_targetDecls_38_, v___x_46_, v___x_47_, v___x_40_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanExe_x3f(lean_object* v_name_49_, lean_object* v_self_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lake_Package_findTargetDecl_x3f(v_name_49_, v_self_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_52_; 
lean_dec_ref(v_self_50_);
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_67_; 
v_val_53_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_67_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_67_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_val_53_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_67_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_name_57_; lean_object* v_kind_58_; lean_object* v_config_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_name_57_ = lean_ctor_get(v_val_53_, 1);
lean_inc(v_name_57_);
v_kind_58_ = lean_ctor_get(v_val_53_, 2);
lean_inc(v_kind_58_);
v_config_59_ = lean_ctor_get(v_val_53_, 3);
lean_inc(v_config_59_);
lean_dec(v_val_53_);
v___x_60_ = l_Lake_LeanExe_keyword;
v___x_61_ = lean_name_eq(v_kind_58_, v___x_60_);
lean_dec(v_kind_58_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec(v_config_59_);
lean_dec(v_name_57_);
lean_del_object(v___x_55_);
lean_dec_ref(v_self_50_);
v___x_62_ = lean_box(0);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v_self_50_);
lean_ctor_set(v___x_63_, 1, v_name_57_);
lean_ctor_set(v___x_63_, 2, v_config_59_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_63_);
v___x_65_ = v___x_55_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanExe_x3f___boxed(lean_object* v_name_68_, lean_object* v_self_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lake_Package_findLeanExe_x3f(v_name_68_, v_self_69_);
lean_dec(v_name_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(size_t v_sz_71_, size_t v_i_72_, lean_object* v_bs_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_usize_dec_lt(v_i_72_, v_sz_71_);
if (v___x_74_ == 0)
{
return v_bs_73_;
}
else
{
lean_object* v_v_75_; lean_object* v___x_76_; lean_object* v_bs_x27_77_; lean_object* v___x_78_; size_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; 
v_v_75_ = lean_array_uget(v_bs_73_, v_i_72_);
v___x_76_ = lean_unsigned_to_nat(0u);
v_bs_x27_77_ = lean_array_uset(v_bs_73_, v_i_72_, v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_v_75_);
v___x_79_ = ((size_t)1ULL);
v___x_80_ = lean_usize_add(v_i_72_, v___x_79_);
v___x_81_ = lean_array_uset(v_bs_x27_77_, v_i_72_, v___x_78_);
v_i_72_ = v___x_80_;
v_bs_73_ = v___x_81_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0___boxed(lean_object* v_sz_83_, lean_object* v_i_84_, lean_object* v_bs_85_){
_start:
{
size_t v_sz_boxed_86_; size_t v_i_boxed_87_; lean_object* v_res_88_; 
v_sz_boxed_86_ = lean_unbox_usize(v_sz_83_);
lean_dec(v_sz_83_);
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_boxed_86_, v_i_boxed_87_, v_bs_85_);
return v_res_88_;
}
}
static size_t _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_91_; size_t v_sz_92_; 
v___x_91_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v_sz_92_ = lean_array_size(v___x_91_);
return v_sz_92_;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2(void){
_start:
{
lean_object* v___x_93_; size_t v___x_94_; size_t v_sz_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v___x_94_ = ((size_t)0ULL);
v_sz_95_ = lean_usize_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1);
v___x_96_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_95_, v___x_94_, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = l_Lake_LeanLib_leanArtsFacet;
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_100_ = lean_array_push(v___x_99_, v___x_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object* v_self_101_){
_start:
{
lean_object* v_toLeanConfig_102_; lean_object* v_srcDir_103_; lean_object* v_exeName_104_; lean_object* v_needs_105_; lean_object* v_extraDepTargets_106_; lean_object* v_nativeFacets_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_toLeanConfig_102_ = lean_ctor_get(v_self_101_, 0);
v_srcDir_103_ = lean_ctor_get(v_self_101_, 1);
v_exeName_104_ = lean_ctor_get(v_self_101_, 3);
v_needs_105_ = lean_ctor_get(v_self_101_, 4);
v_extraDepTargets_106_ = lean_ctor_get(v_self_101_, 5);
v_nativeFacets_107_ = lean_ctor_get(v_self_101_, 6);
v___x_108_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v___x_109_ = lean_obj_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2);
v___x_110_ = 0;
v___x_111_ = lean_obj_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3);
lean_inc_ref(v_nativeFacets_107_);
lean_inc_ref(v_extraDepTargets_106_);
lean_inc_ref(v_needs_105_);
lean_inc_ref(v_exeName_104_);
lean_inc_ref(v_srcDir_103_);
lean_inc_ref(v_toLeanConfig_102_);
v___x_112_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_112_, 0, v_toLeanConfig_102_);
lean_ctor_set(v___x_112_, 1, v_srcDir_103_);
lean_ctor_set(v___x_112_, 2, v___x_108_);
lean_ctor_set(v___x_112_, 3, v___x_109_);
lean_ctor_set(v___x_112_, 4, v_exeName_104_);
lean_ctor_set(v___x_112_, 5, v_needs_105_);
lean_ctor_set(v___x_112_, 6, v_extraDepTargets_106_);
lean_ctor_set(v___x_112_, 7, v___x_111_);
lean_ctor_set(v___x_112_, 8, v_nativeFacets_107_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*9, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*9 + 1, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*9 + 2, v___x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___boxed(lean_object* v_self_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_113_);
lean_dec_ref(v_self_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig(lean_object* v_n_115_, lean_object* v_self_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___boxed(lean_object* v_n_118_, lean_object* v_self_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lake_LeanExeConfig_toLeanLibConfig(v_n_118_, v_self_119_);
lean_dec_ref(v_self_119_);
lean_dec(v_n_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_config(lean_object* v_self_121_){
_start:
{
lean_object* v_config_122_; 
v_config_122_ = lean_ctor_get(v_self_121_, 2);
lean_inc(v_config_122_);
return v_config_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_config___boxed(lean_object* v_self_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lake_LeanExe_config(v_self_123_);
lean_dec_ref(v_self_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_toLeanLib(lean_object* v_self_125_){
_start:
{
lean_object* v_pkg_126_; lean_object* v_name_127_; lean_object* v_config_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_pkg_126_ = lean_ctor_get(v_self_125_, 0);
v_name_127_ = lean_ctor_get(v_self_125_, 1);
v_config_128_ = lean_ctor_get(v_self_125_, 2);
v_isSharedCheck_136_ = !lean_is_exclusive(v_self_125_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v_self_125_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_config_128_);
lean_inc(v_name_127_);
lean_inc(v_pkg_126_);
lean_dec(v_self_125_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_128_);
lean_dec(v_config_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 2, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_pkg_126_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_name_127_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_root(lean_object* v_self_137_){
_start:
{
lean_object* v_config_138_; lean_object* v_pkg_139_; lean_object* v_name_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_150_; 
v_config_138_ = lean_ctor_get(v_self_137_, 2);
v_pkg_139_ = lean_ctor_get(v_self_137_, 0);
v_name_140_ = lean_ctor_get(v_self_137_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_self_137_);
if (v_isSharedCheck_150_ == 0)
{
v___x_142_ = v_self_137_;
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_config_138_);
lean_inc(v_name_140_);
lean_inc(v_pkg_139_);
lean_dec(v_self_137_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_root_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v_root_144_ = lean_ctor_get(v_config_138_, 2);
lean_inc(v_root_144_);
v___x_145_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_138_);
lean_dec(v_config_138_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 2, v___x_145_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_pkg_139_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_name_140_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v___x_145_);
v___x_147_ = v_reuseFailAlloc_149_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_root_144_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f(lean_object* v_name_151_, lean_object* v_self_152_){
_start:
{
lean_object* v_config_153_; lean_object* v_pkg_154_; lean_object* v_name_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_168_; 
v_config_153_ = lean_ctor_get(v_self_152_, 2);
v_pkg_154_ = lean_ctor_get(v_self_152_, 0);
v_name_155_ = lean_ctor_get(v_self_152_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_self_152_);
if (v_isSharedCheck_168_ == 0)
{
v___x_157_ = v_self_152_;
v_isShared_158_ = v_isSharedCheck_168_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_config_153_);
lean_inc(v_name_155_);
lean_inc(v_pkg_154_);
lean_dec(v_self_152_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_168_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v_root_159_; uint8_t v___x_160_; 
v_root_159_ = lean_ctor_get(v_config_153_, 2);
lean_inc(v_root_159_);
v___x_160_ = lean_name_eq(v_name_151_, v_root_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec(v_root_159_);
lean_del_object(v___x_157_);
lean_dec(v_name_155_);
lean_dec_ref(v_pkg_154_);
lean_dec(v_config_153_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_153_);
lean_dec(v_config_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 2, v___x_162_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_pkg_154_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_name_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v___x_162_);
v___x_164_ = v_reuseFailAlloc_167_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_root_159_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f___boxed(lean_object* v_name_169_, lean_object* v_self_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lake_LeanExe_isRoot_x3f(v_name_169_, v_self_170_);
lean_dec(v_name_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRootSrc_x3f(lean_object* v_path_173_, lean_object* v_self_174_){
_start:
{
lean_object* v_config_175_; lean_object* v_pkg_176_; lean_object* v_config_177_; lean_object* v_name_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_201_; 
v_config_175_ = lean_ctor_get(v_self_174_, 2);
lean_inc(v_config_175_);
v_pkg_176_ = lean_ctor_get(v_self_174_, 0);
lean_inc_ref(v_pkg_176_);
v_config_177_ = lean_ctor_get(v_pkg_176_, 6);
v_name_178_ = lean_ctor_get(v_self_174_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_self_174_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; 
v_unused_202_ = lean_ctor_get(v_self_174_, 2);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_self_174_, 0);
lean_dec(v_unused_203_);
v___x_180_ = v_self_174_;
v_isShared_181_ = v_isSharedCheck_201_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_name_178_);
lean_dec(v_self_174_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_201_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_root_182_; lean_object* v_dir_183_; lean_object* v_srcDir_184_; lean_object* v___x_185_; lean_object* v_srcDir_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v_root_182_ = lean_ctor_get(v_config_175_, 2);
lean_inc(v_root_182_);
v_dir_183_ = lean_ctor_get(v_pkg_176_, 4);
lean_inc_ref(v_dir_183_);
v_srcDir_184_ = lean_ctor_get(v_config_177_, 4);
lean_inc_ref(v_srcDir_184_);
v___x_185_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_175_);
lean_dec(v_config_175_);
v_srcDir_186_ = lean_ctor_get(v___x_185_, 1);
lean_inc_ref(v_srcDir_186_);
v___x_187_ = ((lean_object*)(l_Lake_LeanExe_isRootSrc_x3f___closed__0));
v___x_188_ = l_System_FilePath_withExtension(v_path_173_, v___x_187_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 2, v___x_185_);
v___x_190_ = v___x_180_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_pkg_176_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_name_178_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___x_185_);
v___x_190_ = v_reuseFailAlloc_200_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
lean_inc(v_root_182_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_root_182_);
v___x_192_ = l_System_FilePath_normalize(v_srcDir_184_);
v___x_193_ = l_Lake_joinRelative(v_dir_183_, v___x_192_);
v___x_194_ = l_System_FilePath_normalize(v_srcDir_186_);
v___x_195_ = l_Lake_joinRelative(v___x_193_, v___x_194_);
v___x_196_ = l_Lean_modToFilePath(v___x_195_, v_root_182_, v___x_187_);
lean_dec_ref(v___x_195_);
v___x_197_ = lean_string_dec_eq(v___x_188_, v___x_196_);
lean_dec_ref(v___x_196_);
lean_dec_ref(v___x_188_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_dec_ref_known(v___x_191_, 2);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_191_);
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_fileName(lean_object* v_self_204_){
_start:
{
lean_object* v_config_205_; lean_object* v_exeName_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_config_205_ = lean_ctor_get(v_self_204_, 2);
lean_inc(v_config_205_);
lean_dec_ref(v_self_204_);
v_exeName_206_ = lean_ctor_get(v_config_205_, 3);
lean_inc_ref(v_exeName_206_);
lean_dec(v_config_205_);
v___x_207_ = l_System_FilePath_exeExtension;
v___x_208_ = l_System_FilePath_addExtension(v_exeName_206_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_file(lean_object* v_self_209_){
_start:
{
lean_object* v_pkg_210_; lean_object* v_config_211_; lean_object* v_config_212_; lean_object* v_dir_213_; lean_object* v_buildDir_214_; lean_object* v_binDir_215_; lean_object* v_exeName_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_pkg_210_ = lean_ctor_get(v_self_209_, 0);
lean_inc_ref(v_pkg_210_);
v_config_211_ = lean_ctor_get(v_pkg_210_, 6);
lean_inc_ref(v_config_211_);
v_config_212_ = lean_ctor_get(v_self_209_, 2);
lean_inc(v_config_212_);
lean_dec_ref(v_self_209_);
v_dir_213_ = lean_ctor_get(v_pkg_210_, 4);
lean_inc_ref(v_dir_213_);
lean_dec_ref(v_pkg_210_);
v_buildDir_214_ = lean_ctor_get(v_config_211_, 5);
lean_inc_ref(v_buildDir_214_);
v_binDir_215_ = lean_ctor_get(v_config_211_, 8);
lean_inc_ref(v_binDir_215_);
lean_dec_ref(v_config_211_);
v_exeName_216_ = lean_ctor_get(v_config_212_, 3);
lean_inc_ref(v_exeName_216_);
lean_dec(v_config_212_);
v___x_217_ = l_System_FilePath_normalize(v_buildDir_214_);
v___x_218_ = l_Lake_joinRelative(v_dir_213_, v___x_217_);
v___x_219_ = l_System_FilePath_normalize(v_binDir_215_);
v___x_220_ = l_Lake_joinRelative(v___x_218_, v___x_219_);
v___x_221_ = l_System_FilePath_exeExtension;
v___x_222_ = l_System_FilePath_addExtension(v_exeName_216_, v___x_221_);
v___x_223_ = l_Lake_joinRelative(v___x_220_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanExe_supportInterpreter(lean_object* v_self_224_){
_start:
{
lean_object* v_config_225_; uint8_t v_supportInterpreter_226_; 
v_config_225_ = lean_ctor_get(v_self_224_, 2);
v_supportInterpreter_226_ = lean_ctor_get_uint8(v_config_225_, sizeof(void*)*7);
return v_supportInterpreter_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_supportInterpreter___boxed(lean_object* v_self_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lake_LeanExe_supportInterpreter(v_self_227_);
lean_dec_ref(v_self_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeOnlyLinkArgs(lean_object* v_self_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l_System_Platform_isWindows;
if (v___x_249_ == 0)
{
lean_object* v_config_250_; uint8_t v_supportInterpreter_251_; 
v_config_250_ = lean_ctor_get(v_self_248_, 2);
v_supportInterpreter_251_ = lean_ctor_get_uint8(v_config_250_, sizeof(void*)*7);
if (v_supportInterpreter_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = ((lean_object*)(l_Lake_LeanExe_exeOnlyLinkArgs___closed__0));
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = ((lean_object*)(l_Lake_LeanExe_exeOnlyLinkArgs___closed__2));
return v___x_253_;
}
}
else
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_Lake_LeanExe_exeOnlyLinkArgs___closed__6));
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___boxed(lean_object* v_self_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lake_LeanExe_exeOnlyLinkArgs(v_self_255_);
lean_dec_ref(v_self_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs(lean_object* v_self_257_){
_start:
{
lean_object* v_pkg_258_; lean_object* v_config_259_; lean_object* v_toLeanConfig_260_; lean_object* v_config_261_; lean_object* v_toLeanConfig_262_; lean_object* v_moreLinkArgs_263_; lean_object* v_moreLinkArgs_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_pkg_258_ = lean_ctor_get(v_self_257_, 0);
v_config_259_ = lean_ctor_get(v_pkg_258_, 6);
v_toLeanConfig_260_ = lean_ctor_get(v_config_259_, 1);
v_config_261_ = lean_ctor_get(v_self_257_, 2);
v_toLeanConfig_262_ = lean_ctor_get(v_config_261_, 0);
v_moreLinkArgs_263_ = lean_ctor_get(v_toLeanConfig_260_, 8);
v_moreLinkArgs_264_ = lean_ctor_get(v_toLeanConfig_262_, 8);
v___x_265_ = l_Lake_LeanExe_exeOnlyLinkArgs(v_self_257_);
v___x_266_ = l_Array_append___redArg(v___x_265_, v_moreLinkArgs_263_);
v___x_267_ = l_Array_append___redArg(v___x_266_, v_moreLinkArgs_264_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs___boxed(lean_object* v_self_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_LeanExe_linkArgs(v_self_268_);
lean_dec_ref(v_self_268_);
return v_res_269_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanExe_sharedLean(lean_object* v_self_270_){
_start:
{
lean_object* v_config_271_; uint8_t v_supportInterpreter_272_; uint8_t v___x_273_; uint8_t v___x_274_; 
v_config_271_ = lean_ctor_get(v_self_270_, 2);
v_supportInterpreter_272_ = lean_ctor_get_uint8(v_config_271_, sizeof(void*)*7);
v___x_273_ = l_System_Platform_isWindows;
v___x_274_ = lean_strict_and(v___x_273_, v_supportInterpreter_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_sharedLean___boxed(lean_object* v_self_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Lake_LeanExe_sharedLean(v_self_275_);
lean_dec_ref(v_self_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_weakLinkArgs(lean_object* v_self_278_){
_start:
{
lean_object* v_pkg_279_; lean_object* v_config_280_; lean_object* v_toLeanConfig_281_; lean_object* v_config_282_; lean_object* v_toLeanConfig_283_; lean_object* v_weakLinkArgs_284_; lean_object* v_weakLinkArgs_285_; lean_object* v___x_286_; 
v_pkg_279_ = lean_ctor_get(v_self_278_, 0);
v_config_280_ = lean_ctor_get(v_pkg_279_, 6);
v_toLeanConfig_281_ = lean_ctor_get(v_config_280_, 1);
lean_inc_ref(v_toLeanConfig_281_);
v_config_282_ = lean_ctor_get(v_self_278_, 2);
lean_inc(v_config_282_);
lean_dec_ref(v_self_278_);
v_toLeanConfig_283_ = lean_ctor_get(v_config_282_, 0);
lean_inc_ref(v_toLeanConfig_283_);
lean_dec(v_config_282_);
v_weakLinkArgs_284_ = lean_ctor_get(v_toLeanConfig_281_, 9);
lean_inc_ref(v_weakLinkArgs_284_);
lean_dec_ref(v_toLeanConfig_281_);
v_weakLinkArgs_285_ = lean_ctor_get(v_toLeanConfig_283_, 9);
lean_inc_ref(v_weakLinkArgs_285_);
lean_dec_ref(v_toLeanConfig_283_);
v___x_286_ = l_Array_append___redArg(v_weakLinkArgs_284_, v_weakLinkArgs_285_);
lean_dec_ref(v_weakLinkArgs_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs(lean_object* v_self_287_){
_start:
{
lean_object* v_config_288_; lean_object* v_toLeanConfig_289_; lean_object* v_moreLinkObjs_290_; 
v_config_288_ = lean_ctor_get(v_self_287_, 2);
v_toLeanConfig_289_ = lean_ctor_get(v_config_288_, 0);
v_moreLinkObjs_290_ = lean_ctor_get(v_toLeanConfig_289_, 6);
lean_inc_ref(v_moreLinkObjs_290_);
return v_moreLinkObjs_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs___boxed(lean_object* v_self_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_LeanExe_moreLinkObjs(v_self_291_);
lean_dec_ref(v_self_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs(lean_object* v_self_293_){
_start:
{
lean_object* v_config_294_; lean_object* v_toLeanConfig_295_; lean_object* v_moreLinkLibs_296_; 
v_config_294_ = lean_ctor_get(v_self_293_, 2);
v_toLeanConfig_295_ = lean_ctor_get(v_config_294_, 0);
v_moreLinkLibs_296_ = lean_ctor_get(v_toLeanConfig_295_, 7);
lean_inc_ref(v_moreLinkLibs_296_);
return v_moreLinkLibs_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs___boxed(lean_object* v_self_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lake_LeanExe_moreLinkLibs(v_self_297_);
lean_dec_ref(v_self_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(lean_object* v_mod_299_, lean_object* v_as_300_, lean_object* v_i_301_){
_start:
{
lean_object* v_zero_302_; uint8_t v_isZero_303_; 
v_zero_302_ = lean_unsigned_to_nat(0u);
v_isZero_303_ = lean_nat_dec_eq(v_i_301_, v_zero_302_);
if (v_isZero_303_ == 1)
{
lean_object* v___x_304_; 
lean_dec(v_i_301_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v_one_305_; lean_object* v_n_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_one_305_ = lean_unsigned_to_nat(1u);
v_n_306_ = lean_nat_sub(v_i_301_, v_one_305_);
lean_dec(v_i_301_);
v___x_307_ = lean_array_fget_borrowed(v_as_300_, v_n_306_);
lean_inc(v___x_307_);
v___x_308_ = l_Lake_LeanExe_isRoot_x3f(v_mod_299_, v___x_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
v_i_301_ = v_n_306_;
goto _start;
}
else
{
lean_dec(v_n_306_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_310_, lean_object* v_as_311_, lean_object* v_i_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_310_, v_as_311_, v_i_312_);
lean_dec_ref(v_as_311_);
lean_dec(v_mod_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(lean_object* v_self_314_, lean_object* v_as_315_, size_t v_i_316_, size_t v_stop_317_, lean_object* v_b_318_){
_start:
{
lean_object* v___y_320_; uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_eq(v_i_316_, v_stop_317_);
if (v___x_324_ == 0)
{
lean_object* v_toConfigDecl_325_; lean_object* v_name_326_; lean_object* v_kind_327_; lean_object* v_config_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_toConfigDecl_325_ = lean_array_uget_borrowed(v_as_315_, v_i_316_);
v_name_326_ = lean_ctor_get(v_toConfigDecl_325_, 1);
v_kind_327_ = lean_ctor_get(v_toConfigDecl_325_, 2);
v_config_328_ = lean_ctor_get(v_toConfigDecl_325_, 3);
v___x_329_ = l_Lake_LeanExe_keyword;
v___x_330_ = lean_name_eq(v_kind_327_, v___x_329_);
if (v___x_330_ == 0)
{
v___y_320_ = v_b_318_;
goto v___jp_319_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc(v_config_328_);
lean_inc(v_name_326_);
lean_inc_ref(v_self_314_);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v_self_314_);
lean_ctor_set(v___x_331_, 1, v_name_326_);
lean_ctor_set(v___x_331_, 2, v_config_328_);
v___x_332_ = lean_array_push(v_b_318_, v___x_331_);
v___y_320_ = v___x_332_;
goto v___jp_319_;
}
}
else
{
lean_dec_ref(v_self_314_);
return v_b_318_;
}
v___jp_319_:
{
size_t v___x_321_; size_t v___x_322_; 
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_i_316_, v___x_321_);
v_i_316_ = v___x_322_;
v_b_318_ = v___y_320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1___boxed(lean_object* v_self_333_, lean_object* v_as_334_, lean_object* v_i_335_, lean_object* v_stop_336_, lean_object* v_b_337_){
_start:
{
size_t v_i_boxed_338_; size_t v_stop_boxed_339_; lean_object* v_res_340_; 
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_stop_boxed_339_ = lean_unbox_usize(v_stop_336_);
lean_dec(v_stop_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_333_, v_as_334_, v_i_boxed_338_, v_stop_boxed_339_, v_b_337_);
lean_dec_ref(v_as_334_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetModule_x3f(lean_object* v_mod_341_, lean_object* v_self_342_){
_start:
{
lean_object* v___y_344_; lean_object* v_targetDecls_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_targetDecls_348_ = lean_ctor_get(v_self_342_, 15);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_351_ = lean_array_get_size(v_targetDecls_348_);
v___x_352_ = lean_nat_dec_lt(v___x_349_, v___x_351_);
if (v___x_352_ == 0)
{
v___y_344_ = v___x_350_;
goto v___jp_343_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_351_);
lean_inc_ref(v_self_342_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_342_, v_targetDecls_348_, v___x_353_, v___x_354_, v___x_350_);
v___y_344_ = v___x_355_;
goto v___jp_343_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_array_get_size(v___y_344_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_341_, v___y_344_, v___x_345_);
lean_dec_ref(v___y_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = l_Lake_Package_findModule_x3f(v_mod_341_, v_self_342_);
return v___x_347_;
}
else
{
lean_dec_ref(v_self_342_);
lean_dec(v_mod_341_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(lean_object* v_mod_356_, lean_object* v_as_357_, lean_object* v_i_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_356_, v_as_357_, v_i_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_361_, lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(v_mod_361_, v_as_362_, v_i_363_, v_a_364_);
lean_dec_ref(v_as_362_);
lean_dec(v_mod_361_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(lean_object* v_path_366_, lean_object* v_as_367_, lean_object* v_i_368_){
_start:
{
lean_object* v_zero_369_; uint8_t v_isZero_370_; 
v_zero_369_ = lean_unsigned_to_nat(0u);
v_isZero_370_ = lean_nat_dec_eq(v_i_368_, v_zero_369_);
if (v_isZero_370_ == 1)
{
lean_object* v___x_371_; 
lean_dec(v_i_368_);
lean_dec_ref(v_path_366_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v_one_372_; lean_object* v_n_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_one_372_ = lean_unsigned_to_nat(1u);
v_n_373_ = lean_nat_sub(v_i_368_, v_one_372_);
lean_dec(v_i_368_);
v___x_374_ = lean_array_fget_borrowed(v_as_367_, v_n_373_);
lean_inc(v___x_374_);
lean_inc_ref(v_path_366_);
v___x_375_ = l_Lake_LeanExe_isRootSrc_x3f(v_path_366_, v___x_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
v_i_368_ = v_n_373_;
goto _start;
}
else
{
lean_dec(v_n_373_);
lean_dec_ref(v_path_366_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg___boxed(lean_object* v_path_377_, lean_object* v_as_378_, lean_object* v_i_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_377_, v_as_378_, v_i_379_);
lean_dec_ref(v_as_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(lean_object* v_self_384_, lean_object* v_as_385_, size_t v_i_386_, size_t v_stop_387_, lean_object* v_b_388_){
_start:
{
lean_object* v___y_390_; uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
if (v___x_394_ == 0)
{
lean_object* v_toConfigDecl_395_; lean_object* v_name_396_; lean_object* v_kind_397_; lean_object* v_config_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_toConfigDecl_395_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
v_name_396_ = lean_ctor_get(v_toConfigDecl_395_, 1);
v_kind_397_ = lean_ctor_get(v_toConfigDecl_395_, 2);
v_config_398_ = lean_ctor_get(v_toConfigDecl_395_, 3);
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1));
v___x_400_ = lean_name_eq(v_kind_397_, v___x_399_);
if (v___x_400_ == 0)
{
v___y_390_ = v_b_388_;
goto v___jp_389_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_inc(v_config_398_);
lean_inc(v_name_396_);
lean_inc_ref(v_self_384_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v_self_384_);
lean_ctor_set(v___x_401_, 1, v_name_396_);
lean_ctor_set(v___x_401_, 2, v_config_398_);
v___x_402_ = lean_array_push(v_b_388_, v___x_401_);
v___y_390_ = v___x_402_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref(v_self_384_);
return v_b_388_;
}
v___jp_389_:
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_386_, v___x_391_);
v_i_386_ = v___x_392_;
v_b_388_ = v___y_390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___boxed(lean_object* v_self_403_, lean_object* v_as_404_, lean_object* v_i_405_, lean_object* v_stop_406_, lean_object* v_b_407_){
_start:
{
size_t v_i_boxed_408_; size_t v_stop_boxed_409_; lean_object* v_res_410_; 
v_i_boxed_408_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_stop_boxed_409_ = lean_unbox_usize(v_stop_406_);
lean_dec(v_stop_406_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_403_, v_as_404_, v_i_boxed_408_, v_stop_boxed_409_, v_b_407_);
lean_dec_ref(v_as_404_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(lean_object* v_path_411_, lean_object* v_as_412_, lean_object* v_i_413_){
_start:
{
lean_object* v_zero_414_; uint8_t v_isZero_415_; 
v_zero_414_ = lean_unsigned_to_nat(0u);
v_isZero_415_ = lean_nat_dec_eq(v_i_413_, v_zero_414_);
if (v_isZero_415_ == 1)
{
lean_object* v___x_416_; 
lean_dec(v_i_413_);
lean_dec_ref(v_path_411_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v_one_417_; lean_object* v_n_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_one_417_ = lean_unsigned_to_nat(1u);
v_n_418_ = lean_nat_sub(v_i_413_, v_one_417_);
lean_dec(v_i_413_);
v___x_419_ = lean_array_fget_borrowed(v_as_412_, v_n_418_);
lean_inc(v___x_419_);
lean_inc_ref(v_path_411_);
v___x_420_ = l_Lake_LeanLib_findModuleBySrc_x3f(v_path_411_, v___x_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
v_i_413_ = v_n_418_;
goto _start;
}
else
{
lean_dec(v_n_418_);
lean_dec_ref(v_path_411_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object* v_path_422_, lean_object* v_as_423_, lean_object* v_i_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_422_, v_as_423_, v_i_424_);
lean_dec_ref(v_as_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModuleBySrc_x3f(lean_object* v_path_426_, lean_object* v_self_427_){
_start:
{
lean_object* v___y_429_; lean_object* v_targetDecls_432_; lean_object* v___y_434_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_targetDecls_432_ = lean_ctor_get(v_self_427_, 15);
lean_inc_ref(v_targetDecls_432_);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_446_ = lean_array_get_size(v_targetDecls_432_);
v___x_447_ = lean_nat_dec_lt(v___x_444_, v___x_446_);
if (v___x_447_ == 0)
{
v___y_434_ = v___x_445_;
goto v___jp_433_;
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_446_);
lean_inc_ref(v_self_427_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_427_, v_targetDecls_432_, v___x_448_, v___x_449_, v___x_445_);
v___y_434_ = v___x_450_;
goto v___jp_433_;
}
v___jp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_array_get_size(v___y_429_);
v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_426_, v___y_429_, v___x_430_);
lean_dec_ref(v___y_429_);
return v___x_431_;
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_array_get_size(v___y_434_);
lean_inc_ref(v_path_426_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_426_, v___y_434_, v___x_435_);
lean_dec_ref(v___y_434_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_439_ = lean_array_get_size(v_targetDecls_432_);
v___x_440_ = lean_nat_dec_lt(v___x_437_, v___x_439_);
if (v___x_440_ == 0)
{
lean_dec_ref(v_targetDecls_432_);
lean_dec_ref(v_self_427_);
v___y_429_ = v___x_438_;
goto v___jp_428_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_439_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_427_, v_targetDecls_432_, v___x_441_, v___x_442_, v___x_438_);
lean_dec_ref(v_targetDecls_432_);
v___y_429_ = v___x_443_;
goto v___jp_428_;
}
}
else
{
lean_dec_ref(v_targetDecls_432_);
lean_dec_ref(v_self_427_);
lean_dec_ref(v_path_426_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(lean_object* v_path_451_, lean_object* v_as_452_, lean_object* v_i_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_451_, v_as_452_, v_i_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(v_path_456_, v_as_457_, v_i_458_, v_a_459_);
lean_dec_ref(v_as_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(lean_object* v_path_461_, lean_object* v_as_462_, lean_object* v_i_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_461_, v_as_462_, v_i_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___boxed(lean_object* v_path_466_, lean_object* v_as_467_, lean_object* v_i_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(v_path_466_, v_as_467_, v_i_468_, v_a_469_);
lean_dec_ref(v_as_467_);
return v_res_470_;
}
}
lean_object* runtime_initialize_Lake_Config_Module(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanExe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_LeanExe(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LeanExe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanExe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_LeanExe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_LeanExe(builtin);
}
#ifdef __cplusplus
}
#endif
