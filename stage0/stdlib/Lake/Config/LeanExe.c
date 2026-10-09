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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(size_t v_sz_71_, size_t v_i_72_, lean_object* v_bs_73_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_71_ = stack[0].m_num;
size_t v_i_72_ = stack[1].m_num;
lean_object* v_bs_73_ = stack[2].m_obj;
lean_object* v_res_83_;
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_71_, v_i_72_, v_bs_73_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0___boxed(lean_object* v_sz_84_, lean_object* v_i_85_, lean_object* v_bs_86_){
_start:
{
size_t v_sz_boxed_87_; size_t v_i_boxed_88_; lean_object* v_res_89_; 
v_sz_boxed_87_ = lean_unbox_usize(v_sz_84_);
lean_dec(v_sz_84_);
v_i_boxed_88_ = lean_unbox_usize(v_i_85_);
lean_dec(v_i_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_boxed_87_, v_i_boxed_88_, v_bs_86_);
return v_res_89_;
}
}
static size_t _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_92_; size_t v_sz_93_; 
v___x_92_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v_sz_93_ = lean_array_size(v___x_92_);
return v_sz_93_;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2(void){
_start:
{
lean_object* v___x_94_; size_t v___x_95_; size_t v_sz_96_; lean_object* v___x_97_; 
v___x_94_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v___x_95_ = ((size_t)0ULL);
v_sz_96_ = lean_usize_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1);
v___x_97_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_96_, v___x_95_, v___x_94_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = l_Lake_LeanLib_leanArtsFacet;
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_101_ = lean_array_push(v___x_100_, v___x_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object* v_self_102_){
_start:
{
lean_object* v_toLeanConfig_103_; lean_object* v_srcDir_104_; lean_object* v_exeName_105_; lean_object* v_needs_106_; lean_object* v_extraDepTargets_107_; lean_object* v_nativeFacets_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_toLeanConfig_103_ = lean_ctor_get(v_self_102_, 0);
v_srcDir_104_ = lean_ctor_get(v_self_102_, 1);
v_exeName_105_ = lean_ctor_get(v_self_102_, 3);
v_needs_106_ = lean_ctor_get(v_self_102_, 4);
v_extraDepTargets_107_ = lean_ctor_get(v_self_102_, 5);
v_nativeFacets_108_ = lean_ctor_get(v_self_102_, 6);
v___x_109_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v___x_110_ = lean_obj_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2);
v___x_111_ = 0;
v___x_112_ = lean_obj_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3);
lean_inc_ref(v_nativeFacets_108_);
lean_inc_ref(v_extraDepTargets_107_);
lean_inc_ref(v_needs_106_);
lean_inc_ref(v_exeName_105_);
lean_inc_ref(v_srcDir_104_);
lean_inc_ref(v_toLeanConfig_103_);
v___x_113_ = lean_alloc_ctor(0, 9, 4);
lean_ctor_set(v___x_113_, 0, v_toLeanConfig_103_);
lean_ctor_set(v___x_113_, 1, v_srcDir_104_);
lean_ctor_set(v___x_113_, 2, v___x_109_);
lean_ctor_set(v___x_113_, 3, v___x_110_);
lean_ctor_set(v___x_113_, 4, v_exeName_105_);
lean_ctor_set(v___x_113_, 5, v_needs_106_);
lean_ctor_set(v___x_113_, 6, v_extraDepTargets_107_);
lean_ctor_set(v___x_113_, 7, v___x_112_);
lean_ctor_set(v___x_113_, 8, v_nativeFacets_108_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*9, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*9 + 1, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*9 + 2, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*9 + 3, v___x_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___boxed(lean_object* v_self_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_114_);
lean_dec_ref(v_self_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig(lean_object* v_n_116_, lean_object* v_self_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___boxed(lean_object* v_n_119_, lean_object* v_self_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lake_LeanExeConfig_toLeanLibConfig(v_n_119_, v_self_120_);
lean_dec_ref(v_self_120_);
lean_dec(v_n_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_config(lean_object* v_self_122_){
_start:
{
lean_object* v_config_123_; 
v_config_123_ = lean_ctor_get(v_self_122_, 2);
lean_inc(v_config_123_);
return v_config_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_config___boxed(lean_object* v_self_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lake_LeanExe_config(v_self_124_);
lean_dec_ref(v_self_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_toLeanLib(lean_object* v_self_126_){
_start:
{
lean_object* v_pkg_127_; lean_object* v_name_128_; lean_object* v_config_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_pkg_127_ = lean_ctor_get(v_self_126_, 0);
v_name_128_ = lean_ctor_get(v_self_126_, 1);
v_config_129_ = lean_ctor_get(v_self_126_, 2);
v_isSharedCheck_137_ = !lean_is_exclusive(v_self_126_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v_self_126_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_config_129_);
lean_inc(v_name_128_);
lean_inc(v_pkg_127_);
lean_dec(v_self_126_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_129_);
lean_dec(v_config_129_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 2, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_pkg_127_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_name_128_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_root(lean_object* v_self_138_){
_start:
{
lean_object* v_config_139_; lean_object* v_pkg_140_; lean_object* v_name_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_151_; 
v_config_139_ = lean_ctor_get(v_self_138_, 2);
v_pkg_140_ = lean_ctor_get(v_self_138_, 0);
v_name_141_ = lean_ctor_get(v_self_138_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_self_138_);
if (v_isSharedCheck_151_ == 0)
{
v___x_143_ = v_self_138_;
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_config_139_);
lean_inc(v_name_141_);
lean_inc(v_pkg_140_);
lean_dec(v_self_138_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_root_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v_root_145_ = lean_ctor_get(v_config_139_, 2);
lean_inc(v_root_145_);
v___x_146_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_139_);
lean_dec(v_config_139_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 2, v___x_146_);
v___x_148_ = v___x_143_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_pkg_140_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_name_141_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v___x_146_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_root_145_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f(lean_object* v_name_152_, lean_object* v_self_153_){
_start:
{
lean_object* v_config_154_; lean_object* v_pkg_155_; lean_object* v_name_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_169_; 
v_config_154_ = lean_ctor_get(v_self_153_, 2);
v_pkg_155_ = lean_ctor_get(v_self_153_, 0);
v_name_156_ = lean_ctor_get(v_self_153_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_self_153_);
if (v_isSharedCheck_169_ == 0)
{
v___x_158_ = v_self_153_;
v_isShared_159_ = v_isSharedCheck_169_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_config_154_);
lean_inc(v_name_156_);
lean_inc(v_pkg_155_);
lean_dec(v_self_153_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_169_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_root_160_; uint8_t v___x_161_; 
v_root_160_ = lean_ctor_get(v_config_154_, 2);
lean_inc(v_root_160_);
v___x_161_ = lean_name_eq(v_name_152_, v_root_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_dec(v_root_160_);
lean_del_object(v___x_158_);
lean_dec(v_name_156_);
lean_dec_ref(v_pkg_155_);
lean_dec(v_config_154_);
v___x_162_ = lean_box(0);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_154_);
lean_dec(v_config_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 2, v___x_163_);
v___x_165_ = v___x_158_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_pkg_155_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_name_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v___x_163_);
v___x_165_ = v_reuseFailAlloc_168_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_root_160_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f___boxed(lean_object* v_name_170_, lean_object* v_self_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lake_LeanExe_isRoot_x3f(v_name_170_, v_self_171_);
lean_dec(v_name_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRootSrc_x3f(lean_object* v_path_174_, lean_object* v_self_175_){
_start:
{
lean_object* v_config_176_; lean_object* v_pkg_177_; lean_object* v_config_178_; lean_object* v_name_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_202_; 
v_config_176_ = lean_ctor_get(v_self_175_, 2);
lean_inc(v_config_176_);
v_pkg_177_ = lean_ctor_get(v_self_175_, 0);
lean_inc_ref(v_pkg_177_);
v_config_178_ = lean_ctor_get(v_pkg_177_, 6);
v_name_179_ = lean_ctor_get(v_self_175_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_self_175_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_self_175_, 2);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_self_175_, 0);
lean_dec(v_unused_204_);
v___x_181_ = v_self_175_;
v_isShared_182_ = v_isSharedCheck_202_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_name_179_);
lean_dec(v_self_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_202_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_root_183_; lean_object* v_dir_184_; lean_object* v_srcDir_185_; lean_object* v___x_186_; lean_object* v_srcDir_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v_root_183_ = lean_ctor_get(v_config_176_, 2);
lean_inc(v_root_183_);
v_dir_184_ = lean_ctor_get(v_pkg_177_, 4);
lean_inc_ref(v_dir_184_);
v_srcDir_185_ = lean_ctor_get(v_config_178_, 4);
lean_inc_ref(v_srcDir_185_);
v___x_186_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_176_);
lean_dec(v_config_176_);
v_srcDir_187_ = lean_ctor_get(v___x_186_, 1);
lean_inc_ref(v_srcDir_187_);
v___x_188_ = ((lean_object*)(l_Lake_LeanExe_isRootSrc_x3f___closed__0));
v___x_189_ = l_System_FilePath_withExtension(v_path_174_, v___x_188_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v___x_186_);
v___x_191_ = v___x_181_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_pkg_177_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_name_179_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___x_186_);
v___x_191_ = v_reuseFailAlloc_201_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
lean_inc(v_root_183_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_root_183_);
v___x_193_ = l_System_FilePath_normalize(v_srcDir_185_);
v___x_194_ = l_Lake_joinRelative(v_dir_184_, v___x_193_);
v___x_195_ = l_System_FilePath_normalize(v_srcDir_187_);
v___x_196_ = l_Lake_joinRelative(v___x_194_, v___x_195_);
v___x_197_ = l_Lean_modToFilePath(v___x_196_, v_root_183_, v___x_188_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_string_dec_eq(v___x_189_, v___x_197_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v___x_189_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec_ref_known(v___x_192_, 2);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_192_);
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_fileName(lean_object* v_self_205_){
_start:
{
lean_object* v_config_206_; lean_object* v_exeName_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_config_206_ = lean_ctor_get(v_self_205_, 2);
lean_inc(v_config_206_);
lean_dec_ref(v_self_205_);
v_exeName_207_ = lean_ctor_get(v_config_206_, 3);
lean_inc_ref(v_exeName_207_);
lean_dec(v_config_206_);
v___x_208_ = l_System_FilePath_exeExtension;
v___x_209_ = l_System_FilePath_addExtension(v_exeName_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_file(lean_object* v_self_210_){
_start:
{
lean_object* v_pkg_211_; lean_object* v_config_212_; lean_object* v_config_213_; lean_object* v_dir_214_; lean_object* v_buildDir_215_; lean_object* v_binDir_216_; lean_object* v_exeName_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_pkg_211_ = lean_ctor_get(v_self_210_, 0);
lean_inc_ref(v_pkg_211_);
v_config_212_ = lean_ctor_get(v_pkg_211_, 6);
lean_inc_ref(v_config_212_);
v_config_213_ = lean_ctor_get(v_self_210_, 2);
lean_inc(v_config_213_);
lean_dec_ref(v_self_210_);
v_dir_214_ = lean_ctor_get(v_pkg_211_, 4);
lean_inc_ref(v_dir_214_);
lean_dec_ref(v_pkg_211_);
v_buildDir_215_ = lean_ctor_get(v_config_212_, 5);
lean_inc_ref(v_buildDir_215_);
v_binDir_216_ = lean_ctor_get(v_config_212_, 8);
lean_inc_ref(v_binDir_216_);
lean_dec_ref(v_config_212_);
v_exeName_217_ = lean_ctor_get(v_config_213_, 3);
lean_inc_ref(v_exeName_217_);
lean_dec(v_config_213_);
v___x_218_ = l_System_FilePath_normalize(v_buildDir_215_);
v___x_219_ = l_Lake_joinRelative(v_dir_214_, v___x_218_);
v___x_220_ = l_System_FilePath_normalize(v_binDir_216_);
v___x_221_ = l_Lake_joinRelative(v___x_219_, v___x_220_);
v___x_222_ = l_System_FilePath_exeExtension;
v___x_223_ = l_System_FilePath_addExtension(v_exeName_217_, v___x_222_);
v___x_224_ = l_Lake_joinRelative(v___x_221_, v___x_223_);
return v___x_224_;
}
}
uint8_t l_Lake_LeanExe_supportInterpreter(lean_object* v_self_225_){
_start:
{
lean_object* v_config_226_; uint8_t v_supportInterpreter_227_; 
v_config_226_ = lean_ctor_get(v_self_225_, 2);
v_supportInterpreter_227_ = lean_ctor_get_uint8(v_config_226_, sizeof(void*)*7);
return v_supportInterpreter_227_;
}
}
LEAN_EXPORT void l_Lake_LeanExe_supportInterpreter_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_225_ = stack[0].m_obj;
uint8_t v_res_228_;
v_res_228_ = l_Lake_LeanExe_supportInterpreter(v_self_225_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_supportInterpreter___boxed(lean_object* v_self_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Lake_LeanExe_supportInterpreter(v_self_229_);
lean_dec_ref(v_self_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeOnlyLinkArgs(lean_object* v_self_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = l_System_Platform_isWindows;
if (v___x_251_ == 0)
{
lean_object* v_config_252_; uint8_t v_supportInterpreter_253_; 
v_config_252_ = lean_ctor_get(v_self_250_, 2);
v_supportInterpreter_253_ = lean_ctor_get_uint8(v_config_252_, sizeof(void*)*7);
if (v_supportInterpreter_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_Lake_LeanExe_exeOnlyLinkArgs___closed__0));
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = ((lean_object*)(l_Lake_LeanExe_exeOnlyLinkArgs___closed__2));
return v___x_255_;
}
}
else
{
lean_object* v___x_256_; 
v___x_256_ = ((lean_object*)(l_Lake_LeanExe_exeOnlyLinkArgs___closed__6));
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeOnlyLinkArgs___boxed(lean_object* v_self_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lake_LeanExe_exeOnlyLinkArgs(v_self_257_);
lean_dec_ref(v_self_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs(lean_object* v_self_259_){
_start:
{
lean_object* v_pkg_260_; lean_object* v_config_261_; lean_object* v_toLeanConfig_262_; lean_object* v_config_263_; lean_object* v_toLeanConfig_264_; lean_object* v_moreLinkArgs_265_; lean_object* v_moreLinkArgs_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_pkg_260_ = lean_ctor_get(v_self_259_, 0);
v_config_261_ = lean_ctor_get(v_pkg_260_, 6);
v_toLeanConfig_262_ = lean_ctor_get(v_config_261_, 1);
v_config_263_ = lean_ctor_get(v_self_259_, 2);
v_toLeanConfig_264_ = lean_ctor_get(v_config_263_, 0);
v_moreLinkArgs_265_ = lean_ctor_get(v_toLeanConfig_262_, 8);
v_moreLinkArgs_266_ = lean_ctor_get(v_toLeanConfig_264_, 8);
v___x_267_ = l_Lake_LeanExe_exeOnlyLinkArgs(v_self_259_);
v___x_268_ = l_Array_append___redArg(v___x_267_, v_moreLinkArgs_265_);
v___x_269_ = l_Array_append___redArg(v___x_268_, v_moreLinkArgs_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs___boxed(lean_object* v_self_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lake_LeanExe_linkArgs(v_self_270_);
lean_dec_ref(v_self_270_);
return v_res_271_;
}
}
uint8_t l_Lake_LeanExe_sharedLean(lean_object* v_self_272_){
_start:
{
lean_object* v_config_273_; uint8_t v_supportInterpreter_274_; uint8_t v___x_275_; uint8_t v___x_276_; 
v_config_273_ = lean_ctor_get(v_self_272_, 2);
v_supportInterpreter_274_ = lean_ctor_get_uint8(v_config_273_, sizeof(void*)*7);
v___x_275_ = l_System_Platform_isWindows;
v___x_276_ = lean_strict_and(v___x_275_, v_supportInterpreter_274_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lake_LeanExe_sharedLean_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_272_ = stack[0].m_obj;
uint8_t v_res_277_;
v_res_277_ = l_Lake_LeanExe_sharedLean(v_self_272_);
stack->m_num = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_sharedLean___boxed(lean_object* v_self_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lake_LeanExe_sharedLean(v_self_278_);
lean_dec_ref(v_self_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_weakLinkArgs(lean_object* v_self_281_){
_start:
{
lean_object* v_pkg_282_; lean_object* v_config_283_; lean_object* v_toLeanConfig_284_; lean_object* v_config_285_; lean_object* v_toLeanConfig_286_; lean_object* v_weakLinkArgs_287_; lean_object* v_weakLinkArgs_288_; lean_object* v___x_289_; 
v_pkg_282_ = lean_ctor_get(v_self_281_, 0);
v_config_283_ = lean_ctor_get(v_pkg_282_, 6);
v_toLeanConfig_284_ = lean_ctor_get(v_config_283_, 1);
lean_inc_ref(v_toLeanConfig_284_);
v_config_285_ = lean_ctor_get(v_self_281_, 2);
lean_inc(v_config_285_);
lean_dec_ref(v_self_281_);
v_toLeanConfig_286_ = lean_ctor_get(v_config_285_, 0);
lean_inc_ref(v_toLeanConfig_286_);
lean_dec(v_config_285_);
v_weakLinkArgs_287_ = lean_ctor_get(v_toLeanConfig_284_, 9);
lean_inc_ref(v_weakLinkArgs_287_);
lean_dec_ref(v_toLeanConfig_284_);
v_weakLinkArgs_288_ = lean_ctor_get(v_toLeanConfig_286_, 9);
lean_inc_ref(v_weakLinkArgs_288_);
lean_dec_ref(v_toLeanConfig_286_);
v___x_289_ = l_Array_append___redArg(v_weakLinkArgs_287_, v_weakLinkArgs_288_);
lean_dec_ref(v_weakLinkArgs_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs(lean_object* v_self_290_){
_start:
{
lean_object* v_config_291_; lean_object* v_toLeanConfig_292_; lean_object* v_moreLinkObjs_293_; 
v_config_291_ = lean_ctor_get(v_self_290_, 2);
v_toLeanConfig_292_ = lean_ctor_get(v_config_291_, 0);
v_moreLinkObjs_293_ = lean_ctor_get(v_toLeanConfig_292_, 6);
lean_inc_ref(v_moreLinkObjs_293_);
return v_moreLinkObjs_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs___boxed(lean_object* v_self_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_LeanExe_moreLinkObjs(v_self_294_);
lean_dec_ref(v_self_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs(lean_object* v_self_296_){
_start:
{
lean_object* v_config_297_; lean_object* v_toLeanConfig_298_; lean_object* v_moreLinkLibs_299_; 
v_config_297_ = lean_ctor_get(v_self_296_, 2);
v_toLeanConfig_298_ = lean_ctor_get(v_config_297_, 0);
v_moreLinkLibs_299_ = lean_ctor_get(v_toLeanConfig_298_, 7);
lean_inc_ref(v_moreLinkLibs_299_);
return v_moreLinkLibs_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs___boxed(lean_object* v_self_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lake_LeanExe_moreLinkLibs(v_self_300_);
lean_dec_ref(v_self_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(lean_object* v_mod_302_, lean_object* v_as_303_, lean_object* v_i_304_){
_start:
{
lean_object* v_zero_305_; uint8_t v_isZero_306_; 
v_zero_305_ = lean_unsigned_to_nat(0u);
v_isZero_306_ = lean_nat_dec_eq(v_i_304_, v_zero_305_);
if (v_isZero_306_ == 1)
{
lean_object* v___x_307_; 
lean_dec(v_i_304_);
v___x_307_ = lean_box(0);
return v___x_307_;
}
else
{
lean_object* v_one_308_; lean_object* v_n_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_one_308_ = lean_unsigned_to_nat(1u);
v_n_309_ = lean_nat_sub(v_i_304_, v_one_308_);
lean_dec(v_i_304_);
v___x_310_ = lean_array_fget_borrowed(v_as_303_, v_n_309_);
lean_inc(v___x_310_);
v___x_311_ = l_Lake_LeanExe_isRoot_x3f(v_mod_302_, v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
v_i_304_ = v_n_309_;
goto _start;
}
else
{
lean_dec(v_n_309_);
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_313_, lean_object* v_as_314_, lean_object* v_i_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_313_, v_as_314_, v_i_315_);
lean_dec_ref(v_as_314_);
lean_dec(v_mod_313_);
return v_res_316_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(lean_object* v_self_317_, lean_object* v_as_318_, size_t v_i_319_, size_t v_stop_320_, lean_object* v_b_321_){
_start:
{
lean_object* v___y_323_; uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_eq(v_i_319_, v_stop_320_);
if (v___x_327_ == 0)
{
lean_object* v_toConfigDecl_328_; lean_object* v_name_329_; lean_object* v_kind_330_; lean_object* v_config_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_toConfigDecl_328_ = lean_array_uget_borrowed(v_as_318_, v_i_319_);
v_name_329_ = lean_ctor_get(v_toConfigDecl_328_, 1);
v_kind_330_ = lean_ctor_get(v_toConfigDecl_328_, 2);
v_config_331_ = lean_ctor_get(v_toConfigDecl_328_, 3);
v___x_332_ = l_Lake_LeanExe_keyword;
v___x_333_ = lean_name_eq(v_kind_330_, v___x_332_);
if (v___x_333_ == 0)
{
v___y_323_ = v_b_321_;
goto v___jp_322_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_inc(v_config_331_);
lean_inc(v_name_329_);
lean_inc_ref(v_self_317_);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v_self_317_);
lean_ctor_set(v___x_334_, 1, v_name_329_);
lean_ctor_set(v___x_334_, 2, v_config_331_);
v___x_335_ = lean_array_push(v_b_321_, v___x_334_);
v___y_323_ = v___x_335_;
goto v___jp_322_;
}
}
else
{
lean_dec_ref(v_self_317_);
return v_b_321_;
}
v___jp_322_:
{
size_t v___x_324_; size_t v___x_325_; 
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_319_, v___x_324_);
v_i_319_ = v___x_325_;
v_b_321_ = v___y_323_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_317_ = stack[0].m_obj;
lean_object* v_as_318_ = stack[1].m_obj;
size_t v_i_319_ = stack[2].m_num;
size_t v_stop_320_ = stack[3].m_num;
lean_object* v_b_321_ = stack[4].m_obj;
lean_object* v_res_336_;
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_317_, v_as_318_, v_i_319_, v_stop_320_, v_b_321_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1___boxed(lean_object* v_self_337_, lean_object* v_as_338_, lean_object* v_i_339_, lean_object* v_stop_340_, lean_object* v_b_341_){
_start:
{
size_t v_i_boxed_342_; size_t v_stop_boxed_343_; lean_object* v_res_344_; 
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_stop_boxed_343_ = lean_unbox_usize(v_stop_340_);
lean_dec(v_stop_340_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_337_, v_as_338_, v_i_boxed_342_, v_stop_boxed_343_, v_b_341_);
lean_dec_ref(v_as_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetModule_x3f(lean_object* v_mod_345_, lean_object* v_self_346_){
_start:
{
lean_object* v___y_348_; lean_object* v_targetDecls_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_targetDecls_352_ = lean_ctor_get(v_self_346_, 15);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_355_ = lean_array_get_size(v_targetDecls_352_);
v___x_356_ = lean_nat_dec_lt(v___x_353_, v___x_355_);
if (v___x_356_ == 0)
{
v___y_348_ = v___x_354_;
goto v___jp_347_;
}
else
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((size_t)0ULL);
v___x_358_ = lean_usize_of_nat(v___x_355_);
lean_inc_ref(v_self_346_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_346_, v_targetDecls_352_, v___x_357_, v___x_358_, v___x_354_);
v___y_348_ = v___x_359_;
goto v___jp_347_;
}
v___jp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_array_get_size(v___y_348_);
v___x_350_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_345_, v___y_348_, v___x_349_);
lean_dec_ref(v___y_348_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = l_Lake_Package_findModule_x3f(v_mod_345_, v_self_346_);
return v___x_351_;
}
else
{
lean_dec_ref(v_self_346_);
lean_dec(v_mod_345_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(lean_object* v_mod_360_, lean_object* v_as_361_, lean_object* v_i_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_360_, v_as_361_, v_i_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_365_, lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(v_mod_365_, v_as_366_, v_i_367_, v_a_368_);
lean_dec_ref(v_as_366_);
lean_dec(v_mod_365_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(lean_object* v_path_370_, lean_object* v_as_371_, lean_object* v_i_372_){
_start:
{
lean_object* v_zero_373_; uint8_t v_isZero_374_; 
v_zero_373_ = lean_unsigned_to_nat(0u);
v_isZero_374_ = lean_nat_dec_eq(v_i_372_, v_zero_373_);
if (v_isZero_374_ == 1)
{
lean_object* v___x_375_; 
lean_dec(v_i_372_);
lean_dec_ref(v_path_370_);
v___x_375_ = lean_box(0);
return v___x_375_;
}
else
{
lean_object* v_one_376_; lean_object* v_n_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_one_376_ = lean_unsigned_to_nat(1u);
v_n_377_ = lean_nat_sub(v_i_372_, v_one_376_);
lean_dec(v_i_372_);
v___x_378_ = lean_array_fget_borrowed(v_as_371_, v_n_377_);
lean_inc(v___x_378_);
lean_inc_ref(v_path_370_);
v___x_379_ = l_Lake_LeanExe_isRootSrc_x3f(v_path_370_, v___x_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
v_i_372_ = v_n_377_;
goto _start;
}
else
{
lean_dec(v_n_377_);
lean_dec_ref(v_path_370_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg___boxed(lean_object* v_path_381_, lean_object* v_as_382_, lean_object* v_i_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_381_, v_as_382_, v_i_383_);
lean_dec_ref(v_as_382_);
return v_res_384_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(lean_object* v_self_388_, lean_object* v_as_389_, size_t v_i_390_, size_t v_stop_391_, lean_object* v_b_392_){
_start:
{
lean_object* v___y_394_; uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_eq(v_i_390_, v_stop_391_);
if (v___x_398_ == 0)
{
lean_object* v_toConfigDecl_399_; lean_object* v_name_400_; lean_object* v_kind_401_; lean_object* v_config_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_toConfigDecl_399_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v_name_400_ = lean_ctor_get(v_toConfigDecl_399_, 1);
v_kind_401_ = lean_ctor_get(v_toConfigDecl_399_, 2);
v_config_402_ = lean_ctor_get(v_toConfigDecl_399_, 3);
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1));
v___x_404_ = lean_name_eq(v_kind_401_, v___x_403_);
if (v___x_404_ == 0)
{
v___y_394_ = v_b_392_;
goto v___jp_393_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_inc(v_config_402_);
lean_inc(v_name_400_);
lean_inc_ref(v_self_388_);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v_self_388_);
lean_ctor_set(v___x_405_, 1, v_name_400_);
lean_ctor_set(v___x_405_, 2, v_config_402_);
v___x_406_ = lean_array_push(v_b_392_, v___x_405_);
v___y_394_ = v___x_406_;
goto v___jp_393_;
}
}
else
{
lean_dec_ref(v_self_388_);
return v_b_392_;
}
v___jp_393_:
{
size_t v___x_395_; size_t v___x_396_; 
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_390_, v___x_395_);
v_i_390_ = v___x_396_;
v_b_392_ = v___y_394_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_388_ = stack[0].m_obj;
lean_object* v_as_389_ = stack[1].m_obj;
size_t v_i_390_ = stack[2].m_num;
size_t v_stop_391_ = stack[3].m_num;
lean_object* v_b_392_ = stack[4].m_obj;
lean_object* v_res_407_;
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_388_, v_as_389_, v_i_390_, v_stop_391_, v_b_392_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___boxed(lean_object* v_self_408_, lean_object* v_as_409_, lean_object* v_i_410_, lean_object* v_stop_411_, lean_object* v_b_412_){
_start:
{
size_t v_i_boxed_413_; size_t v_stop_boxed_414_; lean_object* v_res_415_; 
v_i_boxed_413_ = lean_unbox_usize(v_i_410_);
lean_dec(v_i_410_);
v_stop_boxed_414_ = lean_unbox_usize(v_stop_411_);
lean_dec(v_stop_411_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_408_, v_as_409_, v_i_boxed_413_, v_stop_boxed_414_, v_b_412_);
lean_dec_ref(v_as_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(lean_object* v_path_416_, lean_object* v_as_417_, lean_object* v_i_418_){
_start:
{
lean_object* v_zero_419_; uint8_t v_isZero_420_; 
v_zero_419_ = lean_unsigned_to_nat(0u);
v_isZero_420_ = lean_nat_dec_eq(v_i_418_, v_zero_419_);
if (v_isZero_420_ == 1)
{
lean_object* v___x_421_; 
lean_dec(v_i_418_);
lean_dec_ref(v_path_416_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
else
{
lean_object* v_one_422_; lean_object* v_n_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_one_422_ = lean_unsigned_to_nat(1u);
v_n_423_ = lean_nat_sub(v_i_418_, v_one_422_);
lean_dec(v_i_418_);
v___x_424_ = lean_array_fget_borrowed(v_as_417_, v_n_423_);
lean_inc(v___x_424_);
lean_inc_ref(v_path_416_);
v___x_425_ = l_Lake_LeanLib_findModuleBySrc_x3f(v_path_416_, v___x_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
v_i_418_ = v_n_423_;
goto _start;
}
else
{
lean_dec(v_n_423_);
lean_dec_ref(v_path_416_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object* v_path_427_, lean_object* v_as_428_, lean_object* v_i_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_427_, v_as_428_, v_i_429_);
lean_dec_ref(v_as_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModuleBySrc_x3f(lean_object* v_path_431_, lean_object* v_self_432_){
_start:
{
lean_object* v___y_434_; lean_object* v_targetDecls_437_; lean_object* v___y_439_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_targetDecls_437_ = lean_ctor_get(v_self_432_, 15);
lean_inc_ref(v_targetDecls_437_);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_451_ = lean_array_get_size(v_targetDecls_437_);
v___x_452_ = lean_nat_dec_lt(v___x_449_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_439_ = v___x_450_;
goto v___jp_438_;
}
else
{
size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((size_t)0ULL);
v___x_454_ = lean_usize_of_nat(v___x_451_);
lean_inc_ref(v_self_432_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_432_, v_targetDecls_437_, v___x_453_, v___x_454_, v___x_450_);
v___y_439_ = v___x_455_;
goto v___jp_438_;
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_array_get_size(v___y_434_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_431_, v___y_434_, v___x_435_);
lean_dec_ref(v___y_434_);
return v___x_436_;
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_array_get_size(v___y_439_);
lean_inc_ref(v_path_431_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_431_, v___y_439_, v___x_440_);
lean_dec_ref(v___y_439_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_444_ = lean_array_get_size(v_targetDecls_437_);
v___x_445_ = lean_nat_dec_lt(v___x_442_, v___x_444_);
if (v___x_445_ == 0)
{
lean_dec_ref(v_targetDecls_437_);
lean_dec_ref(v_self_432_);
v___y_434_ = v___x_443_;
goto v___jp_433_;
}
else
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((size_t)0ULL);
v___x_447_ = lean_usize_of_nat(v___x_444_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_432_, v_targetDecls_437_, v___x_446_, v___x_447_, v___x_443_);
lean_dec_ref(v_targetDecls_437_);
v___y_434_ = v___x_448_;
goto v___jp_433_;
}
}
else
{
lean_dec_ref(v_targetDecls_437_);
lean_dec_ref(v_self_432_);
lean_dec_ref(v_path_431_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(lean_object* v_path_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_456_, v_as_457_, v_i_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_461_, lean_object* v_as_462_, lean_object* v_i_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(v_path_461_, v_as_462_, v_i_463_, v_a_464_);
lean_dec_ref(v_as_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(lean_object* v_path_466_, lean_object* v_as_467_, lean_object* v_i_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_466_, v_as_467_, v_i_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___boxed(lean_object* v_path_471_, lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(v_path_471_, v_as_472_, v_i_473_, v_a_474_);
lean_dec_ref(v_as_472_);
return v_res_475_;
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
