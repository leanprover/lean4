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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Package_findModule_x3f(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
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
static const lean_string_object l_Lake_LeanExe_linkArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "-Wl,--whole-archive"};
static const lean_object* l_Lake_LeanExe_linkArgs___closed__0 = (const lean_object*)&l_Lake_LeanExe_linkArgs___closed__0_value;
static const lean_string_object l_Lake_LeanExe_linkArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "-lleanmanifest"};
static const lean_object* l_Lake_LeanExe_linkArgs___closed__1 = (const lean_object*)&l_Lake_LeanExe_linkArgs___closed__1_value;
static const lean_string_object l_Lake_LeanExe_linkArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-Wl,--no-whole-archive"};
static const lean_object* l_Lake_LeanExe_linkArgs___closed__2 = (const lean_object*)&l_Lake_LeanExe_linkArgs___closed__2_value;
static const lean_array_object l_Lake_LeanExe_linkArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_LeanExe_linkArgs___closed__0_value),((lean_object*)&l_Lake_LeanExe_linkArgs___closed__1_value),((lean_object*)&l_Lake_LeanExe_linkArgs___closed__2_value)}};
static const lean_object* l_Lake_LeanExe_linkArgs___closed__3 = (const lean_object*)&l_Lake_LeanExe_linkArgs___closed__3_value;
static const lean_string_object l_Lake_LeanExe_linkArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-rdynamic"};
static const lean_object* l_Lake_LeanExe_linkArgs___closed__4 = (const lean_object*)&l_Lake_LeanExe_linkArgs___closed__4_value;
static const lean_array_object l_Lake_LeanExe_linkArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_LeanExe_linkArgs___closed__4_value)}};
static const lean_object* l_Lake_LeanExe_linkArgs___closed__5 = (const lean_object*)&l_Lake_LeanExe_linkArgs___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs(lean_object*);
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
v_targetDecls_38_ = lean_ctor_get(v_self_37_, 14);
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
lean_object* v___x_44_; lean_object* v___f_45_; uint8_t v___x_46_; 
v___x_44_ = l_Lake_LeanExe_keyword;
v___f_45_ = lean_alloc_closure((void*)(l_Lake_Package_leanExes___lam__0___boxed), 4, 2);
lean_closure_set(v___f_45_, 0, v___x_44_);
lean_closure_set(v___f_45_, 1, v_self_37_);
v___x_46_ = lean_nat_dec_le(v___x_41_, v___x_41_);
if (v___x_46_ == 0)
{
if (v___x_43_ == 0)
{
lean_dec_ref(v___f_45_);
lean_dec_ref(v_targetDecls_38_);
return v___x_40_;
}
else
{
size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_41_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_42_, v___f_45_, v_targetDecls_38_, v___x_47_, v___x_48_, v___x_40_);
return v___x_49_;
}
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_41_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_42_, v___f_45_, v_targetDecls_38_, v___x_50_, v___x_51_, v___x_40_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanExe_x3f(lean_object* v_name_53_, lean_object* v_self_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lake_Package_findTargetDecl_x3f(v_name_53_, v_self_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v___x_56_; 
lean_dec_ref(v_self_54_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_71_; 
v_val_57_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_71_ == 0)
{
v___x_59_ = v___x_55_;
v_isShared_60_ = v_isSharedCheck_71_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_val_57_);
lean_dec(v___x_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_71_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_name_61_; lean_object* v_kind_62_; lean_object* v_config_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_name_61_ = lean_ctor_get(v_val_57_, 1);
lean_inc(v_name_61_);
v_kind_62_ = lean_ctor_get(v_val_57_, 2);
lean_inc(v_kind_62_);
v_config_63_ = lean_ctor_get(v_val_57_, 3);
lean_inc(v_config_63_);
lean_dec(v_val_57_);
v___x_64_ = l_Lake_LeanExe_keyword;
v___x_65_ = lean_name_eq(v_kind_62_, v___x_64_);
lean_dec(v_kind_62_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
lean_dec(v_config_63_);
lean_dec(v_name_61_);
lean_del_object(v___x_59_);
lean_dec_ref(v_self_54_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v_self_54_);
lean_ctor_set(v___x_67_, 1, v_name_61_);
lean_ctor_set(v___x_67_, 2, v_config_63_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_67_);
v___x_69_ = v___x_59_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanExe_x3f___boxed(lean_object* v_name_72_, lean_object* v_self_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lake_Package_findLeanExe_x3f(v_name_72_, v_self_73_);
lean_dec(v_name_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(size_t v_sz_75_, size_t v_i_76_, lean_object* v_bs_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = lean_usize_dec_lt(v_i_76_, v_sz_75_);
if (v___x_78_ == 0)
{
return v_bs_77_;
}
else
{
lean_object* v_v_79_; lean_object* v___x_80_; lean_object* v_bs_x27_81_; lean_object* v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; 
v_v_79_ = lean_array_uget(v_bs_77_, v_i_76_);
v___x_80_ = lean_unsigned_to_nat(0u);
v_bs_x27_81_ = lean_array_uset(v_bs_77_, v_i_76_, v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_v_79_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_add(v_i_76_, v___x_83_);
v___x_85_ = lean_array_uset(v_bs_x27_81_, v_i_76_, v___x_82_);
v_i_76_ = v___x_84_;
v_bs_77_ = v___x_85_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0___boxed(lean_object* v_sz_87_, lean_object* v_i_88_, lean_object* v_bs_89_){
_start:
{
size_t v_sz_boxed_90_; size_t v_i_boxed_91_; lean_object* v_res_92_; 
v_sz_boxed_90_ = lean_unbox_usize(v_sz_87_);
lean_dec(v_sz_87_);
v_i_boxed_91_ = lean_unbox_usize(v_i_88_);
lean_dec(v_i_88_);
v_res_92_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_boxed_90_, v_i_boxed_91_, v_bs_89_);
return v_res_92_;
}
}
static size_t _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_95_; size_t v_sz_96_; 
v___x_95_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v_sz_96_ = lean_array_size(v___x_95_);
return v_sz_96_;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2(void){
_start:
{
lean_object* v___x_97_; size_t v___x_98_; size_t v_sz_99_; lean_object* v___x_100_; 
v___x_97_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v___x_98_ = ((size_t)0ULL);
v_sz_99_ = lean_usize_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__1);
v___x_100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LeanExeConfig_toLeanLibConfig_spec__0(v_sz_99_, v___x_98_, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = l_Lake_LeanLib_leanArtsFacet;
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_104_ = lean_array_push(v___x_103_, v___x_101_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object* v_self_105_){
_start:
{
lean_object* v_toLeanConfig_106_; lean_object* v_srcDir_107_; lean_object* v_exeName_108_; lean_object* v_needs_109_; lean_object* v_extraDepTargets_110_; lean_object* v_nativeFacets_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_toLeanConfig_106_ = lean_ctor_get(v_self_105_, 0);
v_srcDir_107_ = lean_ctor_get(v_self_105_, 1);
v_exeName_108_ = lean_ctor_get(v_self_105_, 3);
v_needs_109_ = lean_ctor_get(v_self_105_, 4);
v_extraDepTargets_110_ = lean_ctor_get(v_self_105_, 5);
v_nativeFacets_111_ = lean_ctor_get(v_self_105_, 6);
v___x_112_ = ((lean_object*)(l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__0));
v___x_113_ = lean_obj_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__2);
v___x_114_ = 0;
v___x_115_ = lean_obj_once(&l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3, &l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3_once, _init_l_Lake_LeanExeConfig_toLeanLibConfig___redArg___closed__3);
lean_inc_ref(v_nativeFacets_111_);
lean_inc_ref(v_extraDepTargets_110_);
lean_inc_ref(v_needs_109_);
lean_inc_ref(v_exeName_108_);
lean_inc_ref(v_srcDir_107_);
lean_inc_ref(v_toLeanConfig_106_);
v___x_116_ = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(v___x_116_, 0, v_toLeanConfig_106_);
lean_ctor_set(v___x_116_, 1, v_srcDir_107_);
lean_ctor_set(v___x_116_, 2, v___x_112_);
lean_ctor_set(v___x_116_, 3, v___x_113_);
lean_ctor_set(v___x_116_, 4, v_exeName_108_);
lean_ctor_set(v___x_116_, 5, v_needs_109_);
lean_ctor_set(v___x_116_, 6, v_extraDepTargets_110_);
lean_ctor_set(v___x_116_, 7, v___x_115_);
lean_ctor_set(v___x_116_, 8, v_nativeFacets_111_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*9, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*9 + 1, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*9 + 2, v___x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg___boxed(lean_object* v_self_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_117_);
lean_dec_ref(v_self_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig(lean_object* v_n_119_, lean_object* v_self_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_self_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___boxed(lean_object* v_n_122_, lean_object* v_self_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lake_LeanExeConfig_toLeanLibConfig(v_n_122_, v_self_123_);
lean_dec_ref(v_self_123_);
lean_dec(v_n_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_config(lean_object* v_self_125_){
_start:
{
lean_object* v_config_126_; 
v_config_126_ = lean_ctor_get(v_self_125_, 2);
lean_inc(v_config_126_);
return v_config_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_config___boxed(lean_object* v_self_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_LeanExe_config(v_self_127_);
lean_dec_ref(v_self_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_toLeanLib(lean_object* v_self_129_){
_start:
{
lean_object* v_pkg_130_; lean_object* v_name_131_; lean_object* v_config_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_pkg_130_ = lean_ctor_get(v_self_129_, 0);
v_name_131_ = lean_ctor_get(v_self_129_, 1);
v_config_132_ = lean_ctor_get(v_self_129_, 2);
v_isSharedCheck_140_ = !lean_is_exclusive(v_self_129_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v_self_129_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_config_132_);
lean_inc(v_name_131_);
lean_inc(v_pkg_130_);
lean_dec(v_self_129_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_132_);
lean_dec(v_config_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 2, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_pkg_130_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_name_131_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v___x_136_);
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
LEAN_EXPORT lean_object* l_Lake_LeanExe_root(lean_object* v_self_141_){
_start:
{
lean_object* v_config_142_; lean_object* v_pkg_143_; lean_object* v_name_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_154_; 
v_config_142_ = lean_ctor_get(v_self_141_, 2);
v_pkg_143_ = lean_ctor_get(v_self_141_, 0);
v_name_144_ = lean_ctor_get(v_self_141_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_self_141_);
if (v_isSharedCheck_154_ == 0)
{
v___x_146_ = v_self_141_;
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_config_142_);
lean_inc(v_name_144_);
lean_inc(v_pkg_143_);
lean_dec(v_self_141_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_root_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v_root_148_ = lean_ctor_get(v_config_142_, 2);
lean_inc(v_root_148_);
v___x_149_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_142_);
lean_dec(v_config_142_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 2, v___x_149_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_pkg_143_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_name_144_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v___x_149_);
v___x_151_ = v_reuseFailAlloc_153_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_root_148_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f(lean_object* v_name_155_, lean_object* v_self_156_){
_start:
{
lean_object* v_config_157_; lean_object* v_pkg_158_; lean_object* v_name_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_172_; 
v_config_157_ = lean_ctor_get(v_self_156_, 2);
v_pkg_158_ = lean_ctor_get(v_self_156_, 0);
v_name_159_ = lean_ctor_get(v_self_156_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_self_156_);
if (v_isSharedCheck_172_ == 0)
{
v___x_161_ = v_self_156_;
v_isShared_162_ = v_isSharedCheck_172_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_config_157_);
lean_inc(v_name_159_);
lean_inc(v_pkg_158_);
lean_dec(v_self_156_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_172_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_root_163_; uint8_t v___x_164_; 
v_root_163_ = lean_ctor_get(v_config_157_, 2);
lean_inc(v_root_163_);
v___x_164_ = lean_name_eq(v_name_155_, v_root_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_dec(v_root_163_);
lean_del_object(v___x_161_);
lean_dec(v_name_159_);
lean_dec_ref(v_pkg_158_);
lean_dec(v_config_157_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_157_);
lean_dec(v_config_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 2, v___x_166_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_pkg_158_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_name_159_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v___x_166_);
v___x_168_ = v_reuseFailAlloc_171_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_root_163_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRoot_x3f___boxed(lean_object* v_name_173_, lean_object* v_self_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lake_LeanExe_isRoot_x3f(v_name_173_, v_self_174_);
lean_dec(v_name_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_isRootSrc_x3f(lean_object* v_path_177_, lean_object* v_self_178_){
_start:
{
lean_object* v_config_179_; lean_object* v_pkg_180_; lean_object* v_config_181_; lean_object* v_name_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_205_; 
v_config_179_ = lean_ctor_get(v_self_178_, 2);
lean_inc(v_config_179_);
v_pkg_180_ = lean_ctor_get(v_self_178_, 0);
lean_inc_ref(v_pkg_180_);
v_config_181_ = lean_ctor_get(v_pkg_180_, 6);
v_name_182_ = lean_ctor_get(v_self_178_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_self_178_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; 
v_unused_206_ = lean_ctor_get(v_self_178_, 2);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_self_178_, 0);
lean_dec(v_unused_207_);
v___x_184_ = v_self_178_;
v_isShared_185_ = v_isSharedCheck_205_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_name_182_);
lean_dec(v_self_178_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_205_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_root_186_; lean_object* v_dir_187_; lean_object* v_srcDir_188_; lean_object* v___x_189_; lean_object* v_srcDir_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v_root_186_ = lean_ctor_get(v_config_179_, 2);
lean_inc(v_root_186_);
v_dir_187_ = lean_ctor_get(v_pkg_180_, 4);
lean_inc_ref(v_dir_187_);
v_srcDir_188_ = lean_ctor_get(v_config_181_, 4);
lean_inc_ref(v_srcDir_188_);
v___x_189_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_179_);
lean_dec(v_config_179_);
v_srcDir_190_ = lean_ctor_get(v___x_189_, 1);
lean_inc_ref(v_srcDir_190_);
v___x_191_ = ((lean_object*)(l_Lake_LeanExe_isRootSrc_x3f___closed__0));
v___x_192_ = l_System_FilePath_withExtension(v_path_177_, v___x_191_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 2, v___x_189_);
v___x_194_ = v___x_184_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_pkg_180_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_name_182_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v___x_189_);
v___x_194_ = v_reuseFailAlloc_204_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
lean_inc(v_root_186_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_root_186_);
v___x_196_ = l_System_FilePath_normalize(v_srcDir_188_);
v___x_197_ = l_Lake_joinRelative(v_dir_187_, v___x_196_);
v___x_198_ = l_System_FilePath_normalize(v_srcDir_190_);
v___x_199_ = l_Lake_joinRelative(v___x_197_, v___x_198_);
v___x_200_ = l_Lean_modToFilePath(v___x_199_, v_root_186_, v___x_191_);
lean_dec_ref(v___x_199_);
v___x_201_ = lean_string_dec_eq(v___x_192_, v___x_200_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_192_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec_ref(v___x_195_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_195_);
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_fileName(lean_object* v_self_208_){
_start:
{
lean_object* v_config_209_; lean_object* v_exeName_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_config_209_ = lean_ctor_get(v_self_208_, 2);
lean_inc(v_config_209_);
lean_dec_ref(v_self_208_);
v_exeName_210_ = lean_ctor_get(v_config_209_, 3);
lean_inc_ref(v_exeName_210_);
lean_dec(v_config_209_);
v___x_211_ = l_System_FilePath_exeExtension;
v___x_212_ = l_System_FilePath_addExtension(v_exeName_210_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_file(lean_object* v_self_213_){
_start:
{
lean_object* v_pkg_214_; lean_object* v_config_215_; lean_object* v_config_216_; lean_object* v_dir_217_; lean_object* v_buildDir_218_; lean_object* v_binDir_219_; lean_object* v_exeName_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_pkg_214_ = lean_ctor_get(v_self_213_, 0);
lean_inc_ref(v_pkg_214_);
v_config_215_ = lean_ctor_get(v_pkg_214_, 6);
lean_inc_ref(v_config_215_);
v_config_216_ = lean_ctor_get(v_self_213_, 2);
lean_inc(v_config_216_);
lean_dec_ref(v_self_213_);
v_dir_217_ = lean_ctor_get(v_pkg_214_, 4);
lean_inc_ref(v_dir_217_);
lean_dec_ref(v_pkg_214_);
v_buildDir_218_ = lean_ctor_get(v_config_215_, 5);
lean_inc_ref(v_buildDir_218_);
v_binDir_219_ = lean_ctor_get(v_config_215_, 8);
lean_inc_ref(v_binDir_219_);
lean_dec_ref(v_config_215_);
v_exeName_220_ = lean_ctor_get(v_config_216_, 3);
lean_inc_ref(v_exeName_220_);
lean_dec(v_config_216_);
v___x_221_ = l_System_FilePath_normalize(v_buildDir_218_);
v___x_222_ = l_Lake_joinRelative(v_dir_217_, v___x_221_);
v___x_223_ = l_System_FilePath_normalize(v_binDir_219_);
v___x_224_ = l_Lake_joinRelative(v___x_222_, v___x_223_);
v___x_225_ = l_System_FilePath_exeExtension;
v___x_226_ = l_System_FilePath_addExtension(v_exeName_220_, v___x_225_);
v___x_227_ = l_Lake_joinRelative(v___x_224_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanExe_supportInterpreter(lean_object* v_self_228_){
_start:
{
lean_object* v_config_229_; uint8_t v_supportInterpreter_230_; 
v_config_229_ = lean_ctor_get(v_self_228_, 2);
v_supportInterpreter_230_ = lean_ctor_get_uint8(v_config_229_, sizeof(void*)*7);
return v_supportInterpreter_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_supportInterpreter___boxed(lean_object* v_self_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lake_LeanExe_supportInterpreter(v_self_231_);
lean_dec_ref(v_self_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_linkArgs(lean_object* v_self_250_){
_start:
{
lean_object* v_pkg_251_; lean_object* v_config_252_; lean_object* v_toLeanConfig_253_; lean_object* v_config_254_; lean_object* v_toLeanConfig_255_; lean_object* v_moreLinkArgs_256_; uint8_t v_supportInterpreter_257_; lean_object* v_moreLinkArgs_258_; lean_object* v_linkArgs_259_; 
v_pkg_251_ = lean_ctor_get(v_self_250_, 0);
v_config_252_ = lean_ctor_get(v_pkg_251_, 6);
v_toLeanConfig_253_ = lean_ctor_get(v_config_252_, 1);
lean_inc_ref(v_toLeanConfig_253_);
v_config_254_ = lean_ctor_get(v_self_250_, 2);
lean_inc(v_config_254_);
lean_dec_ref(v_self_250_);
v_toLeanConfig_255_ = lean_ctor_get(v_config_254_, 0);
lean_inc_ref(v_toLeanConfig_255_);
v_moreLinkArgs_256_ = lean_ctor_get(v_toLeanConfig_253_, 8);
lean_inc_ref(v_moreLinkArgs_256_);
lean_dec_ref(v_toLeanConfig_253_);
v_supportInterpreter_257_ = lean_ctor_get_uint8(v_config_254_, sizeof(void*)*7);
lean_dec(v_config_254_);
v_moreLinkArgs_258_ = lean_ctor_get(v_toLeanConfig_255_, 8);
lean_inc_ref(v_moreLinkArgs_258_);
lean_dec_ref(v_toLeanConfig_255_);
v_linkArgs_259_ = l_Array_append___redArg(v_moreLinkArgs_256_, v_moreLinkArgs_258_);
lean_dec_ref(v_moreLinkArgs_258_);
if (v_supportInterpreter_257_ == 0)
{
goto v___jp_260_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = l_System_Platform_isWindows;
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v_linkArgs_266_; 
v___x_265_ = ((lean_object*)(l_Lake_LeanExe_linkArgs___closed__5));
v_linkArgs_266_ = l_Array_append___redArg(v___x_265_, v_linkArgs_259_);
lean_dec_ref(v_linkArgs_259_);
return v_linkArgs_266_;
}
else
{
goto v___jp_260_;
}
}
v___jp_260_:
{
uint8_t v___x_261_; 
v___x_261_ = l_System_Platform_isWindows;
if (v___x_261_ == 0)
{
return v_linkArgs_259_;
}
else
{
lean_object* v___x_262_; lean_object* v_linkArgs_263_; 
v___x_262_ = ((lean_object*)(l_Lake_LeanExe_linkArgs___closed__3));
v_linkArgs_263_ = l_Array_append___redArg(v_linkArgs_259_, v___x_262_);
return v_linkArgs_263_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanExe_sharedLean(lean_object* v_self_267_){
_start:
{
lean_object* v_config_268_; uint8_t v_supportInterpreter_269_; uint8_t v___x_270_; uint8_t v___x_271_; 
v_config_268_ = lean_ctor_get(v_self_267_, 2);
v_supportInterpreter_269_ = lean_ctor_get_uint8(v_config_268_, sizeof(void*)*7);
v___x_270_ = l_System_Platform_isWindows;
v___x_271_ = lean_strict_and(v___x_270_, v_supportInterpreter_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_sharedLean___boxed(lean_object* v_self_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Lake_LeanExe_sharedLean(v_self_272_);
lean_dec_ref(v_self_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_weakLinkArgs(lean_object* v_self_275_){
_start:
{
lean_object* v_pkg_276_; lean_object* v_config_277_; lean_object* v_toLeanConfig_278_; lean_object* v_config_279_; lean_object* v_toLeanConfig_280_; lean_object* v_weakLinkArgs_281_; lean_object* v_weakLinkArgs_282_; lean_object* v___x_283_; 
v_pkg_276_ = lean_ctor_get(v_self_275_, 0);
v_config_277_ = lean_ctor_get(v_pkg_276_, 6);
v_toLeanConfig_278_ = lean_ctor_get(v_config_277_, 1);
lean_inc_ref(v_toLeanConfig_278_);
v_config_279_ = lean_ctor_get(v_self_275_, 2);
lean_inc(v_config_279_);
lean_dec_ref(v_self_275_);
v_toLeanConfig_280_ = lean_ctor_get(v_config_279_, 0);
lean_inc_ref(v_toLeanConfig_280_);
lean_dec(v_config_279_);
v_weakLinkArgs_281_ = lean_ctor_get(v_toLeanConfig_278_, 9);
lean_inc_ref(v_weakLinkArgs_281_);
lean_dec_ref(v_toLeanConfig_278_);
v_weakLinkArgs_282_ = lean_ctor_get(v_toLeanConfig_280_, 9);
lean_inc_ref(v_weakLinkArgs_282_);
lean_dec_ref(v_toLeanConfig_280_);
v___x_283_ = l_Array_append___redArg(v_weakLinkArgs_281_, v_weakLinkArgs_282_);
lean_dec_ref(v_weakLinkArgs_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs(lean_object* v_self_284_){
_start:
{
lean_object* v_config_285_; lean_object* v_toLeanConfig_286_; lean_object* v_moreLinkObjs_287_; 
v_config_285_ = lean_ctor_get(v_self_284_, 2);
v_toLeanConfig_286_ = lean_ctor_get(v_config_285_, 0);
v_moreLinkObjs_287_ = lean_ctor_get(v_toLeanConfig_286_, 6);
lean_inc_ref(v_moreLinkObjs_287_);
return v_moreLinkObjs_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkObjs___boxed(lean_object* v_self_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_LeanExe_moreLinkObjs(v_self_288_);
lean_dec_ref(v_self_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs(lean_object* v_self_290_){
_start:
{
lean_object* v_config_291_; lean_object* v_toLeanConfig_292_; lean_object* v_moreLinkLibs_293_; 
v_config_291_ = lean_ctor_get(v_self_290_, 2);
v_toLeanConfig_292_ = lean_ctor_get(v_config_291_, 0);
v_moreLinkLibs_293_ = lean_ctor_get(v_toLeanConfig_292_, 7);
lean_inc_ref(v_moreLinkLibs_293_);
return v_moreLinkLibs_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_moreLinkLibs___boxed(lean_object* v_self_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_LeanExe_moreLinkLibs(v_self_294_);
lean_dec_ref(v_self_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(lean_object* v_mod_296_, lean_object* v_as_297_, lean_object* v_i_298_){
_start:
{
lean_object* v_zero_299_; uint8_t v_isZero_300_; 
v_zero_299_ = lean_unsigned_to_nat(0u);
v_isZero_300_ = lean_nat_dec_eq(v_i_298_, v_zero_299_);
if (v_isZero_300_ == 1)
{
lean_object* v___x_301_; 
lean_dec(v_i_298_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_one_302_; lean_object* v_n_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_one_302_ = lean_unsigned_to_nat(1u);
v_n_303_ = lean_nat_sub(v_i_298_, v_one_302_);
lean_dec(v_i_298_);
v___x_304_ = lean_array_fget_borrowed(v_as_297_, v_n_303_);
lean_inc(v___x_304_);
v___x_305_ = l_Lake_LeanExe_isRoot_x3f(v_mod_296_, v___x_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
v_i_298_ = v_n_303_;
goto _start;
}
else
{
lean_dec(v_n_303_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_307_, lean_object* v_as_308_, lean_object* v_i_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_307_, v_as_308_, v_i_309_);
lean_dec_ref(v_as_308_);
lean_dec(v_mod_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(lean_object* v_self_311_, lean_object* v_as_312_, size_t v_i_313_, size_t v_stop_314_, lean_object* v_b_315_){
_start:
{
lean_object* v___y_317_; uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_eq(v_i_313_, v_stop_314_);
if (v___x_321_ == 0)
{
lean_object* v_toConfigDecl_322_; lean_object* v_name_323_; lean_object* v_kind_324_; lean_object* v_config_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_toConfigDecl_322_ = lean_array_uget_borrowed(v_as_312_, v_i_313_);
v_name_323_ = lean_ctor_get(v_toConfigDecl_322_, 1);
v_kind_324_ = lean_ctor_get(v_toConfigDecl_322_, 2);
v_config_325_ = lean_ctor_get(v_toConfigDecl_322_, 3);
v___x_326_ = l_Lake_LeanExe_keyword;
v___x_327_ = lean_name_eq(v_kind_324_, v___x_326_);
if (v___x_327_ == 0)
{
v___y_317_ = v_b_315_;
goto v___jp_316_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc(v_config_325_);
lean_inc(v_name_323_);
lean_inc_ref(v_self_311_);
v___x_328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_328_, 0, v_self_311_);
lean_ctor_set(v___x_328_, 1, v_name_323_);
lean_ctor_set(v___x_328_, 2, v_config_325_);
v___x_329_ = lean_array_push(v_b_315_, v___x_328_);
v___y_317_ = v___x_329_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref(v_self_311_);
return v_b_315_;
}
v___jp_316_:
{
size_t v___x_318_; size_t v___x_319_; 
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_313_, v___x_318_);
v_i_313_ = v___x_319_;
v_b_315_ = v___y_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1___boxed(lean_object* v_self_330_, lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_stop_333_, lean_object* v_b_334_){
_start:
{
size_t v_i_boxed_335_; size_t v_stop_boxed_336_; lean_object* v_res_337_; 
v_i_boxed_335_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_stop_boxed_336_ = lean_unbox_usize(v_stop_333_);
lean_dec(v_stop_333_);
v_res_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_330_, v_as_331_, v_i_boxed_335_, v_stop_boxed_336_, v_b_334_);
lean_dec_ref(v_as_331_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetModule_x3f(lean_object* v_mod_338_, lean_object* v_self_339_){
_start:
{
lean_object* v___y_341_; lean_object* v_targetDecls_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_targetDecls_345_ = lean_ctor_get(v_self_339_, 14);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_348_ = lean_array_get_size(v_targetDecls_345_);
v___x_349_ = lean_nat_dec_lt(v___x_346_, v___x_348_);
if (v___x_349_ == 0)
{
v___y_341_ = v___x_347_;
goto v___jp_340_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = lean_nat_dec_le(v___x_348_, v___x_348_);
if (v___x_350_ == 0)
{
if (v___x_349_ == 0)
{
v___y_341_ = v___x_347_;
goto v___jp_340_;
}
else
{
size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((size_t)0ULL);
v___x_352_ = lean_usize_of_nat(v___x_348_);
lean_inc_ref(v_self_339_);
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_339_, v_targetDecls_345_, v___x_351_, v___x_352_, v___x_347_);
v___y_341_ = v___x_353_;
goto v___jp_340_;
}
}
else
{
size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = ((size_t)0ULL);
v___x_355_ = lean_usize_of_nat(v___x_348_);
lean_inc_ref(v_self_339_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_339_, v_targetDecls_345_, v___x_354_, v___x_355_, v___x_347_);
v___y_341_ = v___x_356_;
goto v___jp_340_;
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_array_get_size(v___y_341_);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_338_, v___y_341_, v___x_342_);
lean_dec_ref(v___y_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
v___x_344_ = l_Lake_Package_findModule_x3f(v_mod_338_, v_self_339_);
return v___x_344_;
}
else
{
lean_dec_ref(v_self_339_);
lean_dec(v_mod_338_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(lean_object* v_mod_357_, lean_object* v_as_358_, lean_object* v_i_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___redArg(v_mod_357_, v_as_358_, v_i_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_362_, lean_object* v_as_363_, lean_object* v_i_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findTargetModule_x3f_spec__0(v_mod_362_, v_as_363_, v_i_364_, v_a_365_);
lean_dec_ref(v_as_363_);
lean_dec(v_mod_362_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(lean_object* v_path_367_, lean_object* v_as_368_, lean_object* v_i_369_){
_start:
{
lean_object* v_zero_370_; uint8_t v_isZero_371_; 
v_zero_370_ = lean_unsigned_to_nat(0u);
v_isZero_371_ = lean_nat_dec_eq(v_i_369_, v_zero_370_);
if (v_isZero_371_ == 1)
{
lean_object* v___x_372_; 
lean_dec(v_i_369_);
lean_dec_ref(v_path_367_);
v___x_372_ = lean_box(0);
return v___x_372_;
}
else
{
lean_object* v_one_373_; lean_object* v_n_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_one_373_ = lean_unsigned_to_nat(1u);
v_n_374_ = lean_nat_sub(v_i_369_, v_one_373_);
lean_dec(v_i_369_);
v___x_375_ = lean_array_fget_borrowed(v_as_368_, v_n_374_);
lean_inc(v___x_375_);
lean_inc_ref(v_path_367_);
v___x_376_ = l_Lake_LeanExe_isRootSrc_x3f(v_path_367_, v___x_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
v_i_369_ = v_n_374_;
goto _start;
}
else
{
lean_dec(v_n_374_);
lean_dec_ref(v_path_367_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg___boxed(lean_object* v_path_378_, lean_object* v_as_379_, lean_object* v_i_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_378_, v_as_379_, v_i_380_);
lean_dec_ref(v_as_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(lean_object* v_self_385_, lean_object* v_as_386_, size_t v_i_387_, size_t v_stop_388_, lean_object* v_b_389_){
_start:
{
lean_object* v___y_391_; uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_387_, v_stop_388_);
if (v___x_395_ == 0)
{
lean_object* v_toConfigDecl_396_; lean_object* v_name_397_; lean_object* v_kind_398_; lean_object* v_config_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_toConfigDecl_396_ = lean_array_uget_borrowed(v_as_386_, v_i_387_);
v_name_397_ = lean_ctor_get(v_toConfigDecl_396_, 1);
v_kind_398_ = lean_ctor_get(v_toConfigDecl_396_, 2);
v_config_399_ = lean_ctor_get(v_toConfigDecl_396_, 3);
v___x_400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___closed__1));
v___x_401_ = lean_name_eq(v_kind_398_, v___x_400_);
if (v___x_401_ == 0)
{
v___y_391_ = v_b_389_;
goto v___jp_390_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_inc(v_config_399_);
lean_inc(v_name_397_);
lean_inc_ref(v_self_385_);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v_self_385_);
lean_ctor_set(v___x_402_, 1, v_name_397_);
lean_ctor_set(v___x_402_, 2, v_config_399_);
v___x_403_ = lean_array_push(v_b_389_, v___x_402_);
v___y_391_ = v___x_403_;
goto v___jp_390_;
}
}
else
{
lean_dec_ref(v_self_385_);
return v_b_389_;
}
v___jp_390_:
{
size_t v___x_392_; size_t v___x_393_; 
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_add(v_i_387_, v___x_392_);
v_i_387_ = v___x_393_;
v_b_389_ = v___y_391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2___boxed(lean_object* v_self_404_, lean_object* v_as_405_, lean_object* v_i_406_, lean_object* v_stop_407_, lean_object* v_b_408_){
_start:
{
size_t v_i_boxed_409_; size_t v_stop_boxed_410_; lean_object* v_res_411_; 
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_stop_boxed_410_ = lean_unbox_usize(v_stop_407_);
lean_dec(v_stop_407_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_404_, v_as_405_, v_i_boxed_409_, v_stop_boxed_410_, v_b_408_);
lean_dec_ref(v_as_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(lean_object* v_path_412_, lean_object* v_as_413_, lean_object* v_i_414_){
_start:
{
lean_object* v_zero_415_; uint8_t v_isZero_416_; 
v_zero_415_ = lean_unsigned_to_nat(0u);
v_isZero_416_ = lean_nat_dec_eq(v_i_414_, v_zero_415_);
if (v_isZero_416_ == 1)
{
lean_object* v___x_417_; 
lean_dec(v_i_414_);
lean_dec_ref(v_path_412_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v_one_418_; lean_object* v_n_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_one_418_ = lean_unsigned_to_nat(1u);
v_n_419_ = lean_nat_sub(v_i_414_, v_one_418_);
lean_dec(v_i_414_);
v___x_420_ = lean_array_fget_borrowed(v_as_413_, v_n_419_);
lean_inc(v___x_420_);
lean_inc_ref(v_path_412_);
v___x_421_ = l_Lake_LeanLib_findModuleBySrc_x3f(v_path_412_, v___x_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
v_i_414_ = v_n_419_;
goto _start;
}
else
{
lean_dec(v_n_419_);
lean_dec_ref(v_path_412_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object* v_path_423_, lean_object* v_as_424_, lean_object* v_i_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_423_, v_as_424_, v_i_425_);
lean_dec_ref(v_as_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModuleBySrc_x3f(lean_object* v_path_427_, lean_object* v_self_428_){
_start:
{
lean_object* v___y_430_; lean_object* v_targetDecls_433_; lean_object* v___y_435_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_targetDecls_433_ = lean_ctor_get(v_self_428_, 14);
lean_inc_ref(v_targetDecls_433_);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_451_ = lean_array_get_size(v_targetDecls_433_);
v___x_452_ = lean_nat_dec_lt(v___x_449_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_435_ = v___x_450_;
goto v___jp_434_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_le(v___x_451_, v___x_451_);
if (v___x_453_ == 0)
{
if (v___x_452_ == 0)
{
v___y_435_ = v___x_450_;
goto v___jp_434_;
}
else
{
size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
v___x_454_ = ((size_t)0ULL);
v___x_455_ = lean_usize_of_nat(v___x_451_);
lean_inc_ref(v_self_428_);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_428_, v_targetDecls_433_, v___x_454_, v___x_455_, v___x_450_);
v___y_435_ = v___x_456_;
goto v___jp_434_;
}
}
else
{
size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((size_t)0ULL);
v___x_458_ = lean_usize_of_nat(v___x_451_);
lean_inc_ref(v_self_428_);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModuleBySrc_x3f_spec__2(v_self_428_, v_targetDecls_433_, v___x_457_, v___x_458_, v___x_450_);
v___y_435_ = v___x_459_;
goto v___jp_434_;
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_array_get_size(v___y_430_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_427_, v___y_430_, v___x_431_);
lean_dec_ref(v___y_430_);
return v___x_432_;
}
v___jp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_array_get_size(v___y_435_);
lean_inc_ref(v_path_427_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_427_, v___y_435_, v___x_436_);
lean_dec_ref(v___y_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = ((lean_object*)(l_Lake_Package_leanExes___closed__0));
v___x_440_ = lean_array_get_size(v_targetDecls_433_);
v___x_441_ = lean_nat_dec_lt(v___x_438_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_targetDecls_433_);
lean_dec_ref(v_self_428_);
v___y_430_ = v___x_439_;
goto v___jp_429_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = lean_nat_dec_le(v___x_440_, v___x_440_);
if (v___x_442_ == 0)
{
if (v___x_441_ == 0)
{
lean_dec_ref(v_targetDecls_433_);
lean_dec_ref(v_self_428_);
v___y_430_ = v___x_439_;
goto v___jp_429_;
}
else
{
size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((size_t)0ULL);
v___x_444_ = lean_usize_of_nat(v___x_440_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_428_, v_targetDecls_433_, v___x_443_, v___x_444_, v___x_439_);
lean_dec_ref(v_targetDecls_433_);
v___y_430_ = v___x_445_;
goto v___jp_429_;
}
}
else
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((size_t)0ULL);
v___x_447_ = lean_usize_of_nat(v___x_440_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findTargetModule_x3f_spec__1(v_self_428_, v_targetDecls_433_, v___x_446_, v___x_447_, v___x_439_);
lean_dec_ref(v_targetDecls_433_);
v___y_430_ = v___x_448_;
goto v___jp_429_;
}
}
}
else
{
lean_dec_ref(v_targetDecls_433_);
lean_dec_ref(v_self_428_);
lean_dec_ref(v_path_427_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(lean_object* v_path_460_, lean_object* v_as_461_, lean_object* v_i_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___redArg(v_path_460_, v_as_461_, v_i_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_465_, lean_object* v_as_466_, lean_object* v_i_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__0(v_path_465_, v_as_466_, v_i_467_, v_a_468_);
lean_dec_ref(v_as_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(lean_object* v_path_470_, lean_object* v_as_471_, lean_object* v_i_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___redArg(v_path_470_, v_as_471_, v_i_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1___boxed(lean_object* v_path_475_, lean_object* v_as_476_, lean_object* v_i_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModuleBySrc_x3f_spec__1(v_path_475_, v_as_476_, v_i_477_, v_a_478_);
lean_dec_ref(v_as_476_);
return v_res_479_;
}
}
lean_object* runtime_initialize_Lake_Config_Module(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanExe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
