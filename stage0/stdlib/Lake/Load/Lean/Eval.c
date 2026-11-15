// Lean compiler output
// Module: Lake.Load.Lean.Eval
// Imports: public import Lake.Config.Workspace public import Lake.Config.LakefileConfig import Lean.DocString import Lake.DSL.AttributesCore
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instTypeNamePackageFacetDecl;
lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
extern lean_object* l_Lake_instTypeNameScriptFn;
extern lean_object* l_Lake_packageAttr;
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_targetAttr;
size_t lean_array_size(lean_object*);
extern lean_object* l_Lake_moduleFacetAttr;
extern lean_object* l_Lake_instTypeNameModuleFacetDecl;
extern lean_object* l_Lake_packageFacetAttr;
extern lean_object* l_Lake_libraryFacetAttr;
extern lean_object* l_Lake_instTypeNameLibraryFacetDecl;
extern lean_object* l_Lake_lintDriverAttr;
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lake_scriptAttr;
extern lean_object* l_Lake_defaultScriptAttr;
extern lean_object* l_Lake_postUpdateAttr;
extern lean_object* l_Lake_packageDepAttr;
extern lean_object* l_Lake_testDriverAttr;
extern lean_object* l_Lake_defaultTargetAttr;
extern lean_object* l_Lake_cacheServiceAttr;
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Cache_3424128028____hygCtx___hyg_18_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected type at '"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "', `"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` expected"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown constant '"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "configuration file is missing a `package` declaration"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value)}};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1_value;
static const lean_string_object l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "configuration file has multiple `package` declarations"};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value)}};
static const lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3 = (const lean_object*)&l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0 = (const lean_object*)&l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": executable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' has the same root module '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' as executable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "post-update hook was defined in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "', but was registered in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' was already defined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "', but then redefined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": package is missing target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' marked as a default"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' was defined in package '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "', but registered under '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = ": invalid cache service "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": missing name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = ": package is missing script or target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' marked as a test driver"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' marked as a lint driver"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": package is missing script '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_LakefileConfig_loadFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LakefileConfig_loadFromEnv___closed__0 = (const lean_object*)&l_Lake_LakefileConfig_loadFromEnv___closed__0_value;
static const lean_string_object l_Lake_LakefileConfig_loadFromEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = ": cannot both set lintDriver and use @[lint_driver]"};
static const lean_object* l_Lake_LakefileConfig_loadFromEnv___closed__1 = (const lean_object*)&l_Lake_LakefileConfig_loadFromEnv___closed__1_value;
static const lean_string_object l_Lake_LakefileConfig_loadFromEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = ": only one script or executable can be tagged @[lint_driver]"};
static const lean_object* l_Lake_LakefileConfig_loadFromEnv___closed__2 = (const lean_object*)&l_Lake_LakefileConfig_loadFromEnv___closed__2_value;
static const lean_string_object l_Lake_LakefileConfig_loadFromEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = ": cannot both set testDriver and use @[test_driver]"};
static const lean_object* l_Lake_LakefileConfig_loadFromEnv___closed__3 = (const lean_object*)&l_Lake_LakefileConfig_loadFromEnv___closed__3_value;
static const lean_string_object l_Lake_LakefileConfig_loadFromEnv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = ": only one script, executable, or library can be tagged @[test_driver]"};
static const lean_object* l_Lake_LakefileConfig_loadFromEnv___closed__4 = (const lean_object*)&l_Lake_LakefileConfig_loadFromEnv___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(lean_object* v_inst_4_, lean_object* v_const_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_6_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0));
v___x_7_ = 1;
v___x_8_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_const_5_, v___x_7_);
v___x_9_ = lean_string_append(v___x_6_, v___x_8_);
lean_dec_ref(v___x_8_);
v___x_10_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1));
v___x_11_ = lean_string_append(v___x_9_, v___x_10_);
v___x_12_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_4_, v___x_7_);
v___x_13_ = lean_string_append(v___x_11_, v___x_12_);
lean_dec_ref(v___x_12_);
v___x_14_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2));
v___x_15_ = lean_string_append(v___x_13_, v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType(lean_object* v_00_u03b1_17_, lean_object* v_inst_18_, lean_object* v_const_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_18_, v_const_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(lean_object* v_env_23_, lean_object* v_opts_24_, lean_object* v_inst_25_, lean_object* v_const_26_){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_27_ = 0;
lean_inc(v_const_26_);
lean_inc_ref(v_env_23_);
v___x_28_ = l_Lean_Environment_find_x3f(v_env_23_, v_const_26_, v___x_27_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_inst_25_);
lean_dec_ref(v_env_23_);
v___x_29_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0));
v___x_30_ = 1;
v___x_31_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_const_26_, v___x_30_);
v___x_32_ = lean_string_append(v___x_29_, v___x_31_);
lean_dec_ref(v___x_31_);
v___x_33_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_34_ = lean_string_append(v___x_32_, v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_37_; 
v_val_36_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v___x_28_, 1);
v___x_37_ = l_Lean_ConstantInfo_type(v_val_36_);
lean_dec(v_val_36_);
if (lean_obj_tag(v___x_37_) == 4)
{
lean_object* v_declName_38_; uint8_t v___x_39_; 
v_declName_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_declName_38_);
lean_dec_ref_known(v___x_37_, 2);
v___x_39_ = lean_name_eq(v_declName_38_, v_inst_25_);
lean_dec(v_declName_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_dec_ref(v_env_23_);
v___x_40_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_25_, v_const_26_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
lean_dec(v_inst_25_);
v___x_41_ = l_Lean_Environment_evalConst___redArg(v_env_23_, v_opts_24_, v_const_26_, v___x_39_);
lean_dec(v_const_26_);
lean_dec_ref(v_env_23_);
return v___x_41_;
}
}
else
{
lean_object* v___x_42_; 
lean_dec_ref(v___x_37_);
lean_dec_ref(v_env_23_);
v___x_42_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_25_, v_const_26_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___boxed(lean_object* v_env_43_, lean_object* v_opts_44_, lean_object* v_inst_45_, lean_object* v_const_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_43_, v_opts_44_, v_inst_45_, v_const_46_);
lean_dec_ref(v_opts_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(lean_object* v_env_48_, lean_object* v_opts_49_, lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_const_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_48_, v_opts_49_, v_inst_51_, v_const_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___boxed(lean_object* v_env_54_, lean_object* v_opts_55_, lean_object* v_00_u03b1_56_, lean_object* v_inst_57_, lean_object* v_const_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(v_env_54_, v_opts_55_, v_00_u03b1_56_, v_inst_57_, v_const_58_);
lean_dec_ref(v_opts_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0(lean_object* v_declName_61_, lean_object* v_map_62_, lean_object* v_toPure_63_, lean_object* v_____do__lift_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
v___x_66_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_65_, v_declName_61_, v_____do__lift_64_, v_map_62_);
v___x_67_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1(lean_object* v_toPure_68_, lean_object* v_f_69_, lean_object* v_toBind_70_, lean_object* v_map_71_, lean_object* v_declName_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc(v_declName_72_);
v___f_73_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_73_, 0, v_declName_72_);
lean_closure_set(v___f_73_, 1, v_map_71_);
lean_closure_set(v___f_73_, 2, v_toPure_68_);
v___x_74_ = lean_apply_1(v_f_69_, v_declName_72_);
v___x_75_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_74_, v___f_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(lean_object* v_env_76_, lean_object* v_attr_77_, lean_object* v_inst_78_, lean_object* v_f_79_){
_start:
{
lean_object* v_toApplicative_80_; lean_object* v_toBind_81_; lean_object* v_toPure_82_; lean_object* v_entries_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_toApplicative_80_ = lean_ctor_get(v_inst_78_, 0);
v_toBind_81_ = lean_ctor_get(v_inst_78_, 1);
v_toPure_82_ = lean_ctor_get(v_toApplicative_80_, 1);
v_entries_83_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_77_, v_env_76_);
v___x_84_ = lean_box(1);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_array_get_size(v_entries_83_);
v___x_87_ = lean_nat_dec_lt(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
lean_inc(v_toPure_82_);
lean_dec_ref(v_entries_83_);
lean_dec(v_f_79_);
lean_dec_ref(v_inst_78_);
v___x_88_ = lean_apply_2(v_toPure_82_, lean_box(0), v___x_84_);
return v___x_88_;
}
else
{
lean_object* v___f_89_; size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
lean_inc(v_toBind_81_);
lean_inc(v_toPure_82_);
v___f_89_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_89_, 0, v_toPure_82_);
lean_closure_set(v___f_89_, 1, v_f_79_);
lean_closure_set(v___f_89_, 2, v_toBind_81_);
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_86_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_78_, v___f_89_, v_entries_83_, v___x_90_, v___x_91_, v___x_84_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___boxed(lean_object* v_env_93_, lean_object* v_attr_94_, lean_object* v_inst_95_, lean_object* v_f_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(v_env_93_, v_attr_94_, v_inst_95_, v_f_96_);
lean_dec_ref(v_attr_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(lean_object* v_m_98_, lean_object* v_00_u03b2_99_, lean_object* v_env_100_, lean_object* v_attr_101_, lean_object* v_inst_102_, lean_object* v_f_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(v_env_100_, v_attr_101_, v_inst_102_, v_f_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___boxed(lean_object* v_m_105_, lean_object* v_00_u03b2_106_, lean_object* v_env_107_, lean_object* v_attr_108_, lean_object* v_inst_109_, lean_object* v_f_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(v_m_105_, v_00_u03b2_106_, v_env_107_, v_attr_108_, v_inst_109_, v_f_110_);
lean_dec_ref(v_attr_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0(lean_object* v_declName_112_, lean_object* v_map_113_, lean_object* v_toPure_114_, lean_object* v_____do__lift_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_112_, v_____do__lift_115_, v_map_113_);
v___x_117_ = lean_apply_2(v_toPure_114_, lean_box(0), v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1(lean_object* v_toPure_118_, lean_object* v_f_119_, lean_object* v_toBind_120_, lean_object* v_map_121_, lean_object* v_declName_122_){
_start:
{
lean_object* v___f_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
lean_inc(v_declName_122_);
v___f_123_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_123_, 0, v_declName_122_);
lean_closure_set(v___f_123_, 1, v_map_121_);
lean_closure_set(v___f_123_, 2, v_toPure_118_);
v___x_124_ = lean_apply_1(v_f_119_, v_declName_122_);
v___x_125_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_124_, v___f_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(lean_object* v_env_126_, lean_object* v_attr_127_, lean_object* v_inst_128_, lean_object* v_f_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v_toBind_131_; lean_object* v_toPure_132_; lean_object* v_entries_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_128_, 0);
v_toBind_131_ = lean_ctor_get(v_inst_128_, 1);
v_toPure_132_ = lean_ctor_get(v_toApplicative_130_, 1);
v_entries_133_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_127_, v_env_126_);
v___x_134_ = lean_box(1);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_entries_133_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_inc(v_toPure_132_);
lean_dec_ref(v_entries_133_);
lean_dec(v_f_129_);
lean_dec_ref(v_inst_128_);
v___x_138_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_134_);
return v___x_138_;
}
else
{
lean_object* v___f_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
lean_inc(v_toBind_131_);
lean_inc(v_toPure_132_);
v___f_139_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_139_, 0, v_toPure_132_);
lean_closure_set(v___f_139_, 1, v_f_129_);
lean_closure_set(v___f_139_, 2, v_toBind_131_);
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_136_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_128_, v___f_139_, v_entries_133_, v___x_140_, v___x_141_, v___x_134_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___boxed(lean_object* v_env_143_, lean_object* v_attr_144_, lean_object* v_inst_145_, lean_object* v_f_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(v_env_143_, v_attr_144_, v_inst_145_, v_f_146_);
lean_dec_ref(v_attr_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(lean_object* v_m_148_, lean_object* v_00_u03b2_149_, lean_object* v_env_150_, lean_object* v_attr_151_, lean_object* v_inst_152_, lean_object* v_f_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(v_env_150_, v_attr_151_, v_inst_152_, v_f_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___boxed(lean_object* v_m_155_, lean_object* v_00_u03b2_156_, lean_object* v_env_157_, lean_object* v_attr_158_, lean_object* v_inst_159_, lean_object* v_f_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(v_m_155_, v_00_u03b2_156_, v_env_157_, v_attr_158_, v_inst_159_, v_f_160_);
lean_dec_ref(v_attr_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0(lean_object* v_map_162_, lean_object* v_declName_163_, lean_object* v_toPure_164_, lean_object* v_____do__lift_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
v___x_167_ = l_Lake_RBArray_insert___redArg(v___x_166_, v_map_162_, v_declName_163_, v_____do__lift_165_);
v___x_168_ = lean_apply_2(v_toPure_164_, lean_box(0), v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1(lean_object* v_toPure_169_, lean_object* v_f_170_, lean_object* v_toBind_171_, lean_object* v_map_172_, lean_object* v_declName_173_){
_start:
{
lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_inc(v_declName_173_);
v___f_174_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_174_, 0, v_map_172_);
lean_closure_set(v___f_174_, 1, v_declName_173_);
lean_closure_set(v___f_174_, 2, v_toPure_169_);
v___x_175_ = lean_apply_1(v_f_170_, v_declName_173_);
v___x_176_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_175_, v___f_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(lean_object* v_env_177_, lean_object* v_attr_178_, lean_object* v_inst_179_, lean_object* v_f_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v_entries_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_179_, 0);
v_toBind_182_ = lean_ctor_get(v_inst_179_, 1);
v_toPure_183_ = lean_ctor_get(v_toApplicative_181_, 1);
v_entries_184_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_178_, v_env_177_);
v___x_185_ = lean_array_get_size(v_entries_184_);
v___x_186_ = l_Lake_RBArray_mkEmpty___redArg(v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_nat_dec_lt(v___x_187_, v___x_185_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
lean_inc(v_toPure_183_);
lean_dec_ref(v_entries_184_);
lean_dec(v_f_180_);
lean_dec_ref(v_inst_179_);
v___x_189_ = lean_apply_2(v_toPure_183_, lean_box(0), v___x_186_);
return v___x_189_;
}
else
{
lean_object* v___f_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; 
lean_inc(v_toBind_182_);
lean_inc(v_toPure_183_);
v___f_190_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_190_, 0, v_toPure_183_);
lean_closure_set(v___f_190_, 1, v_f_180_);
lean_closure_set(v___f_190_, 2, v_toBind_182_);
v___x_191_ = ((size_t)0ULL);
v___x_192_ = lean_usize_of_nat(v___x_185_);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_179_, v___f_190_, v_entries_184_, v___x_191_, v___x_192_, v___x_186_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___boxed(lean_object* v_env_194_, lean_object* v_attr_195_, lean_object* v_inst_196_, lean_object* v_f_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(v_env_194_, v_attr_195_, v_inst_196_, v_f_197_);
lean_dec_ref(v_attr_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(lean_object* v_m_199_, lean_object* v_00_u03b2_200_, lean_object* v_env_201_, lean_object* v_attr_202_, lean_object* v_inst_203_, lean_object* v_f_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(v_env_201_, v_attr_202_, v_inst_203_, v_f_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___boxed(lean_object* v_m_206_, lean_object* v_00_u03b2_207_, lean_object* v_env_208_, lean_object* v_attr_209_, lean_object* v_inst_210_, lean_object* v_f_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(v_m_206_, v_00_u03b2_207_, v_env_208_, v_attr_209_, v_inst_210_, v_f_211_);
lean_dec_ref(v_attr_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(lean_object* v_env_219_, lean_object* v_opts_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Lake_packageAttr;
lean_inc_ref(v_env_219_);
v___x_222_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_221_, v_env_219_);
v___x_223_ = lean_array_to_list(v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
lean_dec_ref(v_env_219_);
v___x_224_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1));
return v___x_224_;
}
else
{
lean_object* v_tail_225_; 
v_tail_225_ = lean_ctor_get(v___x_223_, 1);
if (lean_obj_tag(v_tail_225_) == 0)
{
lean_object* v_head_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_head_226_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_head_226_);
lean_dec_ref_known(v___x_223_, 2);
v___x_227_ = l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
v___x_228_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_219_, v_opts_220_, v___x_227_, v_head_226_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; 
lean_dec_ref_known(v___x_223_, 2);
lean_dec_ref(v_env_219_);
v___x_229_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3));
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___boxed(lean_object* v_env_230_, lean_object* v_opts_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_230_, v_opts_231_);
lean_dec_ref(v_opts_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(lean_object* v_e_233_){
_start:
{
if (lean_obj_tag(v_e_233_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_a_235_ = lean_ctor_get(v_e_233_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_e_233_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v_e_233_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v_e_233_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_mk_io_user_error(v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v_e_233_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_e_233_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v_e_233_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v_e_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
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
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg___boxed(lean_object* v_e_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(lean_object* v_00_u03b1_255_, lean_object* v_e_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___boxed(lean_object* v_00_u03b1_259_, lean_object* v_e_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(v_00_u03b1_259_, v_e_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0(lean_object* v_env_263_, lean_object* v_opts_264_, lean_object* v___x_265_, lean_object* v_name_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_263_, v_opts_264_, v___x_265_, v_name_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed(lean_object* v_env_268_, lean_object* v_opts_269_, lean_object* v___x_270_, lean_object* v_name_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lake_LakefileConfig_loadFromEnv___lam__0(v_env_268_, v_opts_269_, v___x_270_, v_name_271_);
lean_dec_ref(v_opts_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1(lean_object* v___x_274_, uint8_t v___x_275_, lean_object* v_env_276_, lean_object* v_opts_277_, lean_object* v___x_278_, lean_object* v_scriptName_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0));
v___x_283_ = lean_string_append(v___x_274_, v___x_282_);
lean_inc_n(v_scriptName_279_, 2);
v___x_284_ = l_Lean_Name_toString(v_scriptName_279_, v___x_275_);
v___x_285_ = lean_string_append(v___x_283_, v___x_284_);
lean_dec_ref(v___x_284_);
lean_inc_ref(v_env_276_);
v___x_286_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_276_, v_opts_277_, v___x_278_, v_scriptName_279_);
v___x_287_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v___x_289_ = 1;
v___x_290_ = l_Lean_Options_empty;
v___x_291_ = lean_box(0);
v___x_292_ = lean_box(0);
v___x_293_ = l_Lean_findDocString_x3f(v_env_276_, v_scriptName_279_, v___x_289_, v___x_290_, v___x_291_, v___x_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_285_);
lean_ctor_set(v___x_295_, 1, v_a_288_);
lean_ctor_set(v___x_295_, 2, v_a_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___y_280_);
return v___x_296_;
}
else
{
lean_object* v_a_297_; lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_a_288_);
lean_dec_ref(v___x_285_);
v_a_297_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_293_, 1);
v___x_298_ = lean_io_error_to_string(v_a_297_);
v___x_299_ = 3;
v___x_300_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*1, v___x_299_);
v___x_301_ = lean_array_get_size(v___y_280_);
v___x_302_ = lean_array_push(v___y_280_, v___x_300_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref(v___x_285_);
lean_dec(v_scriptName_279_);
lean_dec_ref(v_env_276_);
v_a_304_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_287_, 1);
v___x_305_ = lean_io_error_to_string(v_a_304_);
v___x_306_ = 3;
v___x_307_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*1, v___x_306_);
v___x_308_ = lean_array_get_size(v___y_280_);
v___x_309_ = lean_array_push(v___y_280_, v___x_307_);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object* v___x_311_, lean_object* v___x_312_, lean_object* v_env_313_, lean_object* v_opts_314_, lean_object* v___x_315_, lean_object* v_scriptName_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
uint8_t v___x_56002__boxed_319_; lean_object* v_res_320_; 
v___x_56002__boxed_319_ = lean_unbox(v___x_312_);
v_res_320_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_311_, v___x_56002__boxed_319_, v_env_313_, v_opts_314_, v___x_315_, v_scriptName_316_, v___y_317_);
lean_dec_ref(v_opts_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object* v_t_321_, lean_object* v_k_322_){
_start:
{
if (lean_obj_tag(v_t_321_) == 0)
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_l_325_; lean_object* v_r_326_; uint8_t v___x_327_; 
v_k_323_ = lean_ctor_get(v_t_321_, 1);
v_v_324_ = lean_ctor_get(v_t_321_, 2);
v_l_325_ = lean_ctor_get(v_t_321_, 3);
v_r_326_ = lean_ctor_get(v_t_321_, 4);
v___x_327_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_322_, v_k_323_);
switch(v___x_327_)
{
case 0:
{
v_t_321_ = v_l_325_;
goto _start;
}
case 1:
{
lean_object* v___x_329_; 
lean_inc(v_v_324_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_v_324_);
return v___x_329_;
}
default: 
{
v_t_321_ = v_r_326_;
goto _start;
}
}
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_box(0);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_332_, lean_object* v_k_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_332_, v_k_333_);
lean_dec(v_k_333_);
lean_dec(v_t_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_338_, lean_object* v_as_339_, size_t v_i_340_, size_t v_stop_341_, lean_object* v_b_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_a_346_; lean_object* v_a_347_; uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_eq(v_i_340_, v_stop_341_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v_name_353_; lean_object* v_kind_354_; lean_object* v_config_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_352_ = lean_array_uget_borrowed(v_as_339_, v_i_340_);
v_name_353_ = lean_ctor_get(v___x_352_, 1);
v_kind_354_ = lean_ctor_get(v___x_352_, 2);
v_config_355_ = lean_ctor_get(v___x_352_, 3);
v___x_356_ = l_Lake_LeanExe_keyword;
v___x_357_ = lean_name_eq(v_kind_354_, v___x_356_);
if (v___x_357_ == 0)
{
v_a_346_ = v_b_342_;
v_a_347_ = v___y_343_;
goto v___jp_345_;
}
else
{
lean_object* v_root_358_; lean_object* v___x_359_; 
v_root_358_ = lean_ctor_get(v_config_355_, 2);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_342_, v_root_358_);
if (lean_obj_tag(v___x_359_) == 1)
{
lean_object* v_val_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_b_342_);
v_val_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_val_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__0));
v___x_362_ = lean_string_append(v___x_338_, v___x_361_);
lean_inc(v_name_353_);
v___x_363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_353_, v___x_357_);
v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
lean_dec_ref(v___x_363_);
v___x_365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__1));
v___x_366_ = lean_string_append(v___x_364_, v___x_365_);
lean_inc(v_root_358_);
v___x_367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_358_, v___x_357_);
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
lean_dec_ref(v___x_367_);
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___closed__2));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
v___x_371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_360_, v___x_357_);
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
lean_dec_ref(v___x_371_);
v___x_373_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
v___x_375_ = 3;
v___x_376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*1, v___x_375_);
v___x_377_ = lean_array_get_size(v___y_343_);
v___x_378_ = lean_array_push(v___y_343_, v___x_376_);
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
lean_dec(v___x_359_);
lean_inc(v_name_353_);
lean_inc(v_root_358_);
v___x_380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_358_, v_name_353_, v_b_342_);
v_a_346_ = v___x_380_;
v_a_347_ = v___y_343_;
goto v___jp_345_;
}
}
}
else
{
lean_object* v___x_381_; 
lean_dec_ref(v___x_338_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_b_342_);
lean_ctor_set(v___x_381_, 1, v___y_343_);
return v___x_381_;
}
v___jp_345_:
{
size_t v___x_348_; size_t v___x_349_; 
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_add(v_i_340_, v___x_348_);
v_i_340_ = v___x_349_;
v_b_342_ = v_a_346_;
v___y_343_ = v_a_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_382_, lean_object* v_as_383_, lean_object* v_i_384_, lean_object* v_stop_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_385_);
lean_dec(v_stop_385_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_382_, v_as_383_, v_i_boxed_389_, v_stop_boxed_390_, v_b_386_, v___y_387_);
lean_dec_ref(v_as_383_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object* v_env_394_, lean_object* v_opts_395_, lean_object* v___x_396_, size_t v_sz_397_, size_t v_i_398_, lean_object* v_bs_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_a_403_; lean_object* v_a_404_; uint8_t v___x_406_; 
v___x_406_ = lean_usize_dec_lt(v_i_398_, v_sz_397_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
lean_dec(v___x_396_);
lean_dec_ref(v_env_394_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_bs_399_);
lean_ctor_set(v___x_407_, 1, v___y_400_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v_v_409_; lean_object* v___x_410_; 
v___x_408_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_409_ = lean_array_uget_borrowed(v_bs_399_, v_i_398_);
lean_inc(v_v_409_);
lean_inc_ref(v_env_394_);
v___x_410_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_394_, v_opts_395_, v___x_408_, v_v_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v_bs_399_);
lean_dec(v___x_396_);
lean_dec_ref(v_env_394_);
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = 3;
v___x_413_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_413_, 0, v_a_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_412_);
v___x_414_ = lean_array_get_size(v___y_400_);
v___x_415_ = lean_array_push(v___y_400_, v___x_413_);
v_a_403_ = v___x_414_;
v_a_404_ = v___x_415_;
goto v___jp_402_;
}
else
{
lean_object* v_a_416_; lean_object* v_pkg_417_; lean_object* v_fn_418_; uint8_t v___x_419_; 
v_a_416_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_410_, 1);
v_pkg_417_ = lean_ctor_get(v_a_416_, 0);
lean_inc(v_pkg_417_);
v_fn_418_ = lean_ctor_get(v_a_416_, 1);
lean_inc_ref(v_fn_418_);
lean_dec(v_a_416_);
v___x_419_ = lean_name_eq(v_pkg_417_, v___x_396_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v_fn_418_);
lean_dec_ref(v_bs_399_);
lean_dec_ref(v_env_394_);
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0));
v___x_421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_417_, v___x_406_);
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
lean_dec_ref(v___x_421_);
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1));
v___x_424_ = lean_string_append(v___x_422_, v___x_423_);
v___x_425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_396_, v___x_406_);
v___x_426_ = lean_string_append(v___x_424_, v___x_425_);
lean_dec_ref(v___x_425_);
v___x_427_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_428_ = lean_string_append(v___x_426_, v___x_427_);
v___x_429_ = 3;
v___x_430_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_429_);
v___x_431_ = lean_array_get_size(v___y_400_);
v___x_432_ = lean_array_push(v___y_400_, v___x_430_);
v_a_403_ = v___x_431_;
v_a_404_ = v___x_432_;
goto v___jp_402_;
}
else
{
lean_object* v___x_433_; lean_object* v_bs_x27_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
lean_dec(v_pkg_417_);
v___x_433_ = lean_unsigned_to_nat(0u);
v_bs_x27_434_ = lean_array_uset(v_bs_399_, v_i_398_, v___x_433_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_398_, v___x_435_);
v___x_437_ = lean_array_uset(v_bs_x27_434_, v_i_398_, v_fn_418_);
v_i_398_ = v___x_436_;
v_bs_399_ = v___x_437_;
goto _start;
}
}
}
v___jp_402_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v_a_403_);
lean_ctor_set(v___x_405_, 1, v_a_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object* v_env_439_, lean_object* v_opts_440_, lean_object* v___x_441_, lean_object* v_sz_442_, lean_object* v_i_443_, lean_object* v_bs_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
size_t v_sz_boxed_447_; size_t v_i_boxed_448_; lean_object* v_res_449_; 
v_sz_boxed_447_ = lean_unbox_usize(v_sz_442_);
lean_dec(v_sz_442_);
v_i_boxed_448_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_439_, v_opts_440_, v___x_441_, v_sz_boxed_447_, v_i_boxed_448_, v_bs_444_, v___y_445_);
lean_dec_ref(v_opts_440_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object* v_t_450_, lean_object* v_k_451_){
_start:
{
if (lean_obj_tag(v_t_450_) == 0)
{
lean_object* v_k_452_; lean_object* v_v_453_; lean_object* v_l_454_; lean_object* v_r_455_; uint8_t v___x_456_; 
v_k_452_ = lean_ctor_get(v_t_450_, 1);
v_v_453_ = lean_ctor_get(v_t_450_, 2);
v_l_454_ = lean_ctor_get(v_t_450_, 3);
v_r_455_ = lean_ctor_get(v_t_450_, 4);
v___x_456_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_451_, v_k_452_);
switch(v___x_456_)
{
case 0:
{
v_t_450_ = v_l_454_;
goto _start;
}
case 1:
{
lean_object* v___x_458_; 
lean_inc(v_v_453_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_v_453_);
return v___x_458_;
}
default: 
{
v_t_450_ = v_r_455_;
goto _start;
}
}
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_t_461_, lean_object* v_k_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_t_461_, v_k_462_);
lean_dec(v_k_462_);
lean_dec(v_t_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(lean_object* v_k_464_, lean_object* v_v_465_, lean_object* v_t_466_){
_start:
{
if (lean_obj_tag(v_t_466_) == 0)
{
lean_object* v_size_467_; lean_object* v_k_468_; lean_object* v_v_469_; lean_object* v_l_470_; lean_object* v_r_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_751_; 
v_size_467_ = lean_ctor_get(v_t_466_, 0);
v_k_468_ = lean_ctor_get(v_t_466_, 1);
v_v_469_ = lean_ctor_get(v_t_466_, 2);
v_l_470_ = lean_ctor_get(v_t_466_, 3);
v_r_471_ = lean_ctor_get(v_t_466_, 4);
v_isSharedCheck_751_ = !lean_is_exclusive(v_t_466_);
if (v_isSharedCheck_751_ == 0)
{
v___x_473_ = v_t_466_;
v_isShared_474_ = v_isSharedCheck_751_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_r_471_);
lean_inc(v_l_470_);
lean_inc(v_v_469_);
lean_inc(v_k_468_);
lean_inc(v_size_467_);
lean_dec(v_t_466_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_751_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
uint8_t v___x_475_; 
v___x_475_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_464_, v_k_468_);
switch(v___x_475_)
{
case 0:
{
lean_object* v_impl_476_; lean_object* v___x_477_; 
lean_dec(v_size_467_);
v_impl_476_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_464_, v_v_465_, v_l_470_);
v___x_477_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_471_) == 0)
{
lean_object* v_size_478_; lean_object* v_size_479_; lean_object* v_k_480_; lean_object* v_v_481_; lean_object* v_l_482_; lean_object* v_r_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_size_478_ = lean_ctor_get(v_r_471_, 0);
v_size_479_ = lean_ctor_get(v_impl_476_, 0);
v_k_480_ = lean_ctor_get(v_impl_476_, 1);
v_v_481_ = lean_ctor_get(v_impl_476_, 2);
v_l_482_ = lean_ctor_get(v_impl_476_, 3);
v_r_483_ = lean_ctor_get(v_impl_476_, 4);
lean_inc(v_r_483_);
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_mul(v___x_484_, v_size_478_);
v___x_486_ = lean_nat_dec_lt(v___x_485_, v_size_479_);
lean_dec(v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
lean_dec(v_r_483_);
v___x_487_ = lean_nat_add(v___x_477_, v_size_479_);
v___x_488_ = lean_nat_add(v___x_487_, v_size_478_);
lean_dec(v___x_487_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 3, v_impl_476_);
lean_ctor_set(v___x_473_, 0, v___x_488_);
v___x_490_ = v___x_473_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_impl_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_r_471_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_557_; 
lean_inc(v_l_482_);
lean_inc(v_v_481_);
lean_inc(v_k_480_);
lean_inc(v_size_479_);
v_isSharedCheck_557_ = !lean_is_exclusive(v_impl_476_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; lean_object* v_unused_561_; lean_object* v_unused_562_; 
v_unused_558_ = lean_ctor_get(v_impl_476_, 4);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_impl_476_, 3);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_impl_476_, 2);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_impl_476_, 1);
lean_dec(v_unused_561_);
v_unused_562_ = lean_ctor_get(v_impl_476_, 0);
lean_dec(v_unused_562_);
v___x_493_ = v_impl_476_;
v_isShared_494_ = v_isSharedCheck_557_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_impl_476_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_557_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_size_495_; lean_object* v_size_496_; lean_object* v_k_497_; lean_object* v_v_498_; lean_object* v_l_499_; lean_object* v_r_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_size_495_ = lean_ctor_get(v_l_482_, 0);
v_size_496_ = lean_ctor_get(v_r_483_, 0);
v_k_497_ = lean_ctor_get(v_r_483_, 1);
v_v_498_ = lean_ctor_get(v_r_483_, 2);
v_l_499_ = lean_ctor_get(v_r_483_, 3);
v_r_500_ = lean_ctor_get(v_r_483_, 4);
v___x_501_ = lean_unsigned_to_nat(2u);
v___x_502_ = lean_nat_mul(v___x_501_, v_size_495_);
v___x_503_ = lean_nat_dec_lt(v_size_496_, v___x_502_);
lean_dec(v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_532_; 
lean_inc(v_r_500_);
lean_inc(v_l_499_);
lean_inc(v_v_498_);
lean_inc(v_k_497_);
v_isSharedCheck_532_ = !lean_is_exclusive(v_r_483_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; lean_object* v_unused_535_; lean_object* v_unused_536_; lean_object* v_unused_537_; 
v_unused_533_ = lean_ctor_get(v_r_483_, 4);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_r_483_, 3);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_r_483_, 2);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_r_483_, 1);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_r_483_, 0);
lean_dec(v_unused_537_);
v___x_505_ = v_r_483_;
v_isShared_506_ = v_isSharedCheck_532_;
goto v_resetjp_504_;
}
else
{
lean_dec(v_r_483_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_532_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___x_520_; lean_object* v___y_522_; 
v___x_507_ = lean_nat_add(v___x_477_, v_size_479_);
lean_dec(v_size_479_);
v___x_508_ = lean_nat_add(v___x_507_, v_size_478_);
lean_dec(v___x_507_);
v___x_520_ = lean_nat_add(v___x_477_, v_size_495_);
if (lean_obj_tag(v_l_499_) == 0)
{
lean_object* v_size_530_; 
v_size_530_ = lean_ctor_get(v_l_499_, 0);
lean_inc(v_size_530_);
v___y_522_ = v_size_530_;
goto v___jp_521_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___y_522_ = v___x_531_;
goto v___jp_521_;
}
v___jp_509_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_nat_add(v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec(v___y_511_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 4, v_r_471_);
lean_ctor_set(v___x_505_, 3, v_r_500_);
lean_ctor_set(v___x_505_, 2, v_v_469_);
lean_ctor_set(v___x_505_, 1, v_k_468_);
lean_ctor_set(v___x_505_, 0, v___x_513_);
v___x_515_ = v___x_505_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_r_500_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_r_471_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v___x_515_);
lean_ctor_set(v___x_493_, 3, v___y_510_);
lean_ctor_set(v___x_493_, 2, v_v_498_);
lean_ctor_set(v___x_493_, 1, v_k_497_);
lean_ctor_set(v___x_493_, 0, v___x_508_);
v___x_517_ = v___x_493_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_k_497_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_v_498_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v___y_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_nat_add(v___x_520_, v___y_522_);
lean_dec(v___y_522_);
lean_dec(v___x_520_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_l_499_);
lean_ctor_set(v___x_473_, 3, v_l_482_);
lean_ctor_set(v___x_473_, 2, v_v_481_);
lean_ctor_set(v___x_473_, 1, v_k_480_);
lean_ctor_set(v___x_473_, 0, v___x_523_);
v___x_525_ = v___x_473_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_k_480_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_v_481_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_l_482_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_l_499_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_nat_add(v___x_477_, v_size_478_);
if (lean_obj_tag(v_r_500_) == 0)
{
lean_object* v_size_527_; 
v_size_527_ = lean_ctor_get(v_r_500_, 0);
lean_inc(v_size_527_);
v___y_510_ = v___x_525_;
v___y_511_ = v___x_526_;
v___y_512_ = v_size_527_;
goto v___jp_509_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___y_510_ = v___x_525_;
v___y_511_ = v___x_526_;
v___y_512_ = v___x_528_;
goto v___jp_509_;
}
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_del_object(v___x_473_);
v___x_538_ = lean_nat_add(v___x_477_, v_size_479_);
lean_dec(v_size_479_);
v___x_539_ = lean_nat_add(v___x_538_, v_size_478_);
lean_dec(v___x_538_);
v___x_540_ = lean_nat_add(v___x_477_, v_size_478_);
v___x_541_ = lean_nat_add(v___x_540_, v_size_496_);
lean_dec(v___x_540_);
lean_inc_ref(v_r_471_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v_r_471_);
lean_ctor_set(v___x_493_, 3, v_r_483_);
lean_ctor_set(v___x_493_, 2, v_v_469_);
lean_ctor_set(v___x_493_, 1, v_k_468_);
lean_ctor_set(v___x_493_, 0, v___x_541_);
v___x_543_ = v___x_493_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_r_483_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_r_471_);
v___x_543_ = v_reuseFailAlloc_556_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_isSharedCheck_550_ = !lean_is_exclusive(v_r_471_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; lean_object* v_unused_552_; lean_object* v_unused_553_; lean_object* v_unused_554_; lean_object* v_unused_555_; 
v_unused_551_ = lean_ctor_get(v_r_471_, 4);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_r_471_, 3);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_r_471_, 2);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_r_471_, 1);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_r_471_, 0);
lean_dec(v_unused_555_);
v___x_545_ = v_r_471_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_dec(v_r_471_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 4, v___x_543_);
lean_ctor_set(v___x_545_, 3, v_l_482_);
lean_ctor_set(v___x_545_, 2, v_v_481_);
lean_ctor_set(v___x_545_, 1, v_k_480_);
lean_ctor_set(v___x_545_, 0, v___x_539_);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_k_480_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_v_481_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_l_482_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v___x_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_563_; 
v_l_563_ = lean_ctor_get(v_impl_476_, 3);
if (lean_obj_tag(v_l_563_) == 0)
{
lean_object* v_r_564_; lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_577_; 
lean_inc_ref(v_l_563_);
v_r_564_ = lean_ctor_get(v_impl_476_, 4);
v_k_565_ = lean_ctor_get(v_impl_476_, 1);
v_v_566_ = lean_ctor_get(v_impl_476_, 2);
v_isSharedCheck_577_ = !lean_is_exclusive(v_impl_476_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_578_ = lean_ctor_get(v_impl_476_, 3);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_impl_476_, 0);
lean_dec(v_unused_579_);
v___x_568_ = v_impl_476_;
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_r_564_);
lean_inc(v_v_566_);
lean_inc(v_k_565_);
lean_dec(v_impl_476_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_564_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v_r_564_);
lean_ctor_set(v___x_568_, 2, v_v_469_);
lean_ctor_set(v___x_568_, 1, v_k_468_);
lean_ctor_set(v___x_568_, 0, v___x_477_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_r_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_r_564_);
v___x_572_ = v_reuseFailAlloc_576_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v___x_572_);
lean_ctor_set(v___x_473_, 3, v_l_563_);
lean_ctor_set(v___x_473_, 2, v_v_566_);
lean_ctor_set(v___x_473_, 1, v_k_565_);
lean_ctor_set(v___x_473_, 0, v___x_570_);
v___x_574_ = v___x_473_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_l_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_r_580_; 
v_r_580_ = lean_ctor_get(v_impl_476_, 4);
lean_inc(v_r_580_);
if (lean_obj_tag(v_r_580_) == 0)
{
lean_object* v_k_581_; lean_object* v_v_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_605_; 
lean_inc(v_l_563_);
v_k_581_ = lean_ctor_get(v_impl_476_, 1);
v_v_582_ = lean_ctor_get(v_impl_476_, 2);
v_isSharedCheck_605_ = !lean_is_exclusive(v_impl_476_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; lean_object* v_unused_607_; lean_object* v_unused_608_; 
v_unused_606_ = lean_ctor_get(v_impl_476_, 4);
lean_dec(v_unused_606_);
v_unused_607_ = lean_ctor_get(v_impl_476_, 3);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_impl_476_, 0);
lean_dec(v_unused_608_);
v___x_584_ = v_impl_476_;
v_isShared_585_ = v_isSharedCheck_605_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_v_582_);
lean_inc(v_k_581_);
lean_dec(v_impl_476_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_605_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_k_586_; lean_object* v_v_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_601_; 
v_k_586_ = lean_ctor_get(v_r_580_, 1);
v_v_587_ = lean_ctor_get(v_r_580_, 2);
v_isSharedCheck_601_ = !lean_is_exclusive(v_r_580_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; lean_object* v_unused_603_; lean_object* v_unused_604_; 
v_unused_602_ = lean_ctor_get(v_r_580_, 4);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_r_580_, 3);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_r_580_, 0);
lean_dec(v_unused_604_);
v___x_589_ = v_r_580_;
v_isShared_590_ = v_isSharedCheck_601_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_v_587_);
lean_inc(v_k_586_);
lean_dec(v_r_580_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_601_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(3u);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_l_563_);
lean_ctor_set(v___x_589_, 3, v_l_563_);
lean_ctor_set(v___x_589_, 2, v_v_582_);
lean_ctor_set(v___x_589_, 1, v_k_581_);
lean_ctor_set(v___x_589_, 0, v___x_477_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_k_581_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_v_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_l_563_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_l_563_);
v___x_593_ = v_reuseFailAlloc_600_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_595_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 4, v_l_563_);
lean_ctor_set(v___x_584_, 2, v_v_469_);
lean_ctor_set(v___x_584_, 1, v_k_468_);
lean_ctor_set(v___x_584_, 0, v___x_477_);
v___x_595_ = v___x_584_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_l_563_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_l_563_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v___x_595_);
lean_ctor_set(v___x_473_, 3, v___x_593_);
lean_ctor_set(v___x_473_, 2, v_v_587_);
lean_ctor_set(v___x_473_, 1, v_k_586_);
lean_ctor_set(v___x_473_, 0, v___x_591_);
v___x_597_ = v___x_473_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(2u);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_r_580_);
lean_ctor_set(v___x_473_, 3, v_impl_476_);
lean_ctor_set(v___x_473_, 0, v___x_609_);
v___x_611_ = v___x_473_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_impl_476_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_r_580_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
case 1:
{
lean_object* v___x_614_; 
lean_dec(v_v_469_);
lean_dec(v_k_468_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v_v_465_);
lean_ctor_set(v___x_473_, 1, v_k_464_);
v___x_614_ = v___x_473_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_size_467_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_r_471_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
default: 
{
lean_object* v_impl_616_; lean_object* v___x_617_; 
lean_dec(v_size_467_);
v_impl_616_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_464_, v_v_465_, v_r_471_);
v___x_617_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_470_) == 0)
{
lean_object* v_size_618_; lean_object* v_size_619_; lean_object* v_k_620_; lean_object* v_v_621_; lean_object* v_l_622_; lean_object* v_r_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_size_618_ = lean_ctor_get(v_l_470_, 0);
v_size_619_ = lean_ctor_get(v_impl_616_, 0);
v_k_620_ = lean_ctor_get(v_impl_616_, 1);
v_v_621_ = lean_ctor_get(v_impl_616_, 2);
v_l_622_ = lean_ctor_get(v_impl_616_, 3);
lean_inc(v_l_622_);
v_r_623_ = lean_ctor_get(v_impl_616_, 4);
v___x_624_ = lean_unsigned_to_nat(3u);
v___x_625_ = lean_nat_mul(v___x_624_, v_size_618_);
v___x_626_ = lean_nat_dec_lt(v___x_625_, v_size_619_);
lean_dec(v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
lean_dec(v_l_622_);
v___x_627_ = lean_nat_add(v___x_617_, v_size_618_);
v___x_628_ = lean_nat_add(v___x_627_, v_size_619_);
lean_dec(v___x_627_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_impl_616_);
lean_ctor_set(v___x_473_, 0, v___x_628_);
v___x_630_ = v___x_473_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_impl_616_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_695_; 
lean_inc(v_r_623_);
lean_inc(v_v_621_);
lean_inc(v_k_620_);
lean_inc(v_size_619_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_impl_616_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_696_ = lean_ctor_get(v_impl_616_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_impl_616_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_impl_616_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_impl_616_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_impl_616_, 0);
lean_dec(v_unused_700_);
v___x_633_ = v_impl_616_;
v_isShared_634_ = v_isSharedCheck_695_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_impl_616_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_695_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_size_635_; lean_object* v_k_636_; lean_object* v_v_637_; lean_object* v_l_638_; lean_object* v_r_639_; lean_object* v_size_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_size_635_ = lean_ctor_get(v_l_622_, 0);
v_k_636_ = lean_ctor_get(v_l_622_, 1);
v_v_637_ = lean_ctor_get(v_l_622_, 2);
v_l_638_ = lean_ctor_get(v_l_622_, 3);
v_r_639_ = lean_ctor_get(v_l_622_, 4);
v_size_640_ = lean_ctor_get(v_r_623_, 0);
v___x_641_ = lean_unsigned_to_nat(2u);
v___x_642_ = lean_nat_mul(v___x_641_, v_size_640_);
v___x_643_ = lean_nat_dec_lt(v_size_635_, v___x_642_);
lean_dec(v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_671_; 
lean_inc(v_r_639_);
lean_inc(v_l_638_);
lean_inc(v_v_637_);
lean_inc(v_k_636_);
v_isSharedCheck_671_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; 
v_unused_672_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_l_622_, 2);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_l_622_, 1);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_676_);
v___x_645_ = v_l_622_;
v_isShared_646_ = v_isSharedCheck_671_;
goto v_resetjp_644_;
}
else
{
lean_dec(v_l_622_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_671_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_661_; 
v___x_647_ = lean_nat_add(v___x_617_, v_size_618_);
v___x_648_ = lean_nat_add(v___x_647_, v_size_619_);
lean_dec(v_size_619_);
if (lean_obj_tag(v_l_638_) == 0)
{
lean_object* v_size_669_; 
v_size_669_ = lean_ctor_get(v_l_638_, 0);
lean_inc(v_size_669_);
v___y_661_ = v_size_669_;
goto v___jp_660_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___y_661_ = v___x_670_;
goto v___jp_660_;
}
v___jp_649_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_nat_add(v___y_650_, v___y_652_);
lean_dec(v___y_652_);
lean_dec(v___y_650_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_r_623_);
lean_ctor_set(v___x_645_, 3, v_r_639_);
lean_ctor_set(v___x_645_, 2, v_v_621_);
lean_ctor_set(v___x_645_, 1, v_k_620_);
lean_ctor_set(v___x_645_, 0, v___x_653_);
v___x_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_r_639_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_r_623_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v___x_655_);
lean_ctor_set(v___x_633_, 3, v___y_651_);
lean_ctor_set(v___x_633_, 2, v_v_637_);
lean_ctor_set(v___x_633_, 1, v_k_636_);
lean_ctor_set(v___x_633_, 0, v___x_648_);
v___x_657_ = v___x_633_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_k_636_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_v_637_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v___y_651_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_nat_add(v___x_647_, v___y_661_);
lean_dec(v___y_661_);
lean_dec(v___x_647_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_l_638_);
lean_ctor_set(v___x_473_, 0, v___x_662_);
v___x_664_ = v___x_473_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_l_638_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_nat_add(v___x_617_, v_size_640_);
if (lean_obj_tag(v_r_639_) == 0)
{
lean_object* v_size_666_; 
v_size_666_ = lean_ctor_get(v_r_639_, 0);
lean_inc(v_size_666_);
v___y_650_ = v___x_665_;
v___y_651_ = v___x_664_;
v___y_652_ = v_size_666_;
goto v___jp_649_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___y_650_ = v___x_665_;
v___y_651_ = v___x_664_;
v___y_652_ = v___x_667_;
goto v___jp_649_;
}
}
}
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_del_object(v___x_473_);
v___x_677_ = lean_nat_add(v___x_617_, v_size_618_);
v___x_678_ = lean_nat_add(v___x_677_, v_size_619_);
lean_dec(v_size_619_);
v___x_679_ = lean_nat_add(v___x_677_, v_size_635_);
lean_dec(v___x_677_);
lean_inc_ref(v_l_470_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_l_622_);
lean_ctor_set(v___x_633_, 3, v_l_470_);
lean_ctor_set(v___x_633_, 2, v_v_469_);
lean_ctor_set(v___x_633_, 1, v_k_468_);
lean_ctor_set(v___x_633_, 0, v___x_679_);
v___x_681_ = v___x_633_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_l_622_);
v___x_681_ = v_reuseFailAlloc_694_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_isSharedCheck_688_ = !lean_is_exclusive(v_l_470_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; lean_object* v_unused_693_; 
v_unused_689_ = lean_ctor_get(v_l_470_, 4);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_l_470_, 3);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_l_470_, 2);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_l_470_, 1);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_l_470_, 0);
lean_dec(v_unused_693_);
v___x_683_ = v_l_470_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_dec(v_l_470_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 4, v_r_623_);
lean_ctor_set(v___x_683_, 3, v___x_681_);
lean_ctor_set(v___x_683_, 2, v_v_621_);
lean_ctor_set(v___x_683_, 1, v_k_620_);
lean_ctor_set(v___x_683_, 0, v___x_678_);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_r_623_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_701_; 
v_l_701_ = lean_ctor_get(v_impl_616_, 3);
lean_inc(v_l_701_);
if (lean_obj_tag(v_l_701_) == 0)
{
lean_object* v_r_702_; lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_727_; 
v_r_702_ = lean_ctor_get(v_impl_616_, 4);
v_k_703_ = lean_ctor_get(v_impl_616_, 1);
v_v_704_ = lean_ctor_get(v_impl_616_, 2);
v_isSharedCheck_727_ = !lean_is_exclusive(v_impl_616_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; lean_object* v_unused_729_; 
v_unused_728_ = lean_ctor_get(v_impl_616_, 3);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_impl_616_, 0);
lean_dec(v_unused_729_);
v___x_706_ = v_impl_616_;
v_isShared_707_ = v_isSharedCheck_727_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_r_702_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
lean_dec(v_impl_616_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_727_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_k_708_; lean_object* v_v_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_k_708_ = lean_ctor_get(v_l_701_, 1);
v_v_709_ = lean_ctor_get(v_l_701_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_l_701_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; 
v_unused_724_ = lean_ctor_get(v_l_701_, 4);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_l_701_, 3);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_l_701_, 0);
lean_dec(v_unused_726_);
v___x_711_ = v_l_701_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_v_709_);
lean_inc(v_k_708_);
lean_dec(v_l_701_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_702_, 2);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 4, v_r_702_);
lean_ctor_set(v___x_711_, 3, v_r_702_);
lean_ctor_set(v___x_711_, 2, v_v_469_);
lean_ctor_set(v___x_711_, 1, v_k_468_);
lean_ctor_set(v___x_711_, 0, v___x_617_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_r_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_r_702_);
v___x_715_ = v_reuseFailAlloc_722_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
lean_inc(v_r_702_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 3, v_r_702_);
lean_ctor_set(v___x_706_, 0, v___x_617_);
v___x_717_ = v___x_706_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_r_702_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_r_702_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v___x_717_);
lean_ctor_set(v___x_473_, 3, v___x_715_);
lean_ctor_set(v___x_473_, 2, v_v_709_);
lean_ctor_set(v___x_473_, 1, v_k_708_);
lean_ctor_set(v___x_473_, 0, v___x_713_);
v___x_719_ = v___x_473_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_708_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_709_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
else
{
lean_object* v_r_730_; 
v_r_730_ = lean_ctor_get(v_impl_616_, 4);
lean_inc(v_r_730_);
if (lean_obj_tag(v_r_730_) == 0)
{
lean_object* v_k_731_; lean_object* v_v_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_743_; 
v_k_731_ = lean_ctor_get(v_impl_616_, 1);
v_v_732_ = lean_ctor_get(v_impl_616_, 2);
v_isSharedCheck_743_ = !lean_is_exclusive(v_impl_616_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_744_ = lean_ctor_get(v_impl_616_, 4);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_impl_616_, 3);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_impl_616_, 0);
lean_dec(v_unused_746_);
v___x_734_ = v_impl_616_;
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_v_732_);
lean_inc(v_k_731_);
lean_dec(v_impl_616_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_unsigned_to_nat(3u);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 4, v_l_701_);
lean_ctor_set(v___x_734_, 2, v_v_469_);
lean_ctor_set(v___x_734_, 1, v_k_468_);
lean_ctor_set(v___x_734_, 0, v___x_617_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_l_701_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_l_701_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_r_730_);
lean_ctor_set(v___x_473_, 3, v___x_738_);
lean_ctor_set(v___x_473_, 2, v_v_732_);
lean_ctor_set(v___x_473_, 1, v_k_731_);
lean_ctor_set(v___x_473_, 0, v___x_736_);
v___x_740_ = v___x_473_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_r_730_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_unsigned_to_nat(2u);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_impl_616_);
lean_ctor_set(v___x_473_, 3, v_r_730_);
lean_ctor_set(v___x_473_, 0, v___x_747_);
v___x_749_ = v___x_473_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_r_730_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_impl_616_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_k_464_);
lean_ctor_set(v___x_753_, 2, v_v_465_);
lean_ctor_set(v___x_753_, 3, v_t_466_);
lean_ctor_set(v___x_753_, 4, v_t_466_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg(lean_object* v___x_757_, lean_object* v_as_758_, size_t v_i_759_, size_t v_stop_760_, lean_object* v_b_761_, lean_object* v___y_762_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_eq(v_i_759_, v_stop_760_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v_name_766_; lean_object* v_kind_767_; lean_object* v___x_768_; 
v___x_765_ = lean_array_uget_borrowed(v_as_758_, v_i_759_);
v_name_766_ = lean_ctor_get(v___x_765_, 1);
v_kind_767_ = lean_ctor_get(v___x_765_, 2);
v___x_768_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_b_761_, v_name_766_);
if (lean_obj_tag(v___x_768_) == 1)
{
lean_object* v_val_769_; lean_object* v_kind_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_b_761_);
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_768_, 1);
v_kind_770_ = lean_ctor_get(v_val_769_, 2);
lean_inc(v_kind_770_);
lean_dec(v_val_769_);
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__0));
v___x_772_ = lean_string_append(v___x_757_, v___x_771_);
v___x_773_ = 1;
lean_inc(v_name_766_);
v___x_774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_766_, v___x_773_);
v___x_775_ = lean_string_append(v___x_772_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__1));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_770_, v___x_773_);
v___x_779_ = lean_string_append(v___x_777_, v___x_778_);
lean_dec_ref(v___x_778_);
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___closed__2));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
lean_inc(v_kind_767_);
v___x_782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_767_, v___x_773_);
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___x_786_ = 3;
v___x_787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*1, v___x_786_);
v___x_788_ = lean_array_get_size(v___y_762_);
v___x_789_ = lean_array_push(v___y_762_, v___x_787_);
v___x_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; 
lean_dec(v___x_768_);
lean_inc(v___x_765_);
lean_inc(v_name_766_);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_name_766_, v___x_765_, v_b_761_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_759_, v___x_792_);
v_i_759_ = v___x_793_;
v_b_761_ = v___x_791_;
goto _start;
}
}
else
{
lean_object* v___x_795_; 
lean_dec_ref(v___x_757_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_b_761_);
lean_ctor_set(v___x_795_, 1, v___y_762_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg___boxed(lean_object* v___x_796_, lean_object* v_as_797_, lean_object* v_i_798_, lean_object* v_stop_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
size_t v_i_boxed_803_; size_t v_stop_boxed_804_; lean_object* v_res_805_; 
v_i_boxed_803_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_stop_boxed_804_ = lean_unbox_usize(v_stop_799_);
lean_dec(v_stop_799_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg(v___x_796_, v_as_797_, v_i_boxed_803_, v_stop_boxed_804_, v_b_800_, v___y_801_);
lean_dec_ref(v_as_797_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object* v_a_808_, lean_object* v___x_809_, size_t v_sz_810_, size_t v_i_811_, lean_object* v_bs_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_811_, v_sz_810_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v___x_809_);
lean_dec_ref(v_a_808_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_bs_812_);
lean_ctor_set(v___x_816_, 1, v___y_813_);
return v___x_816_;
}
else
{
lean_object* v_toTreeMap_817_; lean_object* v_v_818_; lean_object* v___x_819_; 
v_toTreeMap_817_ = lean_ctor_get(v_a_808_, 0);
v_v_818_ = lean_array_uget_borrowed(v_bs_812_, v_i_811_);
v___x_819_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_817_, v_v_818_);
if (lean_obj_tag(v___x_819_) == 1)
{
lean_object* v_val_820_; lean_object* v_name_821_; lean_object* v___x_822_; lean_object* v_bs_x27_823_; size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; 
v_val_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_val_820_);
lean_dec_ref_known(v___x_819_, 1);
v_name_821_ = lean_ctor_get(v_val_820_, 1);
lean_inc(v_name_821_);
lean_dec(v_val_820_);
v___x_822_ = lean_unsigned_to_nat(0u);
v_bs_x27_823_ = lean_array_uset(v_bs_812_, v_i_811_, v___x_822_);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_i_811_, v___x_824_);
v___x_826_ = lean_array_uset(v_bs_x27_823_, v_i_811_, v_name_821_);
v_i_811_ = v___x_825_;
v_bs_812_ = v___x_826_;
goto _start;
}
else
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_844_; 
lean_inc(v_v_818_);
lean_dec(v___x_819_);
lean_dec_ref(v_bs_812_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; 
v_unused_845_ = lean_ctor_get(v_a_808_, 1);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_a_808_, 0);
lean_dec(v_unused_846_);
v___x_829_ = v_a_808_;
v_isShared_830_ = v_isSharedCheck_844_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_a_808_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_844_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0));
v___x_832_ = lean_string_append(v___x_809_, v___x_831_);
v___x_833_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_818_, v___x_815_);
v___x_834_ = lean_string_append(v___x_832_, v___x_833_);
lean_dec_ref(v___x_833_);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_836_ = lean_string_append(v___x_834_, v___x_835_);
v___x_837_ = 3;
v___x_838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1, v___x_837_);
v___x_839_ = lean_array_get_size(v___y_813_);
v___x_840_ = lean_array_push(v___y_813_, v___x_838_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 1);
lean_ctor_set(v___x_829_, 1, v___x_840_);
lean_ctor_set(v___x_829_, 0, v___x_839_);
v___x_842_ = v___x_829_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object* v_a_847_, lean_object* v___x_848_, lean_object* v_sz_849_, lean_object* v_i_850_, lean_object* v_bs_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
size_t v_sz_boxed_854_; size_t v_i_boxed_855_; lean_object* v_res_856_; 
v_sz_boxed_854_ = lean_unbox_usize(v_sz_849_);
lean_dec(v_sz_849_);
v_i_boxed_855_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_847_, v___x_848_, v_sz_boxed_854_, v_i_boxed_855_, v_bs_851_, v___y_852_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(lean_object* v_f_857_, lean_object* v_as_858_, size_t v_i_859_, size_t v_stop_860_, lean_object* v_b_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_eq(v_i_859_, v_stop_860_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_array_uget_borrowed(v_as_858_, v_i_859_);
lean_inc_ref(v_f_857_);
lean_inc(v___x_863_);
v___x_864_ = lean_apply_1(v_f_857_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_b_861_);
lean_dec_ref(v_f_857_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; size_t v___x_876_; size_t v___x_877_; 
v_a_873_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_864_, 1);
v___x_874_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_863_);
v___x_875_ = l_Lake_RBArray_insert___redArg(v___x_874_, v_b_861_, v___x_863_, v_a_873_);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_859_, v___x_876_);
v_i_859_ = v___x_877_;
v_b_861_ = v___x_875_;
goto _start;
}
}
else
{
lean_object* v___x_879_; 
lean_dec_ref(v_f_857_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v_b_861_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object* v_f_880_, lean_object* v_as_881_, lean_object* v_i_882_, lean_object* v_stop_883_, lean_object* v_b_884_){
_start:
{
size_t v_i_boxed_885_; size_t v_stop_boxed_886_; lean_object* v_res_887_; 
v_i_boxed_885_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_stop_boxed_886_ = lean_unbox_usize(v_stop_883_);
lean_dec(v_stop_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_880_, v_as_881_, v_i_boxed_885_, v_stop_boxed_886_, v_b_884_);
lean_dec_ref(v_as_881_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_env_888_, lean_object* v_attr_889_, lean_object* v_f_890_){
_start:
{
lean_object* v_entries_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_entries_891_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_889_, v_env_888_);
v___x_892_ = lean_array_get_size(v_entries_891_);
v___x_893_ = l_Lake_RBArray_mkEmpty___redArg(v___x_892_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_nat_dec_lt(v___x_894_, v___x_892_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_entries_891_);
lean_dec_ref(v_f_890_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_893_);
return v___x_896_;
}
else
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((size_t)0ULL);
v___x_898_ = lean_usize_of_nat(v___x_892_);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_890_, v_entries_891_, v___x_897_, v___x_898_, v___x_893_);
lean_dec_ref(v_entries_891_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_env_900_, lean_object* v_attr_901_, lean_object* v_f_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_900_, v_attr_901_, v_f_902_);
lean_dec_ref(v_attr_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_904_, lean_object* v_as_905_, size_t v_i_906_, size_t v_stop_907_, lean_object* v_b_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_eq(v_i_906_, v_stop_907_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_array_uget_borrowed(v_as_905_, v_i_906_);
lean_inc_ref(v_f_904_);
lean_inc(v___x_912_);
v___x_913_ = lean_apply_3(v_f_904_, v___x_912_, v___y_909_, lean_box(0));
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v_a_915_; lean_object* v___x_916_; size_t v___x_917_; size_t v___x_918_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
v_a_915_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_913_, 2);
lean_inc(v___x_912_);
v___x_916_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_912_, v_a_914_, v_b_908_);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_906_, v___x_917_);
v_i_906_ = v___x_918_;
v_b_908_ = v___x_916_;
v___y_909_ = v_a_915_;
goto _start;
}
else
{
lean_object* v_a_920_; lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_b_908_);
lean_dec_ref(v_f_904_);
v_a_920_ = lean_ctor_get(v___x_913_, 0);
v_a_921_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_913_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_inc(v_a_920_);
lean_dec(v___x_913_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v___x_929_; 
lean_dec_ref(v_f_904_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_b_908_);
lean_ctor_set(v___x_929_, 1, v___y_909_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_930_, lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_stop_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; lean_object* v_res_939_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_933_);
lean_dec(v_stop_933_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_930_, v_as_931_, v_i_boxed_937_, v_stop_boxed_938_, v_b_934_, v___y_935_);
lean_dec_ref(v_as_931_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_940_, lean_object* v_attr_941_, lean_object* v_f_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_entries_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_entries_945_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_941_, v_env_940_);
v___x_946_ = lean_box(1);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_array_get_size(v_entries_945_);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec_ref(v_entries_945_);
lean_dec_ref(v_f_942_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_946_);
lean_ctor_set(v___x_950_, 1, v___y_943_);
return v___x_950_;
}
else
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_948_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_942_, v_entries_945_, v___x_951_, v___x_952_, v___x_946_, v___y_943_);
lean_dec_ref(v_entries_945_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_954_, lean_object* v_attr_955_, lean_object* v_f_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_954_, v_attr_955_, v_f_956_, v___y_957_);
lean_dec_ref(v_attr_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v___x_963_, size_t v_sz_964_, size_t v_i_965_, lean_object* v_bs_966_, lean_object* v___y_967_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_usize_dec_lt(v_i_965_, v_sz_964_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec(v___x_963_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_bs_966_);
lean_ctor_set(v___x_970_, 1, v___y_967_);
return v___x_970_;
}
else
{
lean_object* v_v_971_; lean_object* v_pkg_972_; lean_object* v_name_973_; uint8_t v___x_974_; 
v_v_971_ = lean_array_uget(v_bs_966_, v_i_965_);
v_pkg_972_ = lean_ctor_get(v_v_971_, 0);
v_name_973_ = lean_ctor_get(v_v_971_, 1);
v___x_974_ = lean_name_eq(v_pkg_972_, v___x_963_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_inc(v_name_973_);
lean_inc(v_pkg_972_);
lean_dec(v_v_971_);
lean_dec_ref(v_bs_966_);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__0));
v___x_976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_973_, v___x_969_);
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
lean_dec_ref(v___x_976_);
v___x_978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__1));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___x_980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_972_, v___x_969_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__2));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_963_, v___x_969_);
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
v___x_988_ = 3;
v___x_989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_988_);
v___x_990_ = lean_array_get_size(v___y_967_);
v___x_991_ = lean_array_push(v___y_967_, v___x_989_);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v_bs_x27_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v_bs_x27_994_ = lean_array_uset(v_bs_966_, v_i_965_, v___x_993_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_965_, v___x_995_);
v___x_997_ = lean_array_uset(v_bs_x27_994_, v_i_965_, v_v_971_);
v_i_965_ = v___x_996_;
v_bs_966_ = v___x_997_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___boxed(lean_object* v___x_999_, lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_bs_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v___x_999_, v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1002_, v___y_1003_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_1008_, lean_object* v_opts_1009_, lean_object* v_as_1010_, size_t v_sz_1011_, size_t v_i_1012_, lean_object* v_b_1013_){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_usize_dec_lt(v_i_1012_, v_sz_1011_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref(v_env_1008_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_b_1013_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v_a_1017_; lean_object* v___x_1018_; 
v___x_1016_ = l_Lake_instTypeNameModuleFacetDecl;
v_a_1017_ = lean_array_uget_borrowed(v_as_1010_, v_i_1012_);
lean_inc(v_a_1017_);
lean_inc_ref(v_env_1008_);
v___x_1018_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1008_, v_opts_1009_, v___x_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_b_1013_);
lean_dec_ref(v_env_1008_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v_name_1028_; lean_object* v_config_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1040_; 
v_a_1027_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1018_, 1);
v_name_1028_ = lean_ctor_get(v_a_1027_, 0);
v_config_1029_ = lean_ctor_get(v_a_1027_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1031_ = v_a_1027_;
v_isShared_1032_ = v_isSharedCheck_1040_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_config_1029_);
lean_inc(v_name_1028_);
lean_dec(v_a_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1040_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_name_1028_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_config_1029_);
v___x_1034_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; 
v___x_1035_ = lean_array_push(v_b_1013_, v___x_1034_);
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1012_, v___x_1036_);
v_i_1012_ = v___x_1037_;
v_b_1013_ = v___x_1035_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object* v_env_1041_, lean_object* v_opts_1042_, lean_object* v_as_1043_, lean_object* v_sz_1044_, lean_object* v_i_1045_, lean_object* v_b_1046_){
_start:
{
size_t v_sz_boxed_1047_; size_t v_i_boxed_1048_; lean_object* v_res_1049_; 
v_sz_boxed_1047_ = lean_unbox_usize(v_sz_1044_);
lean_dec(v_sz_1044_);
v_i_boxed_1048_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1041_, v_opts_1042_, v_as_1043_, v_sz_boxed_1047_, v_i_boxed_1048_, v_b_1046_);
lean_dec_ref(v_as_1043_);
lean_dec_ref(v_opts_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v_env_1052_, lean_object* v_opts_1053_, lean_object* v___x_1054_, lean_object* v_as_1055_, size_t v_i_1056_, size_t v_stop_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_usize_dec_eq(v_i_1056_, v_stop_1057_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = l_Lake_instImpl_00___x40_Lake_Config_Cache_3424128028____hygCtx___hyg_18_;
v___x_1063_ = lean_array_uget_borrowed(v_as_1055_, v_i_1056_);
lean_inc(v___x_1063_);
lean_inc_ref(v_env_1052_);
v___x_1064_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1052_, v_opts_1053_, v___x_1062_, v___x_1063_);
v___x_1065_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v_name_x3f_1067_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v_name_x3f_1067_ = lean_ctor_get(v_a_1066_, 0);
if (lean_obj_tag(v_name_x3f_1067_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; 
v_val_1068_ = lean_ctor_get(v_name_x3f_1067_, 0);
v___x_1069_ = lean_box(0);
lean_inc(v_val_1068_);
v___x_1070_ = l_Lean_Name_str___override(v___x_1069_, v_val_1068_);
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1070_, v_a_1066_, v_b_1058_);
v___x_1072_ = ((size_t)1ULL);
v___x_1073_ = lean_usize_add(v_i_1056_, v___x_1072_);
v_i_1056_ = v___x_1073_;
v_b_1058_ = v___x_1071_;
goto _start;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec(v_a_1066_);
lean_dec(v_b_1058_);
lean_dec_ref(v_env_1052_);
v___x_1075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0));
v___x_1076_ = lean_string_append(v___x_1054_, v___x_1075_);
v___x_1077_ = 1;
lean_inc(v___x_1063_);
v___x_1078_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1063_, v___x_1077_);
v___x_1079_ = lean_string_append(v___x_1076_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1));
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
v___x_1082_ = 3;
v___x_1083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
v___x_1084_ = lean_array_get_size(v___y_1059_);
v___x_1085_ = lean_array_push(v___y_1059_, v___x_1083_);
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v_b_1058_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_env_1052_);
v_a_1087_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1088_ = lean_io_error_to_string(v_a_1087_);
v___x_1089_ = 3;
v___x_1090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*1, v___x_1089_);
v___x_1091_ = lean_array_get_size(v___y_1059_);
v___x_1092_ = lean_array_push(v___y_1059_, v___x_1090_);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
return v___x_1093_;
}
}
else
{
lean_object* v___x_1094_; 
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_env_1052_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_b_1058_);
lean_ctor_set(v___x_1094_, 1, v___y_1059_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v_env_1095_, lean_object* v_opts_1096_, lean_object* v___x_1097_, lean_object* v_as_1098_, lean_object* v_i_1099_, lean_object* v_stop_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
size_t v_i_boxed_1104_; size_t v_stop_boxed_1105_; lean_object* v_res_1106_; 
v_i_boxed_1104_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_stop_boxed_1105_ = lean_unbox_usize(v_stop_1100_);
lean_dec(v_stop_1100_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v_env_1095_, v_opts_1096_, v___x_1097_, v_as_1098_, v_i_boxed_1104_, v_stop_boxed_1105_, v_b_1101_, v___y_1102_);
lean_dec_ref(v_as_1098_);
lean_dec_ref(v_opts_1096_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v___x_1111_, size_t v_sz_1112_, size_t v_i_1113_, lean_object* v_bs_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_usize_dec_lt(v_i_1113_, v_sz_1112_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_a_1109_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_bs_1114_);
lean_ctor_set(v___x_1118_, 1, v___y_1115_);
return v___x_1118_;
}
else
{
lean_object* v_toTreeMap_1119_; lean_object* v_v_1120_; lean_object* v___x_1121_; lean_object* v_bs_x27_1122_; lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v___x_1130_; 
v_toTreeMap_1119_ = lean_ctor_get(v_a_1109_, 0);
v_v_1120_ = lean_array_uget(v_bs_1114_, v_i_1113_);
v___x_1121_ = lean_unsigned_to_nat(0u);
v_bs_x27_1122_ = lean_array_uset(v_bs_1114_, v_i_1113_, v___x_1121_);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_1119_, v_v_1120_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_val_1131_; lean_object* v_name_1132_; 
lean_dec(v_v_1120_);
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v_name_1132_ = lean_ctor_get(v_val_1131_, 1);
lean_inc(v_name_1132_);
lean_dec(v_val_1131_);
v_a_1124_ = v_name_1132_;
v_a_1125_ = v___y_1115_;
goto v___jp_1123_;
}
else
{
uint8_t v___x_1133_; 
lean_dec(v___x_1130_);
v___x_1133_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_1120_, v_a_1110_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v_bs_x27_1122_);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1109_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1151_ = lean_ctor_get(v_a_1109_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_a_1109_, 0);
lean_dec(v_unused_1152_);
v___x_1135_ = v_a_1109_;
v_isShared_1136_ = v_isSharedCheck_1150_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v_a_1109_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1150_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_1138_ = lean_string_append(v___x_1111_, v___x_1137_);
v___x_1139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1120_, v___x_1117_);
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
lean_dec_ref(v___x_1139_);
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_1142_ = lean_string_append(v___x_1140_, v___x_1141_);
v___x_1143_ = 3;
v___x_1144_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*1, v___x_1143_);
v___x_1145_ = lean_array_get_size(v___y_1115_);
v___x_1146_ = lean_array_push(v___y_1115_, v___x_1144_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
lean_ctor_set(v___x_1135_, 1, v___x_1146_);
lean_ctor_set(v___x_1135_, 0, v___x_1145_);
v___x_1148_ = v___x_1135_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
v_a_1124_ = v_v_1120_;
v_a_1125_ = v___y_1115_;
goto v___jp_1123_;
}
}
v___jp_1123_:
{
size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((size_t)1ULL);
v___x_1127_ = lean_usize_add(v_i_1113_, v___x_1126_);
v___x_1128_ = lean_array_uset(v_bs_x27_1122_, v_i_1113_, v_a_1124_);
v_i_1113_ = v___x_1127_;
v_bs_1114_ = v___x_1128_;
v___y_1115_ = v_a_1125_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v___x_1155_, lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_bs_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1153_, v_a_1154_, v___x_1155_, v_sz_boxed_1161_, v_i_boxed_1162_, v_bs_1158_, v___y_1159_);
lean_dec(v_a_1154_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v___x_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_bs_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref(v___x_1167_);
lean_dec_ref(v_a_1165_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_bs_1170_);
lean_ctor_set(v___x_1174_, 1, v___y_1171_);
return v___x_1174_;
}
else
{
lean_object* v_toTreeMap_1175_; lean_object* v_v_1176_; lean_object* v___x_1177_; lean_object* v_bs_x27_1178_; lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1186_; 
v_toTreeMap_1175_ = lean_ctor_get(v_a_1165_, 0);
v_v_1176_ = lean_array_uget(v_bs_1170_, v_i_1169_);
v___x_1177_ = lean_unsigned_to_nat(0u);
v_bs_x27_1178_ = lean_array_uset(v_bs_1170_, v_i_1169_, v___x_1177_);
v___x_1186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_1175_, v_v_1176_);
if (lean_obj_tag(v___x_1186_) == 1)
{
lean_object* v_val_1187_; lean_object* v_name_1188_; 
lean_dec(v_v_1176_);
v_val_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_name_1188_ = lean_ctor_get(v_val_1187_, 1);
lean_inc(v_name_1188_);
lean_dec(v_val_1187_);
v_a_1180_ = v_name_1188_;
v_a_1181_ = v___y_1171_;
goto v___jp_1179_;
}
else
{
uint8_t v___x_1189_; 
lean_dec(v___x_1186_);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_1176_, v_a_1166_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_bs_x27_1178_);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1207_ = lean_ctor_get(v_a_1165_, 1);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_a_1165_, 0);
lean_dec(v_unused_1208_);
v___x_1191_ = v_a_1165_;
v_isShared_1192_ = v_isSharedCheck_1206_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v_a_1165_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1206_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_1194_ = lean_string_append(v___x_1167_, v___x_1193_);
v___x_1195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1176_, v___x_1173_);
v___x_1196_ = lean_string_append(v___x_1194_, v___x_1195_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0));
v___x_1198_ = lean_string_append(v___x_1196_, v___x_1197_);
v___x_1199_ = 3;
v___x_1200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*1, v___x_1199_);
v___x_1201_ = lean_array_get_size(v___y_1171_);
v___x_1202_ = lean_array_push(v___y_1171_, v___x_1200_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set_tag(v___x_1191_, 1);
lean_ctor_set(v___x_1191_, 1, v___x_1202_);
lean_ctor_set(v___x_1191_, 0, v___x_1201_);
v___x_1204_ = v___x_1191_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
v_a_1180_ = v_v_1176_;
v_a_1181_ = v___y_1171_;
goto v___jp_1179_;
}
}
v___jp_1179_:
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1169_, v___x_1182_);
v___x_1184_ = lean_array_uset(v_bs_x27_1178_, v_i_1169_, v_a_1180_);
v_i_1169_ = v___x_1183_;
v_bs_1170_ = v___x_1184_;
v___y_1171_ = v_a_1181_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v___x_1211_, lean_object* v_sz_1212_, lean_object* v_i_1213_, lean_object* v_bs_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
size_t v_sz_boxed_1217_; size_t v_i_boxed_1218_; lean_object* v_res_1219_; 
v_sz_boxed_1217_ = lean_unbox_usize(v_sz_1212_);
lean_dec(v_sz_1212_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1209_, v_a_1210_, v___x_1211_, v_sz_boxed_1217_, v_i_boxed_1218_, v_bs_1214_, v___y_1215_);
lean_dec(v_a_1210_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_1221_, lean_object* v___x_1222_, size_t v_sz_1223_, size_t v_i_1224_, lean_object* v_bs_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_usize_dec_lt(v_i_1224_, v_sz_1223_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref(v___x_1222_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_bs_1225_);
lean_ctor_set(v___x_1229_, 1, v___y_1226_);
return v___x_1229_;
}
else
{
lean_object* v_v_1230_; lean_object* v___x_1231_; 
v_v_1230_ = lean_array_uget_borrowed(v_bs_1225_, v_i_1224_);
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_1221_, v_v_1230_);
if (lean_obj_tag(v___x_1231_) == 1)
{
lean_object* v_val_1232_; lean_object* v___x_1233_; lean_object* v_bs_x27_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
v_val_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1233_ = lean_unsigned_to_nat(0u);
v_bs_x27_1234_ = lean_array_uset(v_bs_1225_, v_i_1224_, v___x_1233_);
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_add(v_i_1224_, v___x_1235_);
v___x_1237_ = lean_array_uset(v_bs_x27_1234_, v_i_1224_, v_val_1232_);
v_i_1224_ = v___x_1236_;
v_bs_1225_ = v___x_1237_;
goto _start;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_inc(v_v_1230_);
lean_dec(v___x_1231_);
lean_dec_ref(v_bs_1225_);
v___x_1239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_1240_ = lean_string_append(v___x_1222_, v___x_1239_);
v___x_1241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1230_, v___x_1228_);
v___x_1242_ = lean_string_append(v___x_1240_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
v___x_1245_ = 3;
v___x_1246_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set_uint8(v___x_1246_, sizeof(void*)*1, v___x_1245_);
v___x_1247_ = lean_array_get_size(v___y_1226_);
v___x_1248_ = lean_array_push(v___y_1226_, v___x_1246_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_1250_, lean_object* v___x_1251_, lean_object* v_sz_1252_, lean_object* v_i_1253_, lean_object* v_bs_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1252_);
lean_dec(v_sz_1252_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1253_);
lean_dec(v_i_1253_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1250_, v___x_1251_, v_sz_boxed_1257_, v_i_boxed_1258_, v_bs_1254_, v___y_1255_);
lean_dec(v_a_1250_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_1260_, lean_object* v_opts_1261_, lean_object* v_as_1262_, size_t v_sz_1263_, size_t v_i_1264_, lean_object* v_b_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1264_, v_sz_1263_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_env_1260_);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1265_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v_a_1269_; lean_object* v___x_1270_; 
v___x_1268_ = l_Lake_instTypeNamePackageFacetDecl;
v_a_1269_ = lean_array_uget_borrowed(v_as_1262_, v_i_1264_);
lean_inc(v_a_1269_);
lean_inc_ref(v_env_1260_);
v___x_1270_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1260_, v_opts_1261_, v___x_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_b_1265_);
lean_dec_ref(v_env_1260_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v_name_1280_; lean_object* v_config_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1292_; 
v_a_1279_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1270_, 1);
v_name_1280_ = lean_ctor_get(v_a_1279_, 0);
v_config_1281_ = lean_ctor_get(v_a_1279_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_a_1279_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1283_ = v_a_1279_;
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_config_1281_);
lean_inc(v_name_1280_);
lean_dec(v_a_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_name_1280_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_config_1281_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; 
v___x_1287_ = lean_array_push(v_b_1265_, v___x_1286_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_add(v_i_1264_, v___x_1288_);
v_i_1264_ = v___x_1289_;
v_b_1265_ = v___x_1287_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_1293_, lean_object* v_opts_1294_, lean_object* v_as_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_b_1298_){
_start:
{
size_t v_sz_boxed_1299_; size_t v_i_boxed_1300_; lean_object* v_res_1301_; 
v_sz_boxed_1299_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1300_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1293_, v_opts_1294_, v_as_1295_, v_sz_boxed_1299_, v_i_boxed_1300_, v_b_1298_);
lean_dec_ref(v_as_1295_);
lean_dec_ref(v_opts_1294_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_1302_, lean_object* v_opts_1303_, size_t v_sz_1304_, size_t v_i_1305_, lean_object* v_bs_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_usize_dec_lt(v_i_1305_, v_sz_1304_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref(v_env_1302_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_bs_1306_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v_v_1310_; lean_object* v___x_1311_; 
v___x_1309_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
v_v_1310_ = lean_array_uget_borrowed(v_bs_1306_, v_i_1305_);
lean_inc(v_v_1310_);
lean_inc_ref(v_env_1302_);
v___x_1311_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1302_, v_opts_1303_, v___x_1309_, v_v_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_bs_1306_);
lean_dec_ref(v_env_1302_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v_bs_x27_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v_a_1320_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1321_ = lean_unsigned_to_nat(0u);
v_bs_x27_1322_ = lean_array_uset(v_bs_1306_, v_i_1305_, v___x_1321_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1305_, v___x_1323_);
v___x_1325_ = lean_array_uset(v_bs_x27_1322_, v_i_1305_, v_a_1320_);
v_i_1305_ = v___x_1324_;
v_bs_1306_ = v___x_1325_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_1327_, lean_object* v_opts_1328_, lean_object* v_sz_1329_, lean_object* v_i_1330_, lean_object* v_bs_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1329_);
lean_dec(v_sz_1329_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1327_, v_opts_1328_, v_sz_boxed_1332_, v_i_boxed_1333_, v_bs_1331_);
lean_dec_ref(v_opts_1328_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_1335_, lean_object* v_opts_1336_, lean_object* v_as_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_b_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v_env_1335_);
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_b_1340_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v_a_1344_; lean_object* v___x_1345_; 
v___x_1343_ = l_Lake_instTypeNameLibraryFacetDecl;
v_a_1344_ = lean_array_uget_borrowed(v_as_1337_, v_i_1339_);
lean_inc(v_a_1344_);
lean_inc_ref(v_env_1335_);
v___x_1345_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1335_, v_opts_1336_, v___x_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_b_1340_);
lean_dec_ref(v_env_1335_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v_name_1355_; lean_object* v_config_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1367_; 
v_a_1354_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1345_, 1);
v_name_1355_ = lean_ctor_get(v_a_1354_, 0);
v_config_1356_ = lean_ctor_get(v_a_1354_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_a_1354_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1358_ = v_a_1354_;
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_config_1356_);
lean_inc(v_name_1355_);
lean_dec(v_a_1354_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_name_1355_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_config_1356_);
v___x_1361_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; 
v___x_1362_ = lean_array_push(v_b_1340_, v___x_1361_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1339_, v___x_1363_);
v_i_1339_ = v___x_1364_;
v_b_1340_ = v___x_1362_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_1368_, lean_object* v_opts_1369_, lean_object* v_as_1370_, lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_b_1373_){
_start:
{
size_t v_sz_boxed_1374_; size_t v_i_boxed_1375_; lean_object* v_res_1376_; 
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1375_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1368_, v_opts_1369_, v_as_1370_, v_sz_boxed_1374_, v_i_boxed_1375_, v_b_1373_);
lean_dec_ref(v_as_1370_);
lean_dec_ref(v_opts_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1383_, lean_object* v_opts_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1395_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1384_);
lean_inc_ref_n(v_env_1383_, 2);
v___f_1396_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1396_, 0, v_env_1383_);
lean_closure_set(v___f_1396_, 1, v_opts_1384_);
lean_closure_set(v___f_1396_, 2, v___x_1395_);
v___x_1397_ = l_Lake_instTypeNameScriptFn;
v___x_1398_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1383_, v_opts_1384_);
v___x_1399_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_baseName_1401_; lean_object* v_keyName_1402_; lean_object* v_config_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v_baseName_1401_ = lean_ctor_get(v_a_1400_, 0);
v_keyName_1402_ = lean_ctor_get(v_a_1400_, 1);
v_config_1403_ = lean_ctor_get(v_a_1400_, 3);
v___x_1404_ = 0;
lean_inc(v_baseName_1401_);
v___x_1405_ = l_Lean_Name_toString(v_baseName_1401_, v___x_1404_);
v___x_1406_ = lean_box(v___x_1404_);
lean_inc_ref(v_opts_1384_);
lean_inc_ref_n(v_env_1383_, 2);
lean_inc_ref(v___x_1405_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1407_, 0, v___x_1405_);
lean_closure_set(v___f_1407_, 1, v___x_1406_);
lean_closure_set(v___f_1407_, 2, v_env_1383_);
lean_closure_set(v___f_1407_, 3, v_opts_1384_);
lean_closure_set(v___f_1407_, 4, v___x_1397_);
v___x_1408_ = l_Lake_targetAttr;
v___x_1409_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_1383_, v___x_1408_, v___f_1396_);
v___x_1410_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v_toArray_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v_toArray_1412_ = lean_ctor_get(v_a_1411_, 1);
v_sz_1413_ = lean_array_size(v_toArray_1412_);
v___x_1414_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1412_);
lean_inc(v_keyName_1402_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v_keyName_1402_, v_sz_1413_, v___x_1414_, v_toArray_1412_, v_a_1385_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1693_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_a_1417_ = lean_ctor_get(v___x_1415_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1419_ = v___x_1415_;
v_isShared_1420_ = v_isSharedCheck_1693_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1693_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v_a_1459_; lean_object* v_a_1460_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v_a_1485_; lean_object* v_a_1486_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v_a_1526_; lean_object* v_a_1527_; lean_object* v___y_1628_; lean_object* v_a_1629_; lean_object* v___x_1662_; lean_object* v_a_1664_; lean_object* v_a_1665_; uint8_t v___x_1679_; 
v___x_1448_ = lean_box(1);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_array_get_size(v_a_1416_);
v___x_1679_ = lean_nat_dec_lt(v___x_1449_, v___x_1662_);
if (v___x_1679_ == 0)
{
v_a_1664_ = v___x_1448_;
v_a_1665_ = v_a_1417_;
goto v___jp_1663_;
}
else
{
size_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_usize_of_nat(v___x_1662_);
lean_inc_ref(v___x_1405_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg(v___x_1405_, v_a_1416_, v___x_1414_, v___x_1680_, v___x_1448_, v_a_1417_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v_a_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
v_a_1683_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1681_, 2);
v_a_1664_ = v_a_1682_;
v_a_1665_ = v_a_1683_;
goto v___jp_1663_;
}
else
{
lean_object* v_a_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1684_ = lean_ctor_get(v___x_1681_, 0);
v_a_1685_ = lean_ctor_get(v___x_1681_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1681_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_inc(v_a_1684_);
lean_dec(v___x_1681_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
v___jp_1421_:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1432_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1400_);
lean_ctor_set(v___x_1435_, 1, v___y_1426_);
lean_ctor_set(v___x_1435_, 2, v_a_1434_);
lean_ctor_set(v___x_1435_, 3, v_a_1416_);
lean_ctor_set(v___x_1435_, 4, v___y_1424_);
lean_ctor_set(v___x_1435_, 5, v___y_1423_);
lean_ctor_set(v___x_1435_, 6, v___y_1429_);
lean_ctor_set(v___x_1435_, 7, v___y_1425_);
lean_ctor_set(v___x_1435_, 8, v___y_1431_);
lean_ctor_set(v___x_1435_, 9, v___y_1430_);
lean_ctor_set(v___x_1435_, 10, v___y_1422_);
lean_ctor_set(v___x_1435_, 11, v___y_1428_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v___y_1427_);
lean_ctor_set(v___x_1419_, 0, v___x_1435_);
v___x_1437_ = v___x_1419_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___y_1427_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v_a_1416_);
lean_dec(v_a_1400_);
v_a_1439_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1440_ = lean_io_error_to_string(v_a_1439_);
v___x_1441_ = 3;
v___x_1442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*1, v___x_1441_);
v___x_1443_ = lean_array_get_size(v___y_1427_);
v___x_1444_ = lean_array_push(v___y_1427_, v___x_1442_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 1);
lean_ctor_set(v___x_1419_, 1, v___x_1444_);
lean_ctor_set(v___x_1419_, 0, v___x_1443_);
v___x_1446_ = v___x_1419_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
v___jp_1450_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; size_t v_sz_1464_; lean_object* v___x_1465_; 
v___x_1461_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1462_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1383_, 2);
v___x_1463_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1462_, v_env_1383_);
v_sz_1464_ = lean_array_size(v___x_1463_);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1383_, v_opts_1384_, v___x_1463_, v_sz_1464_, v___x_1414_, v___x_1461_);
lean_dec_ref(v___x_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v___y_1422_ = v___y_1452_;
v___y_1423_ = v___y_1451_;
v___y_1424_ = v___y_1453_;
v___y_1425_ = v___y_1454_;
v___y_1426_ = v___y_1455_;
v___y_1427_ = v_a_1460_;
v___y_1428_ = v_a_1459_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___x_1465_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; size_t v_sz_1469_; lean_object* v___x_1470_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1383_, 2);
v___x_1468_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1467_, v_env_1383_);
v_sz_1469_ = lean_array_size(v___x_1468_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1383_, v_opts_1384_, v___x_1468_, v_sz_1469_, v___x_1414_, v_a_1466_);
lean_dec_ref(v___x_1468_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v___y_1422_ = v___y_1452_;
v___y_1423_ = v___y_1451_;
v___y_1424_ = v___y_1453_;
v___y_1425_ = v___y_1454_;
v___y_1426_ = v___y_1455_;
v___y_1427_ = v_a_1460_;
v___y_1428_ = v_a_1459_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___x_1470_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; size_t v_sz_1474_; lean_object* v___x_1475_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1383_);
v___x_1473_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1472_, v_env_1383_);
v_sz_1474_ = lean_array_size(v___x_1473_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1383_, v_opts_1384_, v___x_1473_, v_sz_1474_, v___x_1414_, v_a_1471_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_opts_1384_);
v___y_1422_ = v___y_1452_;
v___y_1423_ = v___y_1451_;
v___y_1424_ = v___y_1453_;
v___y_1425_ = v___y_1454_;
v___y_1426_ = v___y_1455_;
v___y_1427_ = v_a_1460_;
v___y_1428_ = v_a_1459_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1458_;
v___y_1431_ = v___y_1457_;
v___y_1432_ = v___x_1475_;
goto v___jp_1421_;
}
}
}
v___jp_1476_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; size_t v_sz_1489_; lean_object* v___x_1490_; 
v___x_1487_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1383_);
v___x_1488_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1487_, v_env_1383_);
v_sz_1489_ = lean_array_size(v___x_1488_);
lean_inc_ref(v___x_1405_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1411_, v___y_1480_, v___x_1405_, v_sz_1489_, v___x_1414_, v___x_1488_, v_a_1486_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_a_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
v_a_1492_ = lean_ctor_get(v___x_1490_, 1);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1490_, 2);
v___x_1493_ = lean_array_get_size(v_a_1491_);
v___x_1494_ = lean_nat_dec_lt(v___y_1479_, v___x_1493_);
if (v___x_1494_ == 0)
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_nat_dec_lt(v___x_1449_, v___x_1493_);
if (v___x_1495_ == 0)
{
lean_object* v_lintDriver_1496_; 
lean_dec(v_a_1491_);
lean_dec_ref(v___x_1405_);
v_lintDriver_1496_ = lean_ctor_get(v_config_1403_, 14);
lean_inc_ref(v_lintDriver_1496_);
v___y_1451_ = v___y_1477_;
v___y_1452_ = v_a_1485_;
v___y_1453_ = v___y_1478_;
v___y_1454_ = v___y_1480_;
v___y_1455_ = v___y_1481_;
v___y_1456_ = v___y_1482_;
v___y_1457_ = v___y_1484_;
v___y_1458_ = v___y_1483_;
v_a_1459_ = v_lintDriver_1496_;
v_a_1460_ = v_a_1492_;
goto v___jp_1450_;
}
else
{
lean_object* v_lintDriver_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_lintDriver_1497_ = lean_ctor_get(v_config_1403_, 14);
v___x_1498_ = lean_string_utf8_byte_size(v_lintDriver_1497_);
v___x_1499_ = lean_nat_dec_eq(v___x_1498_, v___x_1449_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v___x_1500_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1501_ = lean_string_append(v___x_1405_, v___x_1500_);
v___x_1502_ = 3;
v___x_1503_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*1, v___x_1502_);
v___x_1504_ = lean_array_get_size(v_a_1492_);
v___x_1505_ = lean_array_push(v_a_1492_, v___x_1503_);
v_a_1392_ = v___x_1504_;
v_a_1393_ = v___x_1505_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v___x_1405_);
v___x_1506_ = lean_array_fget(v_a_1491_, v___x_1449_);
lean_dec(v_a_1491_);
v___x_1507_ = l_Lean_Name_toString(v___x_1506_, v___x_1495_);
v___y_1451_ = v___y_1477_;
v___y_1452_ = v_a_1485_;
v___y_1453_ = v___y_1478_;
v___y_1454_ = v___y_1480_;
v___y_1455_ = v___y_1481_;
v___y_1456_ = v___y_1482_;
v___y_1457_ = v___y_1484_;
v___y_1458_ = v___y_1483_;
v_a_1459_ = v___x_1507_;
v_a_1460_ = v_a_1492_;
goto v___jp_1450_;
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v___x_1508_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1509_ = lean_string_append(v___x_1405_, v___x_1508_);
v___x_1510_ = 3;
v___x_1511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*1, v___x_1510_);
v___x_1512_ = lean_array_get_size(v_a_1492_);
v___x_1513_ = lean_array_push(v_a_1492_, v___x_1511_);
v_a_1392_ = v___x_1512_;
v_a_1393_ = v___x_1513_;
goto v___jp_1391_;
}
}
else
{
lean_object* v_a_1514_; lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v_a_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1514_ = lean_ctor_get(v___x_1490_, 0);
v_a_1515_ = lean_ctor_get(v___x_1490_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1490_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_inc(v_a_1514_);
lean_dec(v___x_1490_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1514_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
v___jp_1523_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1383_);
v___x_1529_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1383_, v___x_1528_, v___f_1407_, v_a_1527_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v_a_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; size_t v_sz_1534_; lean_object* v___x_1535_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
v_a_1531_ = lean_ctor_get(v___x_1529_, 1);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1529_, 2);
v___x_1532_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1383_);
v___x_1533_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1532_, v_env_1383_);
v_sz_1534_ = lean_array_size(v___x_1533_);
lean_inc_ref(v___x_1405_);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1530_, v___x_1405_, v_sz_1534_, v___x_1414_, v___x_1533_, v_a_1531_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_a_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; size_t v_sz_1540_; lean_object* v___x_1541_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
v_a_1537_ = lean_ctor_get(v___x_1535_, 1);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1535_, 2);
v___x_1538_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1383_, 2);
v___x_1539_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1538_, v_env_1383_);
v_sz_1540_ = lean_array_size(v___x_1539_);
lean_inc(v_keyName_1402_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1383_, v_opts_1384_, v_keyName_1402_, v_sz_1540_, v___x_1414_, v___x_1539_, v_a_1537_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1599_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_a_1543_ = lean_ctor_get(v___x_1541_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1545_ = v___x_1541_;
v_isShared_1546_ = v_isSharedCheck_1599_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1599_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; size_t v_sz_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1547_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1383_, 2);
v___x_1548_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1547_, v_env_1383_);
v_sz_1549_ = lean_array_size(v___x_1548_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1383_, v_opts_1384_, v_sz_1549_, v___x_1414_, v___x_1548_);
v___x_1551_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1550_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; size_t v_sz_1555_; lean_object* v___x_1556_; 
lean_del_object(v___x_1545_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1383_);
v___x_1554_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1553_, v_env_1383_);
v_sz_1555_ = lean_array_size(v___x_1554_);
lean_inc_ref(v___x_1405_);
lean_inc(v_a_1411_);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1411_, v_a_1530_, v___x_1405_, v_sz_1555_, v___x_1414_, v___x_1554_, v_a_1543_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1556_, 2);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_array_get_size(v_a_1557_);
v___x_1561_ = lean_nat_dec_lt(v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_nat_dec_lt(v___x_1449_, v___x_1560_);
if (v___x_1562_ == 0)
{
lean_object* v_testDriver_1563_; 
lean_dec(v_a_1557_);
v_testDriver_1563_ = lean_ctor_get(v_config_1403_, 12);
lean_inc_ref(v_testDriver_1563_);
v___y_1477_ = v___y_1524_;
v___y_1478_ = v___y_1525_;
v___y_1479_ = v___x_1559_;
v___y_1480_ = v_a_1530_;
v___y_1481_ = v_a_1552_;
v___y_1482_ = v_a_1526_;
v___y_1483_ = v_a_1542_;
v___y_1484_ = v_a_1536_;
v_a_1485_ = v_testDriver_1563_;
v_a_1486_ = v_a_1558_;
goto v___jp_1476_;
}
else
{
lean_object* v_testDriver_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_testDriver_1564_ = lean_ctor_get(v_config_1403_, 12);
v___x_1565_ = lean_string_utf8_byte_size(v_testDriver_1564_);
v___x_1566_ = lean_nat_dec_eq(v___x_1565_, v___x_1449_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_a_1557_);
lean_dec(v_a_1552_);
lean_dec(v_a_1542_);
lean_dec(v_a_1536_);
lean_dec(v_a_1530_);
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v___x_1567_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1568_ = lean_string_append(v___x_1405_, v___x_1567_);
v___x_1569_ = 3;
v___x_1570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*1, v___x_1569_);
v___x_1571_ = lean_array_get_size(v_a_1558_);
v___x_1572_ = lean_array_push(v_a_1558_, v___x_1570_);
v_a_1388_ = v___x_1571_;
v_a_1389_ = v___x_1572_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_array_fget(v_a_1557_, v___x_1449_);
lean_dec(v_a_1557_);
v___x_1574_ = l_Lean_Name_toString(v___x_1573_, v___x_1562_);
v___y_1477_ = v___y_1524_;
v___y_1478_ = v___y_1525_;
v___y_1479_ = v___x_1559_;
v___y_1480_ = v_a_1530_;
v___y_1481_ = v_a_1552_;
v___y_1482_ = v_a_1526_;
v___y_1483_ = v_a_1542_;
v___y_1484_ = v_a_1536_;
v_a_1485_ = v___x_1574_;
v_a_1486_ = v_a_1558_;
goto v___jp_1476_;
}
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_a_1557_);
lean_dec(v_a_1552_);
lean_dec(v_a_1542_);
lean_dec(v_a_1536_);
lean_dec(v_a_1530_);
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v___x_1575_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1576_ = lean_string_append(v___x_1405_, v___x_1575_);
v___x_1577_ = 3;
v___x_1578_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*1, v___x_1577_);
v___x_1579_ = lean_array_get_size(v_a_1558_);
v___x_1580_ = lean_array_push(v_a_1558_, v___x_1578_);
v_a_1388_ = v___x_1579_;
v_a_1389_ = v___x_1580_;
goto v___jp_1387_;
}
}
else
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1552_);
lean_dec(v_a_1542_);
lean_dec(v_a_1536_);
lean_dec(v_a_1530_);
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1581_ = lean_ctor_get(v___x_1556_, 0);
v_a_1582_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1556_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_inc(v_a_1581_);
lean_dec(v___x_1556_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec(v_a_1542_);
lean_dec(v_a_1536_);
lean_dec(v_a_1530_);
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1590_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1591_ = lean_io_error_to_string(v_a_1590_);
v___x_1592_ = 3;
v___x_1593_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*1, v___x_1592_);
v___x_1594_ = lean_array_get_size(v_a_1543_);
v___x_1595_ = lean_array_push(v_a_1543_, v___x_1593_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 1);
lean_ctor_set(v___x_1545_, 1, v___x_1595_);
lean_ctor_set(v___x_1545_, 0, v___x_1594_);
v___x_1597_ = v___x_1545_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_a_1536_);
lean_dec(v_a_1530_);
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1600_ = lean_ctor_get(v___x_1541_, 0);
v_a_1601_ = lean_ctor_get(v___x_1541_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1541_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_inc(v_a_1600_);
lean_dec(v___x_1541_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1600_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_a_1530_);
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1609_ = lean_ctor_get(v___x_1535_, 0);
v_a_1610_ = lean_ctor_get(v___x_1535_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1535_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_inc(v_a_1609_);
lean_dec(v___x_1535_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1609_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_a_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1618_ = lean_ctor_get(v___x_1529_, 0);
v_a_1619_ = lean_ctor_get(v___x_1529_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1529_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_inc(v_a_1618_);
lean_dec(v___x_1529_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1618_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
v___jp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; size_t v_sz_1632_; lean_object* v___x_1633_; 
v___x_1630_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1383_);
v___x_1631_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1630_, v_env_1383_);
v_sz_1632_ = lean_array_size(v___x_1631_);
lean_inc_ref(v___x_1405_);
lean_inc(v_a_1411_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1411_, v___x_1405_, v_sz_1632_, v___x_1414_, v___x_1631_, v_a_1629_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v_a_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
v_a_1635_ = lean_ctor_get(v___x_1633_, 1);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1633_, 2);
v___x_1636_ = l_Lake_cacheServiceAttr;
lean_inc_ref(v_env_1383_);
v___x_1637_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1636_, v_env_1383_);
v___x_1638_ = lean_array_get_size(v___x_1637_);
v___x_1639_ = lean_nat_dec_lt(v___x_1449_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_dec_ref(v___x_1637_);
v___y_1524_ = v_a_1634_;
v___y_1525_ = v___y_1628_;
v_a_1526_ = v___x_1448_;
v_a_1527_ = v_a_1635_;
goto v___jp_1523_;
}
else
{
size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_usize_of_nat(v___x_1638_);
lean_inc_ref(v___x_1405_);
lean_inc_ref(v_env_1383_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v_env_1383_, v_opts_1384_, v___x_1405_, v___x_1637_, v___x_1414_, v___x_1640_, v___x_1448_, v_a_1635_);
lean_dec_ref(v___x_1637_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_a_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
v_a_1643_ = lean_ctor_get(v___x_1641_, 1);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1641_, 2);
v___y_1524_ = v_a_1634_;
v___y_1525_ = v___y_1628_;
v_a_1526_ = v_a_1642_;
v_a_1527_ = v_a_1643_;
goto v___jp_1523_;
}
else
{
lean_object* v_a_1644_; lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1634_);
lean_dec(v___y_1628_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1644_ = lean_ctor_get(v___x_1641_, 0);
v_a_1645_ = lean_ctor_get(v___x_1641_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1641_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_inc(v_a_1644_);
lean_dec(v___x_1641_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v___y_1628_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1653_ = lean_ctor_get(v___x_1633_, 0);
v_a_1654_ = lean_ctor_get(v___x_1633_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1633_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_inc(v_a_1653_);
lean_dec(v___x_1633_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
v___jp_1663_:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_nat_dec_lt(v___x_1449_, v___x_1662_);
if (v___x_1666_ == 0)
{
v___y_1628_ = v_a_1664_;
v_a_1629_ = v_a_1665_;
goto v___jp_1627_;
}
else
{
size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_usize_of_nat(v___x_1662_);
lean_inc_ref(v___x_1405_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1405_, v_a_1416_, v___x_1414_, v___x_1667_, v___x_1448_, v_a_1665_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 1);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 2);
v___y_1628_ = v_a_1664_;
v_a_1629_ = v_a_1669_;
goto v___jp_1627_;
}
else
{
lean_object* v_a_1670_; lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1664_);
lean_del_object(v___x_1419_);
lean_dec(v_a_1416_);
lean_dec(v_a_1411_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1670_ = lean_ctor_get(v___x_1668_, 0);
v_a_1671_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1668_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_inc(v_a_1670_);
lean_dec(v___x_1668_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1670_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_a_1411_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1694_ = lean_ctor_get(v___x_1415_, 0);
v_a_1695_ = lean_ctor_get(v___x_1415_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1415_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_inc(v_a_1694_);
lean_dec(v___x_1415_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1694_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1400_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1703_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1704_ = lean_io_error_to_string(v_a_1703_);
v___x_1705_ = 3;
v___x_1706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*1, v___x_1705_);
v___x_1707_ = lean_array_get_size(v_a_1385_);
v___x_1708_ = lean_array_push(v_a_1385_, v___x_1706_);
v___x_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
return v___x_1709_;
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref(v___f_1396_);
lean_dec_ref(v_opts_1384_);
lean_dec_ref(v_env_1383_);
v_a_1710_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1711_ = lean_io_error_to_string(v_a_1710_);
v___x_1712_ = 3;
v___x_1713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*1, v___x_1712_);
v___x_1714_ = lean_array_get_size(v_a_1385_);
v___x_1715_ = lean_array_push(v_a_1385_, v___x_1713_);
v___x_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
return v___x_1716_;
}
v___jp_1387_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1388_);
lean_ctor_set(v___x_1390_, 1, v_a_1389_);
return v___x_1390_;
}
v___jp_1391_:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_a_1392_);
lean_ctor_set(v___x_1394_, 1, v_a_1393_);
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1717_, lean_object* v_opts_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1717_, v_opts_1718_, v_a_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1722_, lean_object* v_inst_1723_, lean_object* v_t_1724_, lean_object* v_k_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_t_1724_, v_k_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1727_, lean_object* v_inst_1728_, lean_object* v_t_1729_, lean_object* v_k_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1727_, v_inst_1728_, v_t_1729_, v_k_1730_);
lean_dec(v_k_1730_);
lean_dec(v_t_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object* v_00_u03b2_1732_, lean_object* v_k_1733_, lean_object* v_v_1734_, lean_object* v_t_1735_, lean_object* v_hl_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_1733_, v_v_1734_, v_t_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1738_, lean_object* v_env_1739_, lean_object* v_attr_1740_, lean_object* v_f_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_1739_, v_attr_1740_, v_f_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1743_, lean_object* v_env_1744_, lean_object* v_attr_1745_, lean_object* v_f_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1743_, v_env_1744_, v_attr_1745_, v_f_1746_);
lean_dec_ref(v_attr_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1748_, lean_object* v_t_1749_, lean_object* v_k_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1749_, v_k_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1752_, lean_object* v_t_1753_, lean_object* v_k_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1752_, v_t_1753_, v_k_1754_);
lean_dec(v_k_1754_);
lean_dec(v_t_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1756_, lean_object* v_env_1757_, lean_object* v_attr_1758_, lean_object* v_f_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1757_, v_attr_1758_, v_f_1759_, v___y_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1763_, lean_object* v_env_1764_, lean_object* v_attr_1765_, lean_object* v_f_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1763_, v_env_1764_, v_attr_1765_, v_f_1766_, v___y_1767_);
lean_dec_ref(v_attr_1765_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18(lean_object* v___x_1770_, lean_object* v___x_1771_, lean_object* v_as_1772_, size_t v_i_1773_, size_t v_stop_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___redArg(v___x_1770_, v_as_1772_, v_i_1773_, v_stop_1774_, v_b_1775_, v___y_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18___boxed(lean_object* v___x_1779_, lean_object* v___x_1780_, lean_object* v_as_1781_, lean_object* v_i_1782_, lean_object* v_stop_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
size_t v_i_boxed_1787_; size_t v_stop_boxed_1788_; lean_object* v_res_1789_; 
v_i_boxed_1787_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_stop_boxed_1788_ = lean_unbox_usize(v_stop_1783_);
lean_dec(v_stop_1783_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__18(v___x_1779_, v___x_1780_, v_as_1781_, v_i_boxed_1787_, v_stop_boxed_1788_, v_b_1784_, v___y_1785_);
lean_dec_ref(v_as_1781_);
lean_dec(v___x_1780_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(lean_object* v_00_u03b2_1790_, lean_object* v_f_1791_, lean_object* v_as_1792_, size_t v_i_1793_, size_t v_stop_1794_, lean_object* v_b_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_1791_, v_as_1792_, v_i_1793_, v_stop_1794_, v_b_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1797_, lean_object* v_f_1798_, lean_object* v_as_1799_, lean_object* v_i_1800_, lean_object* v_stop_1801_, lean_object* v_b_1802_){
_start:
{
size_t v_i_boxed_1803_; size_t v_stop_boxed_1804_; lean_object* v_res_1805_; 
v_i_boxed_1803_ = lean_unbox_usize(v_i_1800_);
lean_dec(v_i_1800_);
v_stop_boxed_1804_ = lean_unbox_usize(v_stop_1801_);
lean_dec(v_stop_1801_);
v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(v_00_u03b2_1797_, v_f_1798_, v_as_1799_, v_i_boxed_1803_, v_stop_boxed_1804_, v_b_1802_);
lean_dec_ref(v_as_1799_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1806_, lean_object* v_f_1807_, lean_object* v_as_1808_, size_t v_i_1809_, size_t v_stop_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1807_, v_as_1808_, v_i_1809_, v_stop_1810_, v_b_1811_, v___y_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1815_, lean_object* v_f_1816_, lean_object* v_as_1817_, lean_object* v_i_1818_, lean_object* v_stop_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
size_t v_i_boxed_1823_; size_t v_stop_boxed_1824_; lean_object* v_res_1825_; 
v_i_boxed_1823_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_stop_boxed_1824_ = lean_unbox_usize(v_stop_1819_);
lean_dec(v_stop_1819_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1815_, v_f_1816_, v_as_1817_, v_i_boxed_1823_, v_stop_boxed_1824_, v_b_1820_, v___y_1821_);
lean_dec_ref(v_as_1817_);
return v_res_1825_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakefileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_AttributesCore(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LakefileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Lean_Eval(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Config_LakefileConfig(uint8_t builtin);
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lake_DSL_AttributesCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LakefileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Lean_Eval(builtin);
}
#ifdef __cplusplus
}
#endif
