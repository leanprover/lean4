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
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
extern lean_object* l_Lake_defaultTargetAttr;
extern lean_object* l_Lake_scriptAttr;
extern lean_object* l_Lake_defaultScriptAttr;
extern lean_object* l_Lake_postUpdateAttr;
extern lean_object* l_Lake_packageDepAttr;
extern lean_object* l_Lake_testDriverAttr;
extern lean_object* l_Lake_LeanExe_keyword;
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "post-update hook was defined in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "', but was registered in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": executable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' has the same root module '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' as executable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' was already defined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "', but then redefined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_49115__boxed_319_; lean_object* v_res_320_; 
v___x_49115__boxed_319_ = lean_unbox(v___x_312_);
v_res_320_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_311_, v___x_49115__boxed_319_, v_env_313_, v_opts_314_, v___x_315_, v_scriptName_316_, v___y_317_);
lean_dec_ref(v_opts_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object* v_env_323_, lean_object* v_opts_324_, lean_object* v___x_325_, size_t v_sz_326_, size_t v_i_327_, lean_object* v_bs_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_a_332_; lean_object* v_a_333_; uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v___x_325_);
lean_dec_ref(v_env_323_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_bs_328_);
lean_ctor_set(v___x_336_, 1, v___y_329_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v_v_338_; lean_object* v___x_339_; 
v___x_337_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_338_ = lean_array_uget_borrowed(v_bs_328_, v_i_327_);
lean_inc(v_v_338_);
lean_inc_ref(v_env_323_);
v___x_339_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_323_, v_opts_324_, v___x_337_, v_v_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref(v_bs_328_);
lean_dec(v___x_325_);
lean_dec_ref(v_env_323_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = 3;
v___x_342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_342_, 0, v_a_340_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*1, v___x_341_);
v___x_343_ = lean_array_get_size(v___y_329_);
v___x_344_ = lean_array_push(v___y_329_, v___x_342_);
v_a_332_ = v___x_343_;
v_a_333_ = v___x_344_;
goto v___jp_331_;
}
else
{
lean_object* v_a_345_; lean_object* v_pkg_346_; lean_object* v_fn_347_; uint8_t v___x_348_; 
v_a_345_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_339_, 1);
v_pkg_346_ = lean_ctor_get(v_a_345_, 0);
lean_inc(v_pkg_346_);
v_fn_347_ = lean_ctor_get(v_a_345_, 1);
lean_inc_ref(v_fn_347_);
lean_dec(v_a_345_);
v___x_348_ = lean_name_eq(v_pkg_346_, v___x_325_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_fn_347_);
lean_dec_ref(v_bs_328_);
lean_dec_ref(v_env_323_);
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0));
v___x_350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_346_, v___x_335_);
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___x_354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_325_, v___x_335_);
v___x_355_ = lean_string_append(v___x_353_, v___x_354_);
lean_dec_ref(v___x_354_);
v___x_356_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_357_ = lean_string_append(v___x_355_, v___x_356_);
v___x_358_ = 3;
v___x_359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v___x_358_);
v___x_360_ = lean_array_get_size(v___y_329_);
v___x_361_ = lean_array_push(v___y_329_, v___x_359_);
v_a_332_ = v___x_360_;
v_a_333_ = v___x_361_;
goto v___jp_331_;
}
else
{
lean_object* v___x_362_; lean_object* v_bs_x27_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; 
lean_dec(v_pkg_346_);
v___x_362_ = lean_unsigned_to_nat(0u);
v_bs_x27_363_ = lean_array_uset(v_bs_328_, v_i_327_, v___x_362_);
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_327_, v___x_364_);
v___x_366_ = lean_array_uset(v_bs_x27_363_, v_i_327_, v_fn_347_);
v_i_327_ = v___x_365_;
v_bs_328_ = v___x_366_;
goto _start;
}
}
}
v___jp_331_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v_a_332_);
lean_ctor_set(v___x_334_, 1, v_a_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object* v_env_368_, lean_object* v_opts_369_, lean_object* v___x_370_, lean_object* v_sz_371_, lean_object* v_i_372_, lean_object* v_bs_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
size_t v_sz_boxed_376_; size_t v_i_boxed_377_; lean_object* v_res_378_; 
v_sz_boxed_376_ = lean_unbox_usize(v_sz_371_);
lean_dec(v_sz_371_);
v_i_boxed_377_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_368_, v_opts_369_, v___x_370_, v_sz_boxed_376_, v_i_boxed_377_, v_bs_373_, v___y_374_);
lean_dec_ref(v_opts_369_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object* v_t_379_, lean_object* v_k_380_){
_start:
{
if (lean_obj_tag(v_t_379_) == 0)
{
lean_object* v_k_381_; lean_object* v_v_382_; lean_object* v_l_383_; lean_object* v_r_384_; uint8_t v___x_385_; 
v_k_381_ = lean_ctor_get(v_t_379_, 1);
v_v_382_ = lean_ctor_get(v_t_379_, 2);
v_l_383_ = lean_ctor_get(v_t_379_, 3);
v_r_384_ = lean_ctor_get(v_t_379_, 4);
v___x_385_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_380_, v_k_381_);
switch(v___x_385_)
{
case 0:
{
v_t_379_ = v_l_383_;
goto _start;
}
case 1:
{
lean_object* v___x_387_; 
lean_inc(v_v_382_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v_v_382_);
return v___x_387_;
}
default: 
{
v_t_379_ = v_r_384_;
goto _start;
}
}
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_390_, lean_object* v_k_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_390_, v_k_391_);
lean_dec(v_k_391_);
lean_dec(v_t_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object* v_a_395_, lean_object* v___x_396_, size_t v_sz_397_, size_t v_i_398_, lean_object* v_bs_399_, lean_object* v___y_400_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_usize_dec_lt(v_i_398_, v_sz_397_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
lean_dec_ref(v___x_396_);
lean_dec_ref(v_a_395_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_bs_399_);
lean_ctor_set(v___x_403_, 1, v___y_400_);
return v___x_403_;
}
else
{
lean_object* v_toTreeMap_404_; lean_object* v_v_405_; lean_object* v___x_406_; 
v_toTreeMap_404_ = lean_ctor_get(v_a_395_, 0);
v_v_405_ = lean_array_uget_borrowed(v_bs_399_, v_i_398_);
v___x_406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_404_, v_v_405_);
if (lean_obj_tag(v___x_406_) == 1)
{
lean_object* v_val_407_; lean_object* v_name_408_; lean_object* v___x_409_; lean_object* v_bs_x27_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v_val_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_406_, 1);
v_name_408_ = lean_ctor_get(v_val_407_, 1);
lean_inc(v_name_408_);
lean_dec(v_val_407_);
v___x_409_ = lean_unsigned_to_nat(0u);
v_bs_x27_410_ = lean_array_uset(v_bs_399_, v_i_398_, v___x_409_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_398_, v___x_411_);
v___x_413_ = lean_array_uset(v_bs_x27_410_, v_i_398_, v_name_408_);
v_i_398_ = v___x_412_;
v_bs_399_ = v___x_413_;
goto _start;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_431_; 
lean_inc(v_v_405_);
lean_dec(v___x_406_);
lean_dec_ref(v_bs_399_);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; 
v_unused_432_ = lean_ctor_get(v_a_395_, 1);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_a_395_, 0);
lean_dec(v_unused_433_);
v___x_416_ = v_a_395_;
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_a_395_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0));
v___x_419_ = lean_string_append(v___x_396_, v___x_418_);
v___x_420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_405_, v___x_402_);
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
lean_dec_ref(v___x_420_);
v___x_422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
v___x_424_ = 3;
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
v___x_426_ = lean_array_get_size(v___y_400_);
v___x_427_ = lean_array_push(v___y_400_, v___x_425_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 1, v___x_427_);
lean_ctor_set(v___x_416_, 0, v___x_426_);
v___x_429_ = v___x_416_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object* v_a_434_, lean_object* v___x_435_, lean_object* v_sz_436_, lean_object* v_i_437_, lean_object* v_bs_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
size_t v_sz_boxed_441_; size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_sz_boxed_441_ = lean_unbox_usize(v_sz_436_);
lean_dec(v_sz_436_);
v_i_boxed_442_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_434_, v___x_435_, v_sz_boxed_441_, v_i_boxed_442_, v_bs_438_, v___y_439_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(lean_object* v_f_444_, lean_object* v_as_445_, size_t v_i_446_, size_t v_stop_447_, lean_object* v_b_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_eq(v_i_446_, v_stop_447_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_array_uget_borrowed(v_as_445_, v_i_446_);
lean_inc_ref(v_f_444_);
lean_inc(v___x_450_);
v___x_451_ = lean_apply_1(v_f_444_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_b_448_);
lean_dec_ref(v_f_444_);
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_461_; lean_object* v___x_462_; size_t v___x_463_; size_t v___x_464_; 
v_a_460_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_451_, 1);
v___x_461_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_450_);
v___x_462_ = l_Lake_RBArray_insert___redArg(v___x_461_, v_b_448_, v___x_450_, v_a_460_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_446_, v___x_463_);
v_i_446_ = v___x_464_;
v_b_448_ = v___x_462_;
goto _start;
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v_f_444_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_b_448_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object* v_f_467_, lean_object* v_as_468_, lean_object* v_i_469_, lean_object* v_stop_470_, lean_object* v_b_471_){
_start:
{
size_t v_i_boxed_472_; size_t v_stop_boxed_473_; lean_object* v_res_474_; 
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_stop_boxed_473_ = lean_unbox_usize(v_stop_470_);
lean_dec(v_stop_470_);
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_467_, v_as_468_, v_i_boxed_472_, v_stop_boxed_473_, v_b_471_);
lean_dec_ref(v_as_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_env_475_, lean_object* v_attr_476_, lean_object* v_f_477_){
_start:
{
lean_object* v_entries_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_entries_478_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_476_, v_env_475_);
v___x_479_ = lean_array_get_size(v_entries_478_);
v___x_480_ = l_Lake_RBArray_mkEmpty___redArg(v___x_479_);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_nat_dec_lt(v___x_481_, v___x_479_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_entries_478_);
lean_dec_ref(v_f_477_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_480_);
return v___x_483_;
}
else
{
size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((size_t)0ULL);
v___x_485_ = lean_usize_of_nat(v___x_479_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_477_, v_entries_478_, v___x_484_, v___x_485_, v___x_480_);
lean_dec_ref(v_entries_478_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_env_487_, lean_object* v_attr_488_, lean_object* v_f_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_487_, v_attr_488_, v_f_489_);
lean_dec_ref(v_attr_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_491_, lean_object* v_as_492_, size_t v_i_493_, size_t v_stop_494_, lean_object* v_b_495_, lean_object* v___y_496_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_eq(v_i_493_, v_stop_494_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_array_uget_borrowed(v_as_492_, v_i_493_);
lean_inc_ref(v_f_491_);
lean_inc(v___x_499_);
v___x_500_ = lean_apply_3(v_f_491_, v___x_499_, v___y_496_, lean_box(0));
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_a_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
v_a_502_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_500_, 2);
lean_inc(v___x_499_);
v___x_503_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_499_, v_a_501_, v_b_495_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_493_, v___x_504_);
v_i_493_ = v___x_505_;
v_b_495_ = v___x_503_;
v___y_496_ = v_a_502_;
goto _start;
}
else
{
lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_b_495_);
lean_dec_ref(v_f_491_);
v_a_507_ = lean_ctor_get(v___x_500_, 0);
v_a_508_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_500_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_inc(v_a_507_);
lean_dec(v___x_500_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_507_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v___x_516_; 
lean_dec_ref(v_f_491_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_b_495_);
lean_ctor_set(v___x_516_, 1, v___y_496_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_517_, lean_object* v_as_518_, lean_object* v_i_519_, lean_object* v_stop_520_, lean_object* v_b_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
size_t v_i_boxed_524_; size_t v_stop_boxed_525_; lean_object* v_res_526_; 
v_i_boxed_524_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_stop_boxed_525_ = lean_unbox_usize(v_stop_520_);
lean_dec(v_stop_520_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_517_, v_as_518_, v_i_boxed_524_, v_stop_boxed_525_, v_b_521_, v___y_522_);
lean_dec_ref(v_as_518_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_527_, lean_object* v_attr_528_, lean_object* v_f_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_entries_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_entries_532_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_528_, v_env_527_);
v___x_533_ = lean_box(1);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_array_get_size(v_entries_532_);
v___x_536_ = lean_nat_dec_lt(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec_ref(v_entries_532_);
lean_dec_ref(v_f_529_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_533_);
lean_ctor_set(v___x_537_, 1, v___y_530_);
return v___x_537_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_535_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_529_, v_entries_532_, v___x_538_, v___x_539_, v___x_533_, v___y_530_);
lean_dec_ref(v_entries_532_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_541_, lean_object* v_attr_542_, lean_object* v_f_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_541_, v_attr_542_, v_f_543_, v___y_544_);
lean_dec_ref(v_attr_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v___x_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_bs_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec(v___x_550_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_bs_553_);
lean_ctor_set(v___x_557_, 1, v___y_554_);
return v___x_557_;
}
else
{
lean_object* v_v_558_; lean_object* v_pkg_559_; lean_object* v_name_560_; uint8_t v___x_561_; 
v_v_558_ = lean_array_uget(v_bs_553_, v_i_552_);
v_pkg_559_ = lean_ctor_get(v_v_558_, 0);
v_name_560_ = lean_ctor_get(v_v_558_, 1);
v___x_561_ = lean_name_eq(v_pkg_559_, v___x_550_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_inc(v_name_560_);
lean_inc(v_pkg_559_);
lean_dec(v_v_558_);
lean_dec_ref(v_bs_553_);
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__0));
v___x_563_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_560_, v___x_556_);
v___x_564_ = lean_string_append(v___x_562_, v___x_563_);
lean_dec_ref(v___x_563_);
v___x_565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__1));
v___x_566_ = lean_string_append(v___x_564_, v___x_565_);
v___x_567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_559_, v___x_556_);
v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
lean_dec_ref(v___x_567_);
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__2));
v___x_570_ = lean_string_append(v___x_568_, v___x_569_);
v___x_571_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_550_, v___x_556_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
v___x_575_ = 3;
v___x_576_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*1, v___x_575_);
v___x_577_ = lean_array_get_size(v___y_554_);
v___x_578_ = lean_array_push(v___y_554_, v___x_576_);
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v_bs_x27_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v_bs_x27_581_ = lean_array_uset(v_bs_553_, v_i_552_, v___x_580_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_552_, v___x_582_);
v___x_584_ = lean_array_uset(v_bs_x27_581_, v_i_552_, v_v_558_);
v_i_552_ = v___x_583_;
v_bs_553_ = v___x_584_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___boxed(lean_object* v___x_586_, lean_object* v_sz_587_, lean_object* v_i_588_, lean_object* v_bs_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_587_);
lean_dec(v_sz_587_);
v_i_boxed_593_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v___x_586_, v_sz_boxed_592_, v_i_boxed_593_, v_bs_589_, v___y_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_595_, lean_object* v_opts_596_, lean_object* v_as_597_, size_t v_sz_598_, size_t v_i_599_, lean_object* v_b_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_lt(v_i_599_, v_sz_598_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_env_595_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_b_600_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_a_604_; lean_object* v___x_605_; 
v___x_603_ = l_Lake_instTypeNameModuleFacetDecl;
v_a_604_ = lean_array_uget_borrowed(v_as_597_, v_i_599_);
lean_inc(v_a_604_);
lean_inc_ref(v_env_595_);
v___x_605_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_595_, v_opts_596_, v___x_603_, v_a_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_b_600_);
lean_dec_ref(v_env_595_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v_name_615_; lean_object* v_config_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_627_; 
v_a_614_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_605_, 1);
v_name_615_ = lean_ctor_get(v_a_614_, 0);
v_config_616_ = lean_ctor_get(v_a_614_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_618_ = v_a_614_;
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_config_616_);
lean_inc(v_name_615_);
lean_dec(v_a_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_name_615_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_config_616_);
v___x_621_ = v_reuseFailAlloc_626_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; 
v___x_622_ = lean_array_push(v_b_600_, v___x_621_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_599_, v___x_623_);
v_i_599_ = v___x_624_;
v_b_600_ = v___x_622_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object* v_env_628_, lean_object* v_opts_629_, lean_object* v_as_630_, lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_b_633_){
_start:
{
size_t v_sz_boxed_634_; size_t v_i_boxed_635_; lean_object* v_res_636_; 
v_sz_boxed_634_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_635_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_628_, v_opts_629_, v_as_630_, v_sz_boxed_634_, v_i_boxed_635_, v_b_633_);
lean_dec_ref(v_as_630_);
lean_dec_ref(v_opts_629_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v___x_640_, lean_object* v_as_641_, size_t v_i_642_, size_t v_stop_643_, lean_object* v_b_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_a_648_; lean_object* v_a_649_; uint8_t v___x_653_; 
v___x_653_ = lean_usize_dec_eq(v_i_642_, v_stop_643_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v_name_655_; lean_object* v_kind_656_; lean_object* v_config_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_654_ = lean_array_uget_borrowed(v_as_641_, v_i_642_);
v_name_655_ = lean_ctor_get(v___x_654_, 1);
v_kind_656_ = lean_ctor_get(v___x_654_, 2);
v_config_657_ = lean_ctor_get(v___x_654_, 3);
v___x_658_ = l_Lake_LeanExe_keyword;
v___x_659_ = lean_name_eq(v_kind_656_, v___x_658_);
if (v___x_659_ == 0)
{
v_a_648_ = v_b_644_;
v_a_649_ = v___y_645_;
goto v___jp_647_;
}
else
{
lean_object* v_root_660_; lean_object* v___x_661_; 
v_root_660_ = lean_ctor_get(v_config_657_, 2);
v___x_661_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_644_, v_root_660_);
if (lean_obj_tag(v___x_661_) == 1)
{
lean_object* v_val_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v_b_644_);
v_val_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0));
v___x_664_ = lean_string_append(v___x_640_, v___x_663_);
lean_inc(v_name_655_);
v___x_665_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_655_, v___x_659_);
v___x_666_ = lean_string_append(v___x_664_, v___x_665_);
lean_dec_ref(v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1));
v___x_668_ = lean_string_append(v___x_666_, v___x_667_);
lean_inc(v_root_660_);
v___x_669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_660_, v___x_659_);
v___x_670_ = lean_string_append(v___x_668_, v___x_669_);
lean_dec_ref(v___x_669_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2));
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
v___x_673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_662_, v___x_659_);
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
v___x_677_ = 3;
v___x_678_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*1, v___x_677_);
v___x_679_ = lean_array_get_size(v___y_645_);
v___x_680_ = lean_array_push(v___y_645_, v___x_678_);
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; 
lean_dec(v___x_661_);
lean_inc(v_name_655_);
lean_inc(v_root_660_);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_660_, v_name_655_, v_b_644_);
v_a_648_ = v___x_682_;
v_a_649_ = v___y_645_;
goto v___jp_647_;
}
}
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v___x_640_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_b_644_);
lean_ctor_set(v___x_683_, 1, v___y_645_);
return v___x_683_;
}
v___jp_647_:
{
size_t v___x_650_; size_t v___x_651_; 
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_642_, v___x_650_);
v_i_642_ = v___x_651_;
v_b_644_ = v_a_648_;
v___y_645_ = v_a_649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v___x_684_, lean_object* v_as_685_, lean_object* v_i_686_, lean_object* v_stop_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
size_t v_i_boxed_691_; size_t v_stop_boxed_692_; lean_object* v_res_693_; 
v_i_boxed_691_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_stop_boxed_692_ = lean_unbox_usize(v_stop_687_);
lean_dec(v_stop_687_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_684_, v_as_685_, v_i_boxed_691_, v_stop_boxed_692_, v_b_688_, v___y_689_);
lean_dec_ref(v_as_685_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v___x_698_, size_t v_sz_699_, size_t v_i_700_, lean_object* v_bs_701_, lean_object* v___y_702_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = lean_usize_dec_lt(v_i_700_, v_sz_699_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec_ref(v___x_698_);
lean_dec_ref(v_a_696_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_bs_701_);
lean_ctor_set(v___x_705_, 1, v___y_702_);
return v___x_705_;
}
else
{
lean_object* v_toTreeMap_706_; lean_object* v_v_707_; lean_object* v___x_708_; lean_object* v_bs_x27_709_; lean_object* v_a_711_; lean_object* v_a_712_; lean_object* v___x_717_; 
v_toTreeMap_706_ = lean_ctor_get(v_a_696_, 0);
v_v_707_ = lean_array_uget(v_bs_701_, v_i_700_);
v___x_708_ = lean_unsigned_to_nat(0u);
v_bs_x27_709_ = lean_array_uset(v_bs_701_, v_i_700_, v___x_708_);
v___x_717_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_706_, v_v_707_);
if (lean_obj_tag(v___x_717_) == 1)
{
lean_object* v_val_718_; lean_object* v_name_719_; 
lean_dec(v_v_707_);
v_val_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v___x_717_, 1);
v_name_719_ = lean_ctor_get(v_val_718_, 1);
lean_inc(v_name_719_);
lean_dec(v_val_718_);
v_a_711_ = v_name_719_;
v_a_712_ = v___y_702_;
goto v___jp_710_;
}
else
{
uint8_t v___x_720_; 
lean_dec(v___x_717_);
v___x_720_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_707_, v_a_697_);
if (v___x_720_ == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_bs_x27_709_);
v_isSharedCheck_737_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; lean_object* v_unused_739_; 
v_unused_738_ = lean_ctor_get(v_a_696_, 1);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_a_696_, 0);
lean_dec(v_unused_739_);
v___x_722_ = v_a_696_;
v_isShared_723_ = v_isSharedCheck_737_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_a_696_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_737_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_725_ = lean_string_append(v___x_698_, v___x_724_);
v___x_726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_707_, v___x_704_);
v___x_727_ = lean_string_append(v___x_725_, v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = 3;
v___x_731_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_730_);
v___x_732_ = lean_array_get_size(v___y_702_);
v___x_733_ = lean_array_push(v___y_702_, v___x_731_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
lean_ctor_set(v___x_722_, 1, v___x_733_);
lean_ctor_set(v___x_722_, 0, v___x_732_);
v___x_735_ = v___x_722_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
v_a_711_ = v_v_707_;
v_a_712_ = v___y_702_;
goto v___jp_710_;
}
}
v___jp_710_:
{
size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_add(v_i_700_, v___x_713_);
v___x_715_ = lean_array_uset(v_bs_x27_709_, v_i_700_, v_a_711_);
v_i_700_ = v___x_714_;
v_bs_701_ = v___x_715_;
v___y_702_ = v_a_712_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v___x_742_, lean_object* v_sz_743_, lean_object* v_i_744_, lean_object* v_bs_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
size_t v_sz_boxed_748_; size_t v_i_boxed_749_; lean_object* v_res_750_; 
v_sz_boxed_748_ = lean_unbox_usize(v_sz_743_);
lean_dec(v_sz_743_);
v_i_boxed_749_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_res_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_740_, v_a_741_, v___x_742_, v_sz_boxed_748_, v_i_boxed_749_, v_bs_745_, v___y_746_);
lean_dec(v_a_741_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v___x_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_bs_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_lt(v_i_756_, v_sz_755_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec_ref(v___x_754_);
lean_dec_ref(v_a_752_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_bs_757_);
lean_ctor_set(v___x_761_, 1, v___y_758_);
return v___x_761_;
}
else
{
lean_object* v_toTreeMap_762_; lean_object* v_v_763_; lean_object* v___x_764_; lean_object* v_bs_x27_765_; lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_773_; 
v_toTreeMap_762_ = lean_ctor_get(v_a_752_, 0);
v_v_763_ = lean_array_uget(v_bs_757_, v_i_756_);
v___x_764_ = lean_unsigned_to_nat(0u);
v_bs_x27_765_ = lean_array_uset(v_bs_757_, v_i_756_, v___x_764_);
v___x_773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_762_, v_v_763_);
if (lean_obj_tag(v___x_773_) == 1)
{
lean_object* v_val_774_; lean_object* v_name_775_; 
lean_dec(v_v_763_);
v_val_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v___x_773_, 1);
v_name_775_ = lean_ctor_get(v_val_774_, 1);
lean_inc(v_name_775_);
lean_dec(v_val_774_);
v_a_767_ = v_name_775_;
v_a_768_ = v___y_758_;
goto v___jp_766_;
}
else
{
uint8_t v___x_776_; 
lean_dec(v___x_773_);
v___x_776_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_763_, v_a_753_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_bs_x27_765_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_794_ = lean_ctor_get(v_a_752_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_a_752_, 0);
lean_dec(v_unused_795_);
v___x_778_ = v_a_752_;
v_isShared_779_ = v_isSharedCheck_793_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_a_752_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_793_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_781_ = lean_string_append(v___x_754_, v___x_780_);
v___x_782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_763_, v___x_760_);
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___x_786_ = 3;
v___x_787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*1, v___x_786_);
v___x_788_ = lean_array_get_size(v___y_758_);
v___x_789_ = lean_array_push(v___y_758_, v___x_787_);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 1);
lean_ctor_set(v___x_778_, 1, v___x_789_);
lean_ctor_set(v___x_778_, 0, v___x_788_);
v___x_791_ = v___x_778_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
v_a_767_ = v_v_763_;
v_a_768_ = v___y_758_;
goto v___jp_766_;
}
}
v___jp_766_:
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_756_, v___x_769_);
v___x_771_ = lean_array_uset(v_bs_x27_765_, v_i_756_, v_a_767_);
v_i_756_ = v___x_770_;
v_bs_757_ = v___x_771_;
v___y_758_ = v_a_768_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v___x_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_bs_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_805_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_796_, v_a_797_, v___x_798_, v_sz_boxed_804_, v_i_boxed_805_, v_bs_801_, v___y_802_);
lean_dec(v_a_797_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_808_, lean_object* v___x_809_, size_t v_sz_810_, size_t v_i_811_, lean_object* v_bs_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_811_, v_sz_810_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v___x_809_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_bs_812_);
lean_ctor_set(v___x_816_, 1, v___y_813_);
return v___x_816_;
}
else
{
lean_object* v_v_817_; lean_object* v___x_818_; 
v_v_817_ = lean_array_uget_borrowed(v_bs_812_, v_i_811_);
v___x_818_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_808_, v_v_817_);
if (lean_obj_tag(v___x_818_) == 1)
{
lean_object* v_val_819_; lean_object* v___x_820_; lean_object* v_bs_x27_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v_val_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_unsigned_to_nat(0u);
v_bs_x27_821_ = lean_array_uset(v_bs_812_, v_i_811_, v___x_820_);
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_811_, v___x_822_);
v___x_824_ = lean_array_uset(v_bs_x27_821_, v_i_811_, v_val_819_);
v_i_811_ = v___x_823_;
v_bs_812_ = v___x_824_;
goto _start;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc(v_v_817_);
lean_dec(v___x_818_);
lean_dec_ref(v_bs_812_);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_827_ = lean_string_append(v___x_809_, v___x_826_);
v___x_828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_817_, v___x_815_);
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
lean_dec_ref(v___x_828_);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_831_ = lean_string_append(v___x_829_, v___x_830_);
v___x_832_ = 3;
v___x_833_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*1, v___x_832_);
v___x_834_ = lean_array_get_size(v___y_813_);
v___x_835_ = lean_array_push(v___y_813_, v___x_833_);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_837_, lean_object* v___x_838_, lean_object* v_sz_839_, lean_object* v_i_840_, lean_object* v_bs_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
size_t v_sz_boxed_844_; size_t v_i_boxed_845_; lean_object* v_res_846_; 
v_sz_boxed_844_ = lean_unbox_usize(v_sz_839_);
lean_dec(v_sz_839_);
v_i_boxed_845_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_837_, v___x_838_, v_sz_boxed_844_, v_i_boxed_845_, v_bs_841_, v___y_842_);
lean_dec(v_a_837_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_847_, lean_object* v_opts_848_, size_t v_sz_849_, size_t v_i_850_, lean_object* v_bs_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_850_, v_sz_849_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_dec_ref(v_env_847_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v_bs_851_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v_v_855_; lean_object* v___x_856_; 
v___x_854_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
v_v_855_ = lean_array_uget_borrowed(v_bs_851_, v_i_850_);
lean_inc(v_v_855_);
lean_inc_ref(v_env_847_);
v___x_856_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_847_, v_opts_848_, v___x_854_, v_v_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_bs_851_);
lean_dec_ref(v_env_847_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v_bs_x27_867_; size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v_a_865_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_856_, 1);
v___x_866_ = lean_unsigned_to_nat(0u);
v_bs_x27_867_ = lean_array_uset(v_bs_851_, v_i_850_, v___x_866_);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_850_, v___x_868_);
v___x_870_ = lean_array_uset(v_bs_x27_867_, v_i_850_, v_a_865_);
v_i_850_ = v___x_869_;
v_bs_851_ = v___x_870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_872_, lean_object* v_opts_873_, lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_bs_876_){
_start:
{
size_t v_sz_boxed_877_; size_t v_i_boxed_878_; lean_object* v_res_879_; 
v_sz_boxed_877_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_878_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_872_, v_opts_873_, v_sz_boxed_877_, v_i_boxed_878_, v_bs_876_);
lean_dec_ref(v_opts_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_880_, lean_object* v_opts_881_, lean_object* v_as_882_, size_t v_sz_883_, size_t v_i_884_, lean_object* v_b_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_884_, v_sz_883_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec_ref(v_env_880_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_885_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_890_; 
v___x_888_ = l_Lake_instTypeNamePackageFacetDecl;
v_a_889_ = lean_array_uget_borrowed(v_as_882_, v_i_884_);
lean_inc(v_a_889_);
lean_inc_ref(v_env_880_);
v___x_890_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_880_, v_opts_881_, v___x_888_, v_a_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_b_885_);
lean_dec_ref(v_env_880_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v_name_900_; lean_object* v_config_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_912_; 
v_a_899_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_890_, 1);
v_name_900_ = lean_ctor_get(v_a_899_, 0);
v_config_901_ = lean_ctor_get(v_a_899_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_a_899_);
if (v_isSharedCheck_912_ == 0)
{
v___x_903_ = v_a_899_;
v_isShared_904_ = v_isSharedCheck_912_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_config_901_);
lean_inc(v_name_900_);
lean_dec(v_a_899_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_912_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_name_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_config_901_);
v___x_906_ = v_reuseFailAlloc_911_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; size_t v___x_908_; size_t v___x_909_; 
v___x_907_ = lean_array_push(v_b_885_, v___x_906_);
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_add(v_i_884_, v___x_908_);
v_i_884_ = v___x_909_;
v_b_885_ = v___x_907_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_913_, lean_object* v_opts_914_, lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_b_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_920_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_913_, v_opts_914_, v_as_915_, v_sz_boxed_919_, v_i_boxed_920_, v_b_918_);
lean_dec_ref(v_as_915_);
lean_dec_ref(v_opts_914_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_922_, lean_object* v_opts_923_, lean_object* v_as_924_, size_t v_sz_925_, size_t v_i_926_, lean_object* v_b_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_lt(v_i_926_, v_sz_925_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec_ref(v_env_922_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_b_927_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_932_; 
v___x_930_ = l_Lake_instTypeNameLibraryFacetDecl;
v_a_931_ = lean_array_uget_borrowed(v_as_924_, v_i_926_);
lean_inc(v_a_931_);
lean_inc_ref(v_env_922_);
v___x_932_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_922_, v_opts_923_, v___x_930_, v_a_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_b_927_);
lean_dec_ref(v_env_922_);
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v_name_942_; lean_object* v_config_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_954_; 
v_a_941_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_932_, 1);
v_name_942_ = lean_ctor_get(v_a_941_, 0);
v_config_943_ = lean_ctor_get(v_a_941_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_a_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_945_ = v_a_941_;
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_config_943_);
lean_inc(v_name_942_);
lean_dec(v_a_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_name_942_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_config_943_);
v___x_948_ = v_reuseFailAlloc_953_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; size_t v___x_950_; size_t v___x_951_; 
v___x_949_ = lean_array_push(v_b_927_, v___x_948_);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_926_, v___x_950_);
v_i_926_ = v___x_951_;
v_b_927_ = v___x_949_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_955_, lean_object* v_opts_956_, lean_object* v_as_957_, lean_object* v_sz_958_, lean_object* v_i_959_, lean_object* v_b_960_){
_start:
{
size_t v_sz_boxed_961_; size_t v_i_boxed_962_; lean_object* v_res_963_; 
v_sz_boxed_961_ = lean_unbox_usize(v_sz_958_);
lean_dec(v_sz_958_);
v_i_boxed_962_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_res_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_955_, v_opts_956_, v_as_957_, v_sz_boxed_961_, v_i_boxed_962_, v_b_960_);
lean_dec_ref(v_as_957_);
lean_dec_ref(v_opts_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object* v_t_964_, lean_object* v_k_965_){
_start:
{
if (lean_obj_tag(v_t_964_) == 0)
{
lean_object* v_k_966_; lean_object* v_v_967_; lean_object* v_l_968_; lean_object* v_r_969_; uint8_t v___x_970_; 
v_k_966_ = lean_ctor_get(v_t_964_, 1);
v_v_967_ = lean_ctor_get(v_t_964_, 2);
v_l_968_ = lean_ctor_get(v_t_964_, 3);
v_r_969_ = lean_ctor_get(v_t_964_, 4);
v___x_970_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_965_, v_k_966_);
switch(v___x_970_)
{
case 0:
{
v_t_964_ = v_l_968_;
goto _start;
}
case 1:
{
lean_object* v___x_972_; 
lean_inc(v_v_967_);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_v_967_);
return v___x_972_;
}
default: 
{
v_t_964_ = v_r_969_;
goto _start;
}
}
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_box(0);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_t_975_, lean_object* v_k_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_t_975_, v_k_976_);
lean_dec(v_k_976_);
lean_dec(v_t_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(lean_object* v_k_978_, lean_object* v_v_979_, lean_object* v_t_980_){
_start:
{
if (lean_obj_tag(v_t_980_) == 0)
{
lean_object* v_size_981_; lean_object* v_k_982_; lean_object* v_v_983_; lean_object* v_l_984_; lean_object* v_r_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1265_; 
v_size_981_ = lean_ctor_get(v_t_980_, 0);
v_k_982_ = lean_ctor_get(v_t_980_, 1);
v_v_983_ = lean_ctor_get(v_t_980_, 2);
v_l_984_ = lean_ctor_get(v_t_980_, 3);
v_r_985_ = lean_ctor_get(v_t_980_, 4);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_t_980_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_987_ = v_t_980_;
v_isShared_988_ = v_isSharedCheck_1265_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_r_985_);
lean_inc(v_l_984_);
lean_inc(v_v_983_);
lean_inc(v_k_982_);
lean_inc(v_size_981_);
lean_dec(v_t_980_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1265_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint8_t v___x_989_; 
v___x_989_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_978_, v_k_982_);
switch(v___x_989_)
{
case 0:
{
lean_object* v_impl_990_; lean_object* v___x_991_; 
lean_dec(v_size_981_);
v_impl_990_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_978_, v_v_979_, v_l_984_);
v___x_991_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_985_) == 0)
{
lean_object* v_size_992_; lean_object* v_size_993_; lean_object* v_k_994_; lean_object* v_v_995_; lean_object* v_l_996_; lean_object* v_r_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_size_992_ = lean_ctor_get(v_r_985_, 0);
v_size_993_ = lean_ctor_get(v_impl_990_, 0);
v_k_994_ = lean_ctor_get(v_impl_990_, 1);
v_v_995_ = lean_ctor_get(v_impl_990_, 2);
v_l_996_ = lean_ctor_get(v_impl_990_, 3);
v_r_997_ = lean_ctor_get(v_impl_990_, 4);
lean_inc(v_r_997_);
v___x_998_ = lean_unsigned_to_nat(3u);
v___x_999_ = lean_nat_mul(v___x_998_, v_size_992_);
v___x_1000_ = lean_nat_dec_lt(v___x_999_, v_size_993_);
lean_dec(v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_dec(v_r_997_);
v___x_1001_ = lean_nat_add(v___x_991_, v_size_993_);
v___x_1002_ = lean_nat_add(v___x_1001_, v_size_992_);
lean_dec(v___x_1001_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 3, v_impl_990_);
lean_ctor_set(v___x_987_, 0, v___x_1002_);
v___x_1004_ = v___x_987_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_impl_990_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_r_985_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1071_; 
lean_inc(v_l_996_);
lean_inc(v_v_995_);
lean_inc(v_k_994_);
lean_inc(v_size_993_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_impl_990_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1072_ = lean_ctor_get(v_impl_990_, 4);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_impl_990_, 3);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_impl_990_, 2);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_impl_990_, 1);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_impl_990_, 0);
lean_dec(v_unused_1076_);
v___x_1007_ = v_impl_990_;
v_isShared_1008_ = v_isSharedCheck_1071_;
goto v_resetjp_1006_;
}
else
{
lean_dec(v_impl_990_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1071_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_size_1009_; lean_object* v_size_1010_; lean_object* v_k_1011_; lean_object* v_v_1012_; lean_object* v_l_1013_; lean_object* v_r_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_size_1009_ = lean_ctor_get(v_l_996_, 0);
v_size_1010_ = lean_ctor_get(v_r_997_, 0);
v_k_1011_ = lean_ctor_get(v_r_997_, 1);
v_v_1012_ = lean_ctor_get(v_r_997_, 2);
v_l_1013_ = lean_ctor_get(v_r_997_, 3);
v_r_1014_ = lean_ctor_get(v_r_997_, 4);
v___x_1015_ = lean_unsigned_to_nat(2u);
v___x_1016_ = lean_nat_mul(v___x_1015_, v_size_1009_);
v___x_1017_ = lean_nat_dec_lt(v_size_1010_, v___x_1016_);
lean_dec(v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1046_; 
lean_inc(v_r_1014_);
lean_inc(v_l_1013_);
lean_inc(v_v_1012_);
lean_inc(v_k_1011_);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_r_997_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; 
v_unused_1047_ = lean_ctor_get(v_r_997_, 4);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_r_997_, 3);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_r_997_, 2);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_r_997_, 1);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_r_997_, 0);
lean_dec(v_unused_1051_);
v___x_1019_ = v_r_997_;
v_isShared_1020_ = v_isSharedCheck_1046_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v_r_997_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1046_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___x_1034_; lean_object* v___y_1036_; 
v___x_1021_ = lean_nat_add(v___x_991_, v_size_993_);
lean_dec(v_size_993_);
v___x_1022_ = lean_nat_add(v___x_1021_, v_size_992_);
lean_dec(v___x_1021_);
v___x_1034_ = lean_nat_add(v___x_991_, v_size_1009_);
if (lean_obj_tag(v_l_1013_) == 0)
{
lean_object* v_size_1044_; 
v_size_1044_ = lean_ctor_get(v_l_1013_, 0);
lean_inc(v_size_1044_);
v___y_1036_ = v_size_1044_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___y_1036_ = v___x_1045_;
goto v___jp_1035_;
}
v___jp_1023_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_nat_add(v___y_1024_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec(v___y_1024_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_r_985_);
lean_ctor_set(v___x_1019_, 3, v_r_1014_);
lean_ctor_set(v___x_1019_, 2, v_v_983_);
lean_ctor_set(v___x_1019_, 1, v_k_982_);
lean_ctor_set(v___x_1019_, 0, v___x_1027_);
v___x_1029_ = v___x_1019_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_r_1014_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_r_985_);
v___x_1029_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 4, v___x_1029_);
lean_ctor_set(v___x_1007_, 3, v___y_1025_);
lean_ctor_set(v___x_1007_, 2, v_v_1012_);
lean_ctor_set(v___x_1007_, 1, v_k_1011_);
lean_ctor_set(v___x_1007_, 0, v___x_1022_);
v___x_1031_ = v___x_1007_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_1011_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_1012_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v___y_1025_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_nat_add(v___x_1034_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec(v___x_1034_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v_l_1013_);
lean_ctor_set(v___x_987_, 3, v_l_996_);
lean_ctor_set(v___x_987_, 2, v_v_995_);
lean_ctor_set(v___x_987_, 1, v_k_994_);
lean_ctor_set(v___x_987_, 0, v___x_1037_);
v___x_1039_ = v___x_987_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_994_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_995_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_l_996_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_l_1013_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_nat_add(v___x_991_, v_size_992_);
if (lean_obj_tag(v_r_1014_) == 0)
{
lean_object* v_size_1041_; 
v_size_1041_ = lean_ctor_get(v_r_1014_, 0);
lean_inc(v_size_1041_);
v___y_1024_ = v___x_1040_;
v___y_1025_ = v___x_1039_;
v___y_1026_ = v_size_1041_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v___y_1024_ = v___x_1040_;
v___y_1025_ = v___x_1039_;
v___y_1026_ = v___x_1042_;
goto v___jp_1023_;
}
}
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_del_object(v___x_987_);
v___x_1052_ = lean_nat_add(v___x_991_, v_size_993_);
lean_dec(v_size_993_);
v___x_1053_ = lean_nat_add(v___x_1052_, v_size_992_);
lean_dec(v___x_1052_);
v___x_1054_ = lean_nat_add(v___x_991_, v_size_992_);
v___x_1055_ = lean_nat_add(v___x_1054_, v_size_1010_);
lean_dec(v___x_1054_);
lean_inc_ref(v_r_985_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 4, v_r_985_);
lean_ctor_set(v___x_1007_, 3, v_r_997_);
lean_ctor_set(v___x_1007_, 2, v_v_983_);
lean_ctor_set(v___x_1007_, 1, v_k_982_);
lean_ctor_set(v___x_1007_, 0, v___x_1055_);
v___x_1057_ = v___x_1007_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_r_997_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_r_985_);
v___x_1057_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_isSharedCheck_1064_ = !lean_is_exclusive(v_r_985_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1065_ = lean_ctor_get(v_r_985_, 4);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_r_985_, 3);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_r_985_, 2);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_r_985_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_r_985_, 0);
lean_dec(v_unused_1069_);
v___x_1059_ = v_r_985_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v_r_985_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v___x_1057_);
lean_ctor_set(v___x_1059_, 3, v_l_996_);
lean_ctor_set(v___x_1059_, 2, v_v_995_);
lean_ctor_set(v___x_1059_, 1, v_k_994_);
lean_ctor_set(v___x_1059_, 0, v___x_1053_);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_k_994_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_v_995_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_l_996_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___x_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1077_; 
v_l_1077_ = lean_ctor_get(v_impl_990_, 3);
if (lean_obj_tag(v_l_1077_) == 0)
{
lean_object* v_r_1078_; lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1091_; 
lean_inc_ref(v_l_1077_);
v_r_1078_ = lean_ctor_get(v_impl_990_, 4);
v_k_1079_ = lean_ctor_get(v_impl_990_, 1);
v_v_1080_ = lean_ctor_get(v_impl_990_, 2);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_impl_990_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1092_ = lean_ctor_get(v_impl_990_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_impl_990_, 0);
lean_dec(v_unused_1093_);
v___x_1082_ = v_impl_990_;
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_r_1078_);
lean_inc(v_v_1080_);
lean_inc(v_k_1079_);
lean_dec(v_impl_990_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1078_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 3, v_r_1078_);
lean_ctor_set(v___x_1082_, 2, v_v_983_);
lean_ctor_set(v___x_1082_, 1, v_k_982_);
lean_ctor_set(v___x_1082_, 0, v___x_991_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_r_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_r_1078_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v___x_1086_);
lean_ctor_set(v___x_987_, 3, v_l_1077_);
lean_ctor_set(v___x_987_, 2, v_v_1080_);
lean_ctor_set(v___x_987_, 1, v_k_1079_);
lean_ctor_set(v___x_987_, 0, v___x_1084_);
v___x_1088_ = v___x_987_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_l_1077_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_r_1094_; 
v_r_1094_ = lean_ctor_get(v_impl_990_, 4);
lean_inc(v_r_1094_);
if (lean_obj_tag(v_r_1094_) == 0)
{
lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1119_; 
lean_inc(v_l_1077_);
v_k_1095_ = lean_ctor_get(v_impl_990_, 1);
v_v_1096_ = lean_ctor_get(v_impl_990_, 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_impl_990_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; 
v_unused_1120_ = lean_ctor_get(v_impl_990_, 4);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_impl_990_, 3);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_impl_990_, 0);
lean_dec(v_unused_1122_);
v___x_1098_ = v_impl_990_;
v_isShared_1099_ = v_isSharedCheck_1119_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
lean_dec(v_impl_990_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1119_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1115_; 
v_k_1100_ = lean_ctor_get(v_r_1094_, 1);
v_v_1101_ = lean_ctor_get(v_r_1094_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_r_1094_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1116_ = lean_ctor_get(v_r_1094_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_r_1094_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_1094_, 0);
lean_dec(v_unused_1118_);
v___x_1103_ = v_r_1094_;
v_isShared_1104_ = v_isSharedCheck_1115_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
lean_dec(v_r_1094_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1115_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_unsigned_to_nat(3u);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_l_1077_);
lean_ctor_set(v___x_1103_, 3, v_l_1077_);
lean_ctor_set(v___x_1103_, 2, v_v_1096_);
lean_ctor_set(v___x_1103_, 1, v_k_1095_);
lean_ctor_set(v___x_1103_, 0, v___x_991_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_l_1077_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_l_1077_);
v___x_1107_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_l_1077_);
lean_ctor_set(v___x_1098_, 2, v_v_983_);
lean_ctor_set(v___x_1098_, 1, v_k_982_);
lean_ctor_set(v___x_1098_, 0, v___x_991_);
v___x_1109_ = v___x_1098_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_l_1077_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_l_1077_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v___x_1109_);
lean_ctor_set(v___x_987_, 3, v___x_1107_);
lean_ctor_set(v___x_987_, 2, v_v_1101_);
lean_ctor_set(v___x_987_, 1, v_k_1100_);
lean_ctor_set(v___x_987_, 0, v___x_1105_);
v___x_1111_ = v___x_987_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = lean_unsigned_to_nat(2u);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v_r_1094_);
lean_ctor_set(v___x_987_, 3, v_impl_990_);
lean_ctor_set(v___x_987_, 0, v___x_1123_);
v___x_1125_ = v___x_987_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_impl_990_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_r_1094_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1128_; 
lean_dec(v_v_983_);
lean_dec(v_k_982_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 2, v_v_979_);
lean_ctor_set(v___x_987_, 1, v_k_978_);
v___x_1128_ = v___x_987_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_size_981_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_k_978_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_v_979_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_l_984_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v_r_985_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
default: 
{
lean_object* v_impl_1130_; lean_object* v___x_1131_; 
lean_dec(v_size_981_);
v_impl_1130_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_978_, v_v_979_, v_r_985_);
v___x_1131_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_984_) == 0)
{
lean_object* v_size_1132_; lean_object* v_size_1133_; lean_object* v_k_1134_; lean_object* v_v_1135_; lean_object* v_l_1136_; lean_object* v_r_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_size_1132_ = lean_ctor_get(v_l_984_, 0);
v_size_1133_ = lean_ctor_get(v_impl_1130_, 0);
v_k_1134_ = lean_ctor_get(v_impl_1130_, 1);
v_v_1135_ = lean_ctor_get(v_impl_1130_, 2);
v_l_1136_ = lean_ctor_get(v_impl_1130_, 3);
lean_inc(v_l_1136_);
v_r_1137_ = lean_ctor_get(v_impl_1130_, 4);
v___x_1138_ = lean_unsigned_to_nat(3u);
v___x_1139_ = lean_nat_mul(v___x_1138_, v_size_1132_);
v___x_1140_ = lean_nat_dec_lt(v___x_1139_, v_size_1133_);
lean_dec(v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec(v_l_1136_);
v___x_1141_ = lean_nat_add(v___x_1131_, v_size_1132_);
v___x_1142_ = lean_nat_add(v___x_1141_, v_size_1133_);
lean_dec(v___x_1141_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v_impl_1130_);
lean_ctor_set(v___x_987_, 0, v___x_1142_);
v___x_1144_ = v___x_987_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_l_984_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_impl_1130_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1209_; 
lean_inc(v_r_1137_);
lean_inc(v_v_1135_);
lean_inc(v_k_1134_);
lean_inc(v_size_1133_);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_impl_1130_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; lean_object* v_unused_1213_; lean_object* v_unused_1214_; 
v_unused_1210_ = lean_ctor_get(v_impl_1130_, 4);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_impl_1130_, 3);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_impl_1130_, 2);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_impl_1130_, 1);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_impl_1130_, 0);
lean_dec(v_unused_1214_);
v___x_1147_ = v_impl_1130_;
v_isShared_1148_ = v_isSharedCheck_1209_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v_impl_1130_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1209_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_size_1149_; lean_object* v_k_1150_; lean_object* v_v_1151_; lean_object* v_l_1152_; lean_object* v_r_1153_; lean_object* v_size_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_size_1149_ = lean_ctor_get(v_l_1136_, 0);
v_k_1150_ = lean_ctor_get(v_l_1136_, 1);
v_v_1151_ = lean_ctor_get(v_l_1136_, 2);
v_l_1152_ = lean_ctor_get(v_l_1136_, 3);
v_r_1153_ = lean_ctor_get(v_l_1136_, 4);
v_size_1154_ = lean_ctor_get(v_r_1137_, 0);
v___x_1155_ = lean_unsigned_to_nat(2u);
v___x_1156_ = lean_nat_mul(v___x_1155_, v_size_1154_);
v___x_1157_ = lean_nat_dec_lt(v_size_1149_, v___x_1156_);
lean_dec(v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1185_; 
lean_inc(v_r_1153_);
lean_inc(v_l_1152_);
lean_inc(v_v_1151_);
lean_inc(v_k_1150_);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_l_1136_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1186_ = lean_ctor_get(v_l_1136_, 4);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_l_1136_, 3);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_l_1136_, 2);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_l_1136_, 1);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_l_1136_, 0);
lean_dec(v_unused_1190_);
v___x_1159_ = v_l_1136_;
v_isShared_1160_ = v_isSharedCheck_1185_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_l_1136_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1185_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1175_; 
v___x_1161_ = lean_nat_add(v___x_1131_, v_size_1132_);
v___x_1162_ = lean_nat_add(v___x_1161_, v_size_1133_);
lean_dec(v_size_1133_);
if (lean_obj_tag(v_l_1152_) == 0)
{
lean_object* v_size_1183_; 
v_size_1183_ = lean_ctor_get(v_l_1152_, 0);
lean_inc(v_size_1183_);
v___y_1175_ = v_size_1183_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_unsigned_to_nat(0u);
v___y_1175_ = v___x_1184_;
goto v___jp_1174_;
}
v___jp_1163_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_nat_add(v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_r_1137_);
lean_ctor_set(v___x_1159_, 3, v_r_1153_);
lean_ctor_set(v___x_1159_, 2, v_v_1135_);
lean_ctor_set(v___x_1159_, 1, v_k_1134_);
lean_ctor_set(v___x_1159_, 0, v___x_1167_);
v___x_1169_ = v___x_1159_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_k_1134_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_v_1135_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_r_1153_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_r_1137_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 4, v___x_1169_);
lean_ctor_set(v___x_1147_, 3, v___y_1164_);
lean_ctor_set(v___x_1147_, 2, v_v_1151_);
lean_ctor_set(v___x_1147_, 1, v_k_1150_);
lean_ctor_set(v___x_1147_, 0, v___x_1162_);
v___x_1171_ = v___x_1147_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1150_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1151_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v___y_1164_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
v___jp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_nat_add(v___x_1161_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec(v___x_1161_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v_l_1152_);
lean_ctor_set(v___x_987_, 0, v___x_1176_);
v___x_1178_ = v___x_987_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_l_984_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v_l_1152_);
v___x_1178_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_nat_add(v___x_1131_, v_size_1154_);
if (lean_obj_tag(v_r_1153_) == 0)
{
lean_object* v_size_1180_; 
v_size_1180_ = lean_ctor_get(v_r_1153_, 0);
lean_inc(v_size_1180_);
v___y_1164_ = v___x_1178_;
v___y_1165_ = v___x_1179_;
v___y_1166_ = v_size_1180_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___y_1164_ = v___x_1178_;
v___y_1165_ = v___x_1179_;
v___y_1166_ = v___x_1181_;
goto v___jp_1163_;
}
}
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_del_object(v___x_987_);
v___x_1191_ = lean_nat_add(v___x_1131_, v_size_1132_);
v___x_1192_ = lean_nat_add(v___x_1191_, v_size_1133_);
lean_dec(v_size_1133_);
v___x_1193_ = lean_nat_add(v___x_1191_, v_size_1149_);
lean_dec(v___x_1191_);
lean_inc_ref(v_l_984_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 4, v_l_1136_);
lean_ctor_set(v___x_1147_, 3, v_l_984_);
lean_ctor_set(v___x_1147_, 2, v_v_983_);
lean_ctor_set(v___x_1147_, 1, v_k_982_);
lean_ctor_set(v___x_1147_, 0, v___x_1193_);
v___x_1195_ = v___x_1147_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_l_984_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_l_1136_);
v___x_1195_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_isSharedCheck_1202_ = !lean_is_exclusive(v_l_984_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1203_ = lean_ctor_get(v_l_984_, 4);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_l_984_, 3);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_l_984_, 2);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_l_984_, 1);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_l_984_, 0);
lean_dec(v_unused_1207_);
v___x_1197_ = v_l_984_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_dec(v_l_984_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 4, v_r_1137_);
lean_ctor_set(v___x_1197_, 3, v___x_1195_);
lean_ctor_set(v___x_1197_, 2, v_v_1135_);
lean_ctor_set(v___x_1197_, 1, v_k_1134_);
lean_ctor_set(v___x_1197_, 0, v___x_1192_);
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_k_1134_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_v_1135_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_r_1137_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1215_; 
v_l_1215_ = lean_ctor_get(v_impl_1130_, 3);
lean_inc(v_l_1215_);
if (lean_obj_tag(v_l_1215_) == 0)
{
lean_object* v_r_1216_; lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1241_; 
v_r_1216_ = lean_ctor_get(v_impl_1130_, 4);
v_k_1217_ = lean_ctor_get(v_impl_1130_, 1);
v_v_1218_ = lean_ctor_get(v_impl_1130_, 2);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_impl_1130_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; lean_object* v_unused_1243_; 
v_unused_1242_ = lean_ctor_get(v_impl_1130_, 3);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_impl_1130_, 0);
lean_dec(v_unused_1243_);
v___x_1220_ = v_impl_1130_;
v_isShared_1221_ = v_isSharedCheck_1241_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_r_1216_);
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
lean_dec(v_impl_1130_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1241_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_k_1222_; lean_object* v_v_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1237_; 
v_k_1222_ = lean_ctor_get(v_l_1215_, 1);
v_v_1223_ = lean_ctor_get(v_l_1215_, 2);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_l_1215_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; 
v_unused_1238_ = lean_ctor_get(v_l_1215_, 4);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_l_1215_, 3);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_l_1215_, 0);
lean_dec(v_unused_1240_);
v___x_1225_ = v_l_1215_;
v_isShared_1226_ = v_isSharedCheck_1237_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_v_1223_);
lean_inc(v_k_1222_);
lean_dec(v_l_1215_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1237_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1216_, 2);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 4, v_r_1216_);
lean_ctor_set(v___x_1225_, 3, v_r_1216_);
lean_ctor_set(v___x_1225_, 2, v_v_983_);
lean_ctor_set(v___x_1225_, 1, v_k_982_);
lean_ctor_set(v___x_1225_, 0, v___x_1131_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_r_1216_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_r_1216_);
v___x_1229_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
lean_inc(v_r_1216_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 3, v_r_1216_);
lean_ctor_set(v___x_1220_, 0, v___x_1131_);
v___x_1231_ = v___x_1220_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_r_1216_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_r_1216_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v___x_1231_);
lean_ctor_set(v___x_987_, 3, v___x_1229_);
lean_ctor_set(v___x_987_, 2, v_v_1223_);
lean_ctor_set(v___x_987_, 1, v_k_1222_);
lean_ctor_set(v___x_987_, 0, v___x_1227_);
v___x_1233_ = v___x_987_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
}
else
{
lean_object* v_r_1244_; 
v_r_1244_ = lean_ctor_get(v_impl_1130_, 4);
lean_inc(v_r_1244_);
if (lean_obj_tag(v_r_1244_) == 0)
{
lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
v_k_1245_ = lean_ctor_get(v_impl_1130_, 1);
v_v_1246_ = lean_ctor_get(v_impl_1130_, 2);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_impl_1130_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1258_ = lean_ctor_get(v_impl_1130_, 4);
lean_dec(v_unused_1258_);
v_unused_1259_ = lean_ctor_get(v_impl_1130_, 3);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v_impl_1130_, 0);
lean_dec(v_unused_1260_);
v___x_1248_ = v_impl_1130_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
lean_dec(v_impl_1130_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(3u);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 4, v_l_1215_);
lean_ctor_set(v___x_1248_, 2, v_v_983_);
lean_ctor_set(v___x_1248_, 1, v_k_982_);
lean_ctor_set(v___x_1248_, 0, v___x_1131_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_l_1215_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_l_1215_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v_r_1244_);
lean_ctor_set(v___x_987_, 3, v___x_1252_);
lean_ctor_set(v___x_987_, 2, v_v_1246_);
lean_ctor_set(v___x_987_, 1, v_k_1245_);
lean_ctor_set(v___x_987_, 0, v___x_1250_);
v___x_1254_ = v___x_987_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_r_1244_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_unsigned_to_nat(2u);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v_impl_1130_);
lean_ctor_set(v___x_987_, 3, v_r_1244_);
lean_ctor_set(v___x_987_, 0, v___x_1261_);
v___x_1263_ = v___x_987_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_r_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_impl_1130_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
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
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_k_978_);
lean_ctor_set(v___x_1267_, 2, v_v_979_);
lean_ctor_set(v___x_1267_, 3, v_t_980_);
lean_ctor_set(v___x_1267_, 4, v_t_980_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object* v___x_1271_, lean_object* v_as_1272_, size_t v_i_1273_, size_t v_stop_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_usize_dec_eq(v_i_1273_, v_stop_1274_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v_name_1280_; lean_object* v_kind_1281_; lean_object* v___x_1282_; 
v___x_1279_ = lean_array_uget_borrowed(v_as_1272_, v_i_1273_);
v_name_1280_ = lean_ctor_get(v___x_1279_, 1);
v_kind_1281_ = lean_ctor_get(v___x_1279_, 2);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_b_1275_, v_name_1280_);
if (lean_obj_tag(v___x_1282_) == 1)
{
lean_object* v_val_1283_; lean_object* v_kind_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_b_1275_);
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_kind_1284_ = lean_ctor_get(v_val_1283_, 2);
lean_inc(v_kind_1284_);
lean_dec(v_val_1283_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0));
v___x_1286_ = lean_string_append(v___x_1271_, v___x_1285_);
v___x_1287_ = 1;
lean_inc(v_name_1280_);
v___x_1288_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1280_, v___x_1287_);
v___x_1289_ = lean_string_append(v___x_1286_, v___x_1288_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1));
v___x_1291_ = lean_string_append(v___x_1289_, v___x_1290_);
v___x_1292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1284_, v___x_1287_);
v___x_1293_ = lean_string_append(v___x_1291_, v___x_1292_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2));
v___x_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
lean_inc(v_kind_1281_);
v___x_1296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1281_, v___x_1287_);
v___x_1297_ = lean_string_append(v___x_1295_, v___x_1296_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1299_ = lean_string_append(v___x_1297_, v___x_1298_);
v___x_1300_ = 3;
v___x_1301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*1, v___x_1300_);
v___x_1302_ = lean_array_get_size(v___y_1276_);
v___x_1303_ = lean_array_push(v___y_1276_, v___x_1301_);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; 
lean_dec(v___x_1282_);
lean_inc(v___x_1279_);
lean_inc(v_name_1280_);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_name_1280_, v___x_1279_, v_b_1275_);
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_add(v_i_1273_, v___x_1306_);
v_i_1273_ = v___x_1307_;
v_b_1275_ = v___x_1305_;
goto _start;
}
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v___x_1271_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_b_1275_);
lean_ctor_set(v___x_1309_, 1, v___y_1276_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object* v___x_1310_, lean_object* v_as_1311_, lean_object* v_i_1312_, lean_object* v_stop_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
size_t v_i_boxed_1317_; size_t v_stop_boxed_1318_; lean_object* v_res_1319_; 
v_i_boxed_1317_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_stop_boxed_1318_ = lean_unbox_usize(v_stop_1313_);
lean_dec(v_stop_1313_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1310_, v_as_1311_, v_i_boxed_1317_, v_stop_boxed_1318_, v_b_1314_, v___y_1315_);
lean_dec_ref(v_as_1311_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1326_, lean_object* v_opts_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_a_1331_; lean_object* v_a_1332_; lean_object* v_a_1335_; lean_object* v_a_1336_; lean_object* v___x_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1338_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1327_);
lean_inc_ref_n(v_env_1326_, 2);
v___f_1339_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1339_, 0, v_env_1326_);
lean_closure_set(v___f_1339_, 1, v_opts_1327_);
lean_closure_set(v___f_1339_, 2, v___x_1338_);
v___x_1340_ = l_Lake_instTypeNameScriptFn;
v___x_1341_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1326_, v_opts_1327_);
v___x_1342_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v_baseName_1344_; lean_object* v_keyName_1345_; lean_object* v_config_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___f_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v_baseName_1344_ = lean_ctor_get(v_a_1343_, 0);
v_keyName_1345_ = lean_ctor_get(v_a_1343_, 1);
v_config_1346_ = lean_ctor_get(v_a_1343_, 3);
v___x_1347_ = 0;
lean_inc(v_baseName_1344_);
v___x_1348_ = l_Lean_Name_toString(v_baseName_1344_, v___x_1347_);
v___x_1349_ = lean_box(v___x_1347_);
lean_inc_ref(v_opts_1327_);
lean_inc_ref_n(v_env_1326_, 2);
lean_inc_ref(v___x_1348_);
v___f_1350_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1350_, 0, v___x_1348_);
lean_closure_set(v___f_1350_, 1, v___x_1349_);
lean_closure_set(v___f_1350_, 2, v_env_1326_);
lean_closure_set(v___f_1350_, 3, v_opts_1327_);
lean_closure_set(v___f_1350_, 4, v___x_1340_);
v___x_1351_ = l_Lake_targetAttr;
v___x_1352_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_1326_, v___x_1351_, v___f_1339_);
v___x_1353_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_toArray_1355_; size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v_toArray_1355_ = lean_ctor_get(v_a_1354_, 1);
v_sz_1356_ = lean_array_size(v_toArray_1355_);
v___x_1357_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1355_);
lean_inc(v_keyName_1345_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v_keyName_1345_, v_sz_1356_, v___x_1357_, v_toArray_1355_, v_a_1328_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1611_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_a_1360_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1362_ = v___x_1358_;
v_isShared_1363_ = v_isSharedCheck_1611_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1611_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v_a_1400_; lean_object* v_a_1401_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v_a_1425_; lean_object* v_a_1426_; lean_object* v___y_1464_; lean_object* v_a_1465_; lean_object* v___x_1580_; lean_object* v_a_1582_; lean_object* v_a_1583_; uint8_t v___x_1597_; 
v___x_1390_ = lean_box(1);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_array_get_size(v_a_1359_);
v___x_1597_ = lean_nat_dec_lt(v___x_1391_, v___x_1580_);
if (v___x_1597_ == 0)
{
v_a_1582_ = v___x_1390_;
v_a_1583_ = v_a_1360_;
goto v___jp_1581_;
}
else
{
size_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_usize_of_nat(v___x_1580_);
lean_inc_ref(v___x_1348_);
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1348_, v_a_1359_, v___x_1357_, v___x_1598_, v___x_1390_, v_a_1360_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_a_1601_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
v_a_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1599_, 2);
v_a_1582_ = v_a_1600_;
v_a_1583_ = v_a_1601_;
goto v___jp_1581_;
}
else
{
lean_object* v_a_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___f_1350_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1602_ = lean_ctor_get(v___x_1599_, 0);
v_a_1603_ = lean_ctor_get(v___x_1599_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1599_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_inc(v_a_1602_);
lean_dec(v___x_1599_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
v___jp_1364_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1377_, 0, v_a_1343_);
lean_ctor_set(v___x_1377_, 1, v___y_1367_);
lean_ctor_set(v___x_1377_, 2, v_a_1376_);
lean_ctor_set(v___x_1377_, 3, v_a_1359_);
lean_ctor_set(v___x_1377_, 4, v___y_1373_);
lean_ctor_set(v___x_1377_, 5, v___y_1366_);
lean_ctor_set(v___x_1377_, 6, v___y_1371_);
lean_ctor_set(v___x_1377_, 7, v___y_1370_);
lean_ctor_set(v___x_1377_, 8, v___y_1369_);
lean_ctor_set(v___x_1377_, 9, v___y_1368_);
lean_ctor_set(v___x_1377_, 10, v___y_1365_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___y_1372_);
lean_ctor_set(v___x_1362_, 0, v___x_1377_);
v___x_1379_ = v___x_1362_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___y_1372_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_dec(v___y_1373_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_a_1359_);
lean_dec(v_a_1343_);
v_a_1381_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1382_ = lean_io_error_to_string(v_a_1381_);
v___x_1383_ = 3;
v___x_1384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*1, v___x_1383_);
v___x_1385_ = lean_array_get_size(v___y_1372_);
v___x_1386_ = lean_array_push(v___y_1372_, v___x_1384_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
lean_ctor_set(v___x_1362_, 1, v___x_1386_);
lean_ctor_set(v___x_1362_, 0, v___x_1385_);
v___x_1388_ = v___x_1362_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
v___jp_1392_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; size_t v_sz_1405_; lean_object* v___x_1406_; 
v___x_1402_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1403_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1326_, 2);
v___x_1404_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1403_, v_env_1326_);
v_sz_1405_ = lean_array_size(v___x_1404_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1326_, v_opts_1327_, v___x_1404_, v_sz_1405_, v___x_1357_, v___x_1402_);
lean_dec_ref(v___x_1404_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v___y_1365_ = v_a_1400_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1396_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v_a_1401_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___x_1406_;
goto v___jp_1364_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; size_t v_sz_1410_; lean_object* v___x_1411_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1326_, 2);
v___x_1409_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1408_, v_env_1326_);
v_sz_1410_ = lean_array_size(v___x_1409_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1326_, v_opts_1327_, v___x_1409_, v_sz_1410_, v___x_1357_, v_a_1407_);
lean_dec_ref(v___x_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v___y_1365_ = v_a_1400_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1396_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v_a_1401_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___x_1411_;
goto v___jp_1364_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v_sz_1415_; lean_object* v___x_1416_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1326_);
v___x_1414_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1413_, v_env_1326_);
v_sz_1415_ = lean_array_size(v___x_1414_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1326_, v_opts_1327_, v___x_1414_, v_sz_1415_, v___x_1357_, v_a_1412_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_opts_1327_);
v___y_1365_ = v_a_1400_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1396_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v_a_1401_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___x_1416_;
goto v___jp_1364_;
}
}
}
v___jp_1417_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; size_t v_sz_1429_; lean_object* v___x_1430_; 
v___x_1427_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1326_);
v___x_1428_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1427_, v_env_1326_);
v_sz_1429_ = lean_array_size(v___x_1428_);
lean_inc_ref(v___x_1348_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1354_, v___y_1423_, v___x_1348_, v_sz_1429_, v___x_1357_, v___x_1428_, v_a_1426_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_a_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1430_, 2);
v___x_1433_ = lean_array_get_size(v_a_1431_);
v___x_1434_ = lean_nat_dec_lt(v___y_1420_, v___x_1433_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_nat_dec_lt(v___x_1391_, v___x_1433_);
if (v___x_1435_ == 0)
{
lean_object* v_lintDriver_1436_; 
lean_dec(v_a_1431_);
lean_dec_ref(v___x_1348_);
v_lintDriver_1436_ = lean_ctor_get(v_config_1346_, 14);
lean_inc_ref(v_lintDriver_1436_);
v___y_1393_ = v___y_1419_;
v___y_1394_ = v___y_1418_;
v___y_1395_ = v_a_1425_;
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1422_;
v___y_1398_ = v___y_1423_;
v___y_1399_ = v___y_1424_;
v_a_1400_ = v_lintDriver_1436_;
v_a_1401_ = v_a_1432_;
goto v___jp_1392_;
}
else
{
lean_object* v_lintDriver_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_lintDriver_1437_ = lean_ctor_get(v_config_1346_, 14);
v___x_1438_ = lean_string_utf8_byte_size(v_lintDriver_1437_);
v___x_1439_ = lean_nat_dec_eq(v___x_1438_, v___x_1391_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1425_);
lean_dec(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v___x_1440_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1441_ = lean_string_append(v___x_1348_, v___x_1440_);
v___x_1442_ = 3;
v___x_1443_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set_uint8(v___x_1443_, sizeof(void*)*1, v___x_1442_);
v___x_1444_ = lean_array_get_size(v_a_1432_);
v___x_1445_ = lean_array_push(v_a_1432_, v___x_1443_);
v_a_1335_ = v___x_1444_;
v_a_1336_ = v___x_1445_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v___x_1348_);
v___x_1446_ = lean_array_fget(v_a_1431_, v___x_1391_);
lean_dec(v_a_1431_);
v___x_1447_ = l_Lean_Name_toString(v___x_1446_, v___x_1435_);
v___y_1393_ = v___y_1419_;
v___y_1394_ = v___y_1418_;
v___y_1395_ = v_a_1425_;
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1422_;
v___y_1398_ = v___y_1423_;
v___y_1399_ = v___y_1424_;
v_a_1400_ = v___x_1447_;
v_a_1401_ = v_a_1432_;
goto v___jp_1392_;
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1425_);
lean_dec(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v___x_1448_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1449_ = lean_string_append(v___x_1348_, v___x_1448_);
v___x_1450_ = 3;
v___x_1451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1, v___x_1450_);
v___x_1452_ = lean_array_get_size(v_a_1432_);
v___x_1453_ = lean_array_push(v_a_1432_, v___x_1451_);
v_a_1335_ = v___x_1452_;
v_a_1336_ = v___x_1453_;
goto v___jp_1334_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v_a_1425_);
lean_dec(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1454_ = lean_ctor_get(v___x_1430_, 0);
v_a_1455_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1430_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_inc(v_a_1454_);
lean_dec(v___x_1430_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1454_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
v___jp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; size_t v_sz_1468_; lean_object* v___x_1469_; 
v___x_1466_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1326_);
v___x_1467_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1466_, v_env_1326_);
v_sz_1468_ = lean_array_size(v___x_1467_);
lean_inc_ref(v___x_1348_);
lean_inc(v_a_1354_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1354_, v___x_1348_, v_sz_1468_, v___x_1357_, v___x_1467_, v_a_1465_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
v_a_1471_ = lean_ctor_get(v___x_1469_, 1);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1469_, 2);
v___x_1472_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1326_);
v___x_1473_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1326_, v___x_1472_, v___f_1350_, v_a_1471_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; size_t v_sz_1478_; lean_object* v___x_1479_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
v_a_1475_ = lean_ctor_get(v___x_1473_, 1);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1473_, 2);
v___x_1476_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1326_);
v___x_1477_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1476_, v_env_1326_);
v_sz_1478_ = lean_array_size(v___x_1477_);
lean_inc_ref(v___x_1348_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1474_, v___x_1348_, v_sz_1478_, v___x_1357_, v___x_1477_, v_a_1475_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; size_t v_sz_1484_; lean_object* v___x_1485_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
v_a_1481_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1479_, 2);
v___x_1482_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1326_, 2);
v___x_1483_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1482_, v_env_1326_);
v_sz_1484_ = lean_array_size(v___x_1483_);
lean_inc(v_keyName_1345_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1326_, v_opts_1327_, v_keyName_1345_, v_sz_1484_, v___x_1357_, v___x_1483_, v_a_1481_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1543_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_a_1487_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1543_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1543_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; size_t v_sz_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1491_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1326_, 2);
v___x_1492_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1491_, v_env_1326_);
v_sz_1493_ = lean_array_size(v___x_1492_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1326_, v_opts_1327_, v_sz_1493_, v___x_1357_, v___x_1492_);
v___x_1495_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; size_t v_sz_1499_; lean_object* v___x_1500_; 
lean_del_object(v___x_1489_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1326_);
v___x_1498_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1497_, v_env_1326_);
v_sz_1499_ = lean_array_size(v___x_1498_);
lean_inc_ref(v___x_1348_);
lean_inc(v_a_1354_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1354_, v_a_1474_, v___x_1348_, v_sz_1499_, v___x_1357_, v___x_1498_, v_a_1487_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1500_, 2);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_array_get_size(v_a_1501_);
v___x_1505_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_nat_dec_lt(v___x_1391_, v___x_1504_);
if (v___x_1506_ == 0)
{
lean_object* v_testDriver_1507_; 
lean_dec(v_a_1501_);
v_testDriver_1507_ = lean_ctor_get(v_config_1346_, 12);
lean_inc_ref(v_testDriver_1507_);
v___y_1418_ = v_a_1470_;
v___y_1419_ = v_a_1496_;
v___y_1420_ = v___x_1503_;
v___y_1421_ = v_a_1486_;
v___y_1422_ = v_a_1480_;
v___y_1423_ = v_a_1474_;
v___y_1424_ = v___y_1464_;
v_a_1425_ = v_testDriver_1507_;
v_a_1426_ = v_a_1502_;
goto v___jp_1417_;
}
else
{
lean_object* v_testDriver_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_testDriver_1508_ = lean_ctor_get(v_config_1346_, 12);
v___x_1509_ = lean_string_utf8_byte_size(v_testDriver_1508_);
v___x_1510_ = lean_nat_dec_eq(v___x_1509_, v___x_1391_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec(v_a_1501_);
lean_dec(v_a_1496_);
lean_dec(v_a_1486_);
lean_dec(v_a_1480_);
lean_dec(v_a_1474_);
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v___x_1511_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1512_ = lean_string_append(v___x_1348_, v___x_1511_);
v___x_1513_ = 3;
v___x_1514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*1, v___x_1513_);
v___x_1515_ = lean_array_get_size(v_a_1502_);
v___x_1516_ = lean_array_push(v_a_1502_, v___x_1514_);
v_a_1331_ = v___x_1515_;
v_a_1332_ = v___x_1516_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_array_fget(v_a_1501_, v___x_1391_);
lean_dec(v_a_1501_);
v___x_1518_ = l_Lean_Name_toString(v___x_1517_, v___x_1506_);
v___y_1418_ = v_a_1470_;
v___y_1419_ = v_a_1496_;
v___y_1420_ = v___x_1503_;
v___y_1421_ = v_a_1486_;
v___y_1422_ = v_a_1480_;
v___y_1423_ = v_a_1474_;
v___y_1424_ = v___y_1464_;
v_a_1425_ = v___x_1518_;
v_a_1426_ = v_a_1502_;
goto v___jp_1417_;
}
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_a_1501_);
lean_dec(v_a_1496_);
lean_dec(v_a_1486_);
lean_dec(v_a_1480_);
lean_dec(v_a_1474_);
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v___x_1519_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1520_ = lean_string_append(v___x_1348_, v___x_1519_);
v___x_1521_ = 3;
v___x_1522_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set_uint8(v___x_1522_, sizeof(void*)*1, v___x_1521_);
v___x_1523_ = lean_array_get_size(v_a_1502_);
v___x_1524_ = lean_array_push(v_a_1502_, v___x_1522_);
v_a_1331_ = v___x_1523_;
v_a_1332_ = v___x_1524_;
goto v___jp_1330_;
}
}
else
{
lean_object* v_a_1525_; lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1496_);
lean_dec(v_a_1486_);
lean_dec(v_a_1480_);
lean_dec(v_a_1474_);
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1525_ = lean_ctor_get(v___x_1500_, 0);
v_a_1526_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1500_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_inc(v_a_1525_);
lean_dec(v___x_1500_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1525_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v_a_1486_);
lean_dec(v_a_1480_);
lean_dec(v_a_1474_);
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1534_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1535_ = lean_io_error_to_string(v_a_1534_);
v___x_1536_ = 3;
v___x_1537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*1, v___x_1536_);
v___x_1538_ = lean_array_get_size(v_a_1487_);
v___x_1539_ = lean_array_push(v_a_1487_, v___x_1537_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 1);
lean_ctor_set(v___x_1489_, 1, v___x_1539_);
lean_ctor_set(v___x_1489_, 0, v___x_1538_);
v___x_1541_ = v___x_1489_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1480_);
lean_dec(v_a_1474_);
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1544_ = lean_ctor_get(v___x_1485_, 0);
v_a_1545_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1485_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_inc(v_a_1544_);
lean_dec(v___x_1485_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1544_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_a_1474_);
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1553_ = lean_ctor_get(v___x_1479_, 0);
v_a_1554_ = lean_ctor_get(v___x_1479_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1479_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_inc(v_a_1553_);
lean_dec(v___x_1479_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1470_);
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1562_ = lean_ctor_get(v___x_1473_, 0);
v_a_1563_ = lean_ctor_get(v___x_1473_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1473_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_inc(v_a_1562_);
lean_dec(v___x_1473_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1562_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v___y_1464_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___f_1350_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1571_ = lean_ctor_get(v___x_1469_, 0);
v_a_1572_ = lean_ctor_get(v___x_1469_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1469_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_inc(v_a_1571_);
lean_dec(v___x_1469_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
v___jp_1581_:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_nat_dec_lt(v___x_1391_, v___x_1580_);
if (v___x_1584_ == 0)
{
v___y_1464_ = v_a_1582_;
v_a_1465_ = v_a_1583_;
goto v___jp_1463_;
}
else
{
size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_usize_of_nat(v___x_1580_);
lean_inc_ref(v___x_1348_);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1348_, v_a_1359_, v___x_1357_, v___x_1585_, v___x_1390_, v_a_1583_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 2);
v___y_1464_ = v_a_1582_;
v_a_1465_ = v_a_1587_;
goto v___jp_1463_;
}
else
{
lean_object* v_a_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_a_1582_);
lean_del_object(v___x_1362_);
lean_dec(v_a_1359_);
lean_dec(v_a_1354_);
lean_dec_ref(v___f_1350_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1588_ = lean_ctor_get(v___x_1586_, 0);
v_a_1589_ = lean_ctor_get(v___x_1586_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1586_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_inc(v_a_1588_);
lean_dec(v___x_1586_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_a_1354_);
lean_dec_ref(v___f_1350_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1612_ = lean_ctor_get(v___x_1358_, 0);
v_a_1613_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1358_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_inc(v_a_1612_);
lean_dec(v___x_1358_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1612_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v___f_1350_);
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1343_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1621_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1622_ = lean_io_error_to_string(v_a_1621_);
v___x_1623_ = 3;
v___x_1624_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*1, v___x_1623_);
v___x_1625_ = lean_array_get_size(v_a_1328_);
v___x_1626_ = lean_array_push(v_a_1328_, v___x_1624_);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
return v___x_1627_;
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v___f_1339_);
lean_dec_ref(v_opts_1327_);
lean_dec_ref(v_env_1326_);
v_a_1628_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1629_ = lean_io_error_to_string(v_a_1628_);
v___x_1630_ = 3;
v___x_1631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*1, v___x_1630_);
v___x_1632_ = lean_array_get_size(v_a_1328_);
v___x_1633_ = lean_array_push(v_a_1328_, v___x_1631_);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
v___jp_1330_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1331_);
lean_ctor_set(v___x_1333_, 1, v_a_1332_);
return v___x_1333_;
}
v___jp_1334_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1335_);
lean_ctor_set(v___x_1337_, 1, v_a_1336_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1635_, lean_object* v_opts_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1635_, v_opts_1636_, v_a_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1640_, lean_object* v_inst_1641_, lean_object* v_t_1642_, lean_object* v_k_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_t_1642_, v_k_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1645_, lean_object* v_inst_1646_, lean_object* v_t_1647_, lean_object* v_k_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1645_, v_inst_1646_, v_t_1647_, v_k_1648_);
lean_dec(v_k_1648_);
lean_dec(v_t_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object* v_00_u03b2_1650_, lean_object* v_k_1651_, lean_object* v_v_1652_, lean_object* v_t_1653_, lean_object* v_hl_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_1651_, v_v_1652_, v_t_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1656_, lean_object* v_env_1657_, lean_object* v_attr_1658_, lean_object* v_f_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_1657_, v_attr_1658_, v_f_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1661_, lean_object* v_env_1662_, lean_object* v_attr_1663_, lean_object* v_f_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1661_, v_env_1662_, v_attr_1663_, v_f_1664_);
lean_dec_ref(v_attr_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1666_, lean_object* v_t_1667_, lean_object* v_k_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1667_, v_k_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1670_, lean_object* v_t_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1670_, v_t_1671_, v_k_1672_);
lean_dec(v_k_1672_);
lean_dec(v_t_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1674_, lean_object* v_env_1675_, lean_object* v_attr_1676_, lean_object* v_f_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1675_, v_attr_1676_, v_f_1677_, v___y_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_env_1682_, lean_object* v_attr_1683_, lean_object* v_f_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1681_, v_env_1682_, v_attr_1683_, v_f_1684_, v___y_1685_);
lean_dec_ref(v_attr_1683_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v_as_1690_, size_t v_i_1691_, size_t v_stop_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1688_, v_as_1690_, v_i_1691_, v_stop_1692_, v_b_1693_, v___y_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v_as_1699_, lean_object* v_i_1700_, lean_object* v_stop_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
size_t v_i_boxed_1705_; size_t v_stop_boxed_1706_; lean_object* v_res_1707_; 
v_i_boxed_1705_ = lean_unbox_usize(v_i_1700_);
lean_dec(v_i_1700_);
v_stop_boxed_1706_ = lean_unbox_usize(v_stop_1701_);
lean_dec(v_stop_1701_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1697_, v___x_1698_, v_as_1699_, v_i_boxed_1705_, v_stop_boxed_1706_, v_b_1702_, v___y_1703_);
lean_dec_ref(v_as_1699_);
lean_dec(v___x_1698_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(lean_object* v_00_u03b2_1708_, lean_object* v_f_1709_, lean_object* v_as_1710_, size_t v_i_1711_, size_t v_stop_1712_, lean_object* v_b_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_1709_, v_as_1710_, v_i_1711_, v_stop_1712_, v_b_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1715_, lean_object* v_f_1716_, lean_object* v_as_1717_, lean_object* v_i_1718_, lean_object* v_stop_1719_, lean_object* v_b_1720_){
_start:
{
size_t v_i_boxed_1721_; size_t v_stop_boxed_1722_; lean_object* v_res_1723_; 
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_stop_boxed_1722_ = lean_unbox_usize(v_stop_1719_);
lean_dec(v_stop_1719_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(v_00_u03b2_1715_, v_f_1716_, v_as_1717_, v_i_boxed_1721_, v_stop_boxed_1722_, v_b_1720_);
lean_dec_ref(v_as_1717_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1724_, lean_object* v_f_1725_, lean_object* v_as_1726_, size_t v_i_1727_, size_t v_stop_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1725_, v_as_1726_, v_i_1727_, v_stop_1728_, v_b_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1733_, lean_object* v_f_1734_, lean_object* v_as_1735_, lean_object* v_i_1736_, lean_object* v_stop_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
size_t v_i_boxed_1741_; size_t v_stop_boxed_1742_; lean_object* v_res_1743_; 
v_i_boxed_1741_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_stop_boxed_1742_ = lean_unbox_usize(v_stop_1737_);
lean_dec(v_stop_1737_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1733_, v_f_1734_, v_as_1735_, v_i_boxed_1741_, v_stop_boxed_1742_, v_b_1738_, v___y_1739_);
lean_dec_ref(v_as_1735_);
return v_res_1743_;
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
