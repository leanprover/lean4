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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_packageAttr;
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
extern lean_object* l_Lake_targetAttr;
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_instTypeNameScriptFn_unsafe__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_moduleFacetAttr;
extern lean_object* l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
extern lean_object* l_Lake_packageFacetAttr;
extern lean_object* l_Lake_libraryFacetAttr;
extern lean_object* l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
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
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "post-update hook was defined in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "', but was registered in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' was defined in package '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "', but registered under '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": package is missing target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' marked as a default"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_declName_38_; uint8_t v___x_39_; uint8_t v___x_40_; 
v_declName_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_declName_38_);
lean_dec_ref_known(v___x_37_, 2);
v___x_39_ = lean_name_eq(v_declName_38_, v_inst_25_);
lean_dec(v_declName_38_);
v___x_40_ = lean_bool_not(v___x_39_);
if (v___x_40_ == 0)
{
uint8_t v___x_41_; lean_object* v___x_42_; 
lean_dec(v_inst_25_);
v___x_41_ = 1;
v___x_42_ = l_Lean_Environment_evalConst___redArg(v_env_23_, v_opts_24_, v_const_26_, v___x_41_);
lean_dec(v_const_26_);
lean_dec_ref(v_env_23_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
lean_dec_ref(v_env_23_);
v___x_43_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_25_, v_const_26_);
return v___x_43_;
}
}
else
{
lean_object* v___x_44_; 
lean_dec_ref(v___x_37_);
lean_dec_ref(v_env_23_);
v___x_44_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_25_, v_const_26_);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___boxed(lean_object* v_env_45_, lean_object* v_opts_46_, lean_object* v_inst_47_, lean_object* v_const_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_45_, v_opts_46_, v_inst_47_, v_const_48_);
lean_dec_ref(v_opts_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(lean_object* v_env_50_, lean_object* v_opts_51_, lean_object* v_00_u03b1_52_, lean_object* v_inst_53_, lean_object* v_const_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_50_, v_opts_51_, v_inst_53_, v_const_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___boxed(lean_object* v_env_56_, lean_object* v_opts_57_, lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_const_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(v_env_56_, v_opts_57_, v_00_u03b1_58_, v_inst_59_, v_const_60_);
lean_dec_ref(v_opts_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0(lean_object* v_declName_63_, lean_object* v_map_64_, lean_object* v_toPure_65_, lean_object* v_____do__lift_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
v___x_68_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_67_, v_declName_63_, v_____do__lift_66_, v_map_64_);
v___x_69_ = lean_apply_2(v_toPure_65_, lean_box(0), v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1(lean_object* v_toPure_70_, lean_object* v_f_71_, lean_object* v_toBind_72_, lean_object* v_map_73_, lean_object* v_declName_74_){
_start:
{
lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_inc(v_declName_74_);
v___f_75_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_75_, 0, v_declName_74_);
lean_closure_set(v___f_75_, 1, v_map_73_);
lean_closure_set(v___f_75_, 2, v_toPure_70_);
v___x_76_ = lean_apply_1(v_f_71_, v_declName_74_);
v___x_77_ = lean_apply_4(v_toBind_72_, lean_box(0), lean_box(0), v___x_76_, v___f_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(lean_object* v_env_78_, lean_object* v_attr_79_, lean_object* v_inst_80_, lean_object* v_f_81_){
_start:
{
lean_object* v_toApplicative_82_; lean_object* v_toBind_83_; lean_object* v_toPure_84_; lean_object* v_entries_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_toApplicative_82_ = lean_ctor_get(v_inst_80_, 0);
v_toBind_83_ = lean_ctor_get(v_inst_80_, 1);
v_toPure_84_ = lean_ctor_get(v_toApplicative_82_, 1);
v_entries_85_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_79_, v_env_78_);
v___x_86_ = lean_box(1);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_array_get_size(v_entries_85_);
v___x_89_ = lean_nat_dec_lt(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_inc(v_toPure_84_);
lean_dec_ref(v_entries_85_);
lean_dec(v_f_81_);
lean_dec_ref(v_inst_80_);
v___x_90_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_86_);
return v___x_90_;
}
else
{
lean_object* v___f_91_; uint8_t v___x_92_; 
lean_inc(v_toBind_83_);
lean_inc(v_toPure_84_);
v___f_91_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_91_, 0, v_toPure_84_);
lean_closure_set(v___f_91_, 1, v_f_81_);
lean_closure_set(v___f_91_, 2, v_toBind_83_);
v___x_92_ = lean_nat_dec_le(v___x_88_, v___x_88_);
if (v___x_92_ == 0)
{
if (v___x_89_ == 0)
{
lean_object* v___x_93_; 
lean_inc(v_toPure_84_);
lean_dec_ref(v___f_91_);
lean_dec_ref(v_entries_85_);
lean_dec_ref(v_inst_80_);
v___x_93_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_86_);
return v___x_93_;
}
else
{
size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((size_t)0ULL);
v___x_95_ = lean_usize_of_nat(v___x_88_);
v___x_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_80_, v___f_91_, v_entries_85_, v___x_94_, v___x_95_, v___x_86_);
return v___x_96_;
}
}
else
{
size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_88_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_80_, v___f_91_, v_entries_85_, v___x_97_, v___x_98_, v___x_86_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___boxed(lean_object* v_env_100_, lean_object* v_attr_101_, lean_object* v_inst_102_, lean_object* v_f_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(v_env_100_, v_attr_101_, v_inst_102_, v_f_103_);
lean_dec_ref(v_attr_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(lean_object* v_m_105_, lean_object* v_00_u03b2_106_, lean_object* v_env_107_, lean_object* v_attr_108_, lean_object* v_inst_109_, lean_object* v_f_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(v_env_107_, v_attr_108_, v_inst_109_, v_f_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___boxed(lean_object* v_m_112_, lean_object* v_00_u03b2_113_, lean_object* v_env_114_, lean_object* v_attr_115_, lean_object* v_inst_116_, lean_object* v_f_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(v_m_112_, v_00_u03b2_113_, v_env_114_, v_attr_115_, v_inst_116_, v_f_117_);
lean_dec_ref(v_attr_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0(lean_object* v_declName_119_, lean_object* v_map_120_, lean_object* v_toPure_121_, lean_object* v_____do__lift_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_119_, v_____do__lift_122_, v_map_120_);
v___x_124_ = lean_apply_2(v_toPure_121_, lean_box(0), v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1(lean_object* v_toPure_125_, lean_object* v_f_126_, lean_object* v_toBind_127_, lean_object* v_map_128_, lean_object* v_declName_129_){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_inc(v_declName_129_);
v___f_130_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_130_, 0, v_declName_129_);
lean_closure_set(v___f_130_, 1, v_map_128_);
lean_closure_set(v___f_130_, 2, v_toPure_125_);
v___x_131_ = lean_apply_1(v_f_126_, v_declName_129_);
v___x_132_ = lean_apply_4(v_toBind_127_, lean_box(0), lean_box(0), v___x_131_, v___f_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(lean_object* v_env_133_, lean_object* v_attr_134_, lean_object* v_inst_135_, lean_object* v_f_136_){
_start:
{
lean_object* v_toApplicative_137_; lean_object* v_toBind_138_; lean_object* v_toPure_139_; lean_object* v_entries_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_toApplicative_137_ = lean_ctor_get(v_inst_135_, 0);
v_toBind_138_ = lean_ctor_get(v_inst_135_, 1);
v_toPure_139_ = lean_ctor_get(v_toApplicative_137_, 1);
v_entries_140_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_134_, v_env_133_);
v___x_141_ = lean_box(1);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v_entries_140_);
v___x_144_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_inc(v_toPure_139_);
lean_dec_ref(v_entries_140_);
lean_dec(v_f_136_);
lean_dec_ref(v_inst_135_);
v___x_145_ = lean_apply_2(v_toPure_139_, lean_box(0), v___x_141_);
return v___x_145_;
}
else
{
lean_object* v___f_146_; uint8_t v___x_147_; 
lean_inc(v_toBind_138_);
lean_inc(v_toPure_139_);
v___f_146_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_146_, 0, v_toPure_139_);
lean_closure_set(v___f_146_, 1, v_f_136_);
lean_closure_set(v___f_146_, 2, v_toBind_138_);
v___x_147_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_147_ == 0)
{
if (v___x_144_ == 0)
{
lean_object* v___x_148_; 
lean_inc(v_toPure_139_);
lean_dec_ref(v___f_146_);
lean_dec_ref(v_entries_140_);
lean_dec_ref(v_inst_135_);
v___x_148_ = lean_apply_2(v_toPure_139_, lean_box(0), v___x_141_);
return v___x_148_;
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_143_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_135_, v___f_146_, v_entries_140_, v___x_149_, v___x_150_, v___x_141_);
return v___x_151_;
}
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_143_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_135_, v___f_146_, v_entries_140_, v___x_152_, v___x_153_, v___x_141_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___boxed(lean_object* v_env_155_, lean_object* v_attr_156_, lean_object* v_inst_157_, lean_object* v_f_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(v_env_155_, v_attr_156_, v_inst_157_, v_f_158_);
lean_dec_ref(v_attr_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(lean_object* v_m_160_, lean_object* v_00_u03b2_161_, lean_object* v_env_162_, lean_object* v_attr_163_, lean_object* v_inst_164_, lean_object* v_f_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(v_env_162_, v_attr_163_, v_inst_164_, v_f_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___boxed(lean_object* v_m_167_, lean_object* v_00_u03b2_168_, lean_object* v_env_169_, lean_object* v_attr_170_, lean_object* v_inst_171_, lean_object* v_f_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(v_m_167_, v_00_u03b2_168_, v_env_169_, v_attr_170_, v_inst_171_, v_f_172_);
lean_dec_ref(v_attr_170_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0(lean_object* v_map_174_, lean_object* v_declName_175_, lean_object* v_toPure_176_, lean_object* v_____do__lift_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
v___x_179_ = l_Lake_RBArray_insert___redArg(v___x_178_, v_map_174_, v_declName_175_, v_____do__lift_177_);
v___x_180_ = lean_apply_2(v_toPure_176_, lean_box(0), v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1(lean_object* v_toPure_181_, lean_object* v_f_182_, lean_object* v_toBind_183_, lean_object* v_map_184_, lean_object* v_declName_185_){
_start:
{
lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc(v_declName_185_);
v___f_186_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_186_, 0, v_map_184_);
lean_closure_set(v___f_186_, 1, v_declName_185_);
lean_closure_set(v___f_186_, 2, v_toPure_181_);
v___x_187_ = lean_apply_1(v_f_182_, v_declName_185_);
v___x_188_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_187_, v___f_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(lean_object* v_env_189_, lean_object* v_attr_190_, lean_object* v_inst_191_, lean_object* v_f_192_){
_start:
{
lean_object* v_toApplicative_193_; lean_object* v_toBind_194_; lean_object* v_toPure_195_; lean_object* v_entries_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_toApplicative_193_ = lean_ctor_get(v_inst_191_, 0);
v_toBind_194_ = lean_ctor_get(v_inst_191_, 1);
v_toPure_195_ = lean_ctor_get(v_toApplicative_193_, 1);
v_entries_196_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_190_, v_env_189_);
v___x_197_ = lean_array_get_size(v_entries_196_);
v___x_198_ = l_Lake_RBArray_mkEmpty___redArg(v___x_197_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_nat_dec_lt(v___x_199_, v___x_197_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_inc(v_toPure_195_);
lean_dec_ref(v_entries_196_);
lean_dec(v_f_192_);
lean_dec_ref(v_inst_191_);
v___x_201_ = lean_apply_2(v_toPure_195_, lean_box(0), v___x_198_);
return v___x_201_;
}
else
{
lean_object* v___f_202_; uint8_t v___x_203_; 
lean_inc(v_toBind_194_);
lean_inc(v_toPure_195_);
v___f_202_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_202_, 0, v_toPure_195_);
lean_closure_set(v___f_202_, 1, v_f_192_);
lean_closure_set(v___f_202_, 2, v_toBind_194_);
v___x_203_ = lean_nat_dec_le(v___x_197_, v___x_197_);
if (v___x_203_ == 0)
{
if (v___x_200_ == 0)
{
lean_object* v___x_204_; 
lean_inc(v_toPure_195_);
lean_dec_ref(v___f_202_);
lean_dec_ref(v_entries_196_);
lean_dec_ref(v_inst_191_);
v___x_204_ = lean_apply_2(v_toPure_195_, lean_box(0), v___x_198_);
return v___x_204_;
}
else
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((size_t)0ULL);
v___x_206_ = lean_usize_of_nat(v___x_197_);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_191_, v___f_202_, v_entries_196_, v___x_205_, v___x_206_, v___x_198_);
return v___x_207_;
}
}
else
{
size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((size_t)0ULL);
v___x_209_ = lean_usize_of_nat(v___x_197_);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_191_, v___f_202_, v_entries_196_, v___x_208_, v___x_209_, v___x_198_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___boxed(lean_object* v_env_211_, lean_object* v_attr_212_, lean_object* v_inst_213_, lean_object* v_f_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(v_env_211_, v_attr_212_, v_inst_213_, v_f_214_);
lean_dec_ref(v_attr_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(lean_object* v_m_216_, lean_object* v_00_u03b2_217_, lean_object* v_env_218_, lean_object* v_attr_219_, lean_object* v_inst_220_, lean_object* v_f_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(v_env_218_, v_attr_219_, v_inst_220_, v_f_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___boxed(lean_object* v_m_223_, lean_object* v_00_u03b2_224_, lean_object* v_env_225_, lean_object* v_attr_226_, lean_object* v_inst_227_, lean_object* v_f_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(v_m_223_, v_00_u03b2_224_, v_env_225_, v_attr_226_, v_inst_227_, v_f_228_);
lean_dec_ref(v_attr_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(lean_object* v_env_236_, lean_object* v_opts_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = l_Lake_packageAttr;
lean_inc_ref(v_env_236_);
v___x_239_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_238_, v_env_236_);
v___x_240_ = lean_array_to_list(v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_dec_ref(v_env_236_);
v___x_241_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1));
return v___x_241_;
}
else
{
lean_object* v_tail_242_; 
v_tail_242_ = lean_ctor_get(v___x_240_, 1);
lean_inc(v_tail_242_);
if (lean_obj_tag(v_tail_242_) == 0)
{
lean_object* v_head_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_head_243_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_head_243_);
lean_dec_ref_known(v___x_240_, 2);
v___x_244_ = l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
v___x_245_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_236_, v_opts_237_, v___x_244_, v_head_243_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; 
lean_dec_ref_known(v___x_240_, 2);
lean_dec(v_tail_242_);
lean_dec_ref(v_env_236_);
v___x_246_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3));
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___boxed(lean_object* v_env_247_, lean_object* v_opts_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_247_, v_opts_248_);
lean_dec_ref(v_opts_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(lean_object* v_e_250_){
_start:
{
if (lean_obj_tag(v_e_250_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_a_252_ = lean_ctor_get(v_e_250_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_e_250_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v_e_250_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v_e_250_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_mk_io_user_error(v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v_e_250_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v_e_250_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v_e_250_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v_e_250_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 0);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg___boxed(lean_object* v_e_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(lean_object* v_00_u03b1_272_, lean_object* v_e_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___boxed(lean_object* v_00_u03b1_276_, lean_object* v_e_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(v_00_u03b1_276_, v_e_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0(lean_object* v_env_280_, lean_object* v_opts_281_, lean_object* v___x_282_, lean_object* v_name_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_280_, v_opts_281_, v___x_282_, v_name_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed(lean_object* v_env_285_, lean_object* v_opts_286_, lean_object* v___x_287_, lean_object* v_name_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_LakefileConfig_loadFromEnv___lam__0(v_env_285_, v_opts_286_, v___x_287_, v_name_288_);
lean_dec_ref(v_opts_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1(uint8_t v___x_291_, lean_object* v_env_292_, lean_object* v_opts_293_, lean_object* v___x_294_, lean_object* v___x_295_, lean_object* v_scriptName_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_inc_n(v_scriptName_296_, 2);
v___x_299_ = l_Lean_Name_toString(v_scriptName_296_, v___x_291_);
lean_inc_ref(v_env_292_);
v___x_300_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_292_, v_opts_293_, v___x_294_, v_scriptName_296_);
v___x_301_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = 1;
v___x_304_ = l_Lean_Options_empty;
v___x_305_ = lean_box(0);
v___x_306_ = lean_box(0);
v___x_307_ = l_Lean_findDocString_x3f(v_env_292_, v_scriptName_296_, v___x_303_, v___x_304_, v___x_305_, v___x_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0));
v___x_310_ = lean_string_append(v___x_295_, v___x_309_);
v___x_311_ = lean_string_append(v___x_310_, v___x_299_);
lean_dec_ref(v___x_299_);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_a_302_);
lean_ctor_set(v___x_312_, 2, v_a_308_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___y_297_);
return v___x_313_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_a_302_);
lean_dec_ref(v___x_299_);
lean_dec_ref(v___x_295_);
v_a_314_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_307_, 1);
v___x_315_ = lean_io_error_to_string(v_a_314_);
v___x_316_ = 3;
v___x_317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*1, v___x_316_);
v___x_318_ = lean_array_get_size(v___y_297_);
v___x_319_ = lean_array_push(v___y_297_, v___x_317_);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec_ref(v___x_299_);
lean_dec(v_scriptName_296_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v_env_292_);
v_a_321_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_301_, 1);
v___x_322_ = lean_io_error_to_string(v_a_321_);
v___x_323_ = 3;
v___x_324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_323_);
v___x_325_ = lean_array_get_size(v___y_297_);
v___x_326_ = lean_array_push(v___y_297_, v___x_324_);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object* v___x_328_, lean_object* v_env_329_, lean_object* v_opts_330_, lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v_scriptName_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_51094__boxed_336_; lean_object* v_res_337_; 
v___x_51094__boxed_336_ = lean_unbox(v___x_328_);
v_res_337_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_51094__boxed_336_, v_env_329_, v_opts_330_, v___x_331_, v___x_332_, v_scriptName_333_, v___y_334_);
lean_dec_ref(v_opts_330_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object* v_env_340_, lean_object* v_opts_341_, lean_object* v___x_342_, size_t v_sz_343_, size_t v_i_344_, lean_object* v_bs_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_a_349_; lean_object* v_a_350_; uint8_t v___x_352_; 
v___x_352_ = lean_usize_dec_lt(v_i_344_, v_sz_343_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_dec(v___x_342_);
lean_dec_ref(v_env_340_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_bs_345_);
lean_ctor_set(v___x_353_, 1, v___y_346_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v_v_355_; lean_object* v___x_356_; 
v___x_354_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_355_ = lean_array_uget_borrowed(v_bs_345_, v_i_344_);
lean_inc(v_v_355_);
lean_inc_ref(v_env_340_);
v___x_356_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_340_, v_opts_341_, v___x_354_, v_v_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_bs_345_);
lean_dec(v___x_342_);
lean_dec_ref(v_env_340_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v___x_358_ = 3;
v___x_359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_359_, 0, v_a_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v___x_358_);
v___x_360_ = lean_array_get_size(v___y_346_);
v___x_361_ = lean_array_push(v___y_346_, v___x_359_);
v_a_349_ = v___x_360_;
v_a_350_ = v___x_361_;
goto v___jp_348_;
}
else
{
lean_object* v_a_362_; lean_object* v_pkg_363_; lean_object* v_fn_364_; uint8_t v___x_365_; 
v_a_362_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_356_, 1);
v_pkg_363_ = lean_ctor_get(v_a_362_, 0);
lean_inc(v_pkg_363_);
v_fn_364_ = lean_ctor_get(v_a_362_, 1);
lean_inc_ref(v_fn_364_);
lean_dec(v_a_362_);
v___x_365_ = lean_name_eq(v_pkg_363_, v___x_342_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_fn_364_);
lean_dec_ref(v_bs_345_);
lean_dec_ref(v_env_340_);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0));
v___x_367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_363_, v___x_352_);
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
lean_dec_ref(v___x_367_);
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
v___x_371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_342_, v___x_352_);
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
lean_dec_ref(v___x_371_);
v___x_373_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
v___x_375_ = 3;
v___x_376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*1, v___x_375_);
v___x_377_ = lean_array_get_size(v___y_346_);
v___x_378_ = lean_array_push(v___y_346_, v___x_376_);
v_a_349_ = v___x_377_;
v_a_350_ = v___x_378_;
goto v___jp_348_;
}
else
{
lean_object* v___x_379_; lean_object* v_bs_x27_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; 
lean_dec(v_pkg_363_);
v___x_379_ = lean_unsigned_to_nat(0u);
v_bs_x27_380_ = lean_array_uset(v_bs_345_, v_i_344_, v___x_379_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_add(v_i_344_, v___x_381_);
v___x_383_ = lean_array_uset(v_bs_x27_380_, v_i_344_, v_fn_364_);
v_i_344_ = v___x_382_;
v_bs_345_ = v___x_383_;
goto _start;
}
}
}
v___jp_348_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v_a_349_);
lean_ctor_set(v___x_351_, 1, v_a_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object* v_env_385_, lean_object* v_opts_386_, lean_object* v___x_387_, lean_object* v_sz_388_, lean_object* v_i_389_, lean_object* v_bs_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v_sz_boxed_393_ = lean_unbox_usize(v_sz_388_);
lean_dec(v_sz_388_);
v_i_boxed_394_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_385_, v_opts_386_, v___x_387_, v_sz_boxed_393_, v_i_boxed_394_, v_bs_390_, v___y_391_);
lean_dec_ref(v_opts_386_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object* v___x_399_, size_t v_sz_400_, size_t v_i_401_, lean_object* v_bs_402_, lean_object* v___y_403_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v___x_399_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_bs_402_);
lean_ctor_set(v___x_406_, 1, v___y_403_);
return v___x_406_;
}
else
{
lean_object* v_v_407_; lean_object* v_pkg_408_; lean_object* v_name_409_; uint8_t v___x_410_; 
v_v_407_ = lean_array_uget(v_bs_402_, v_i_401_);
v_pkg_408_ = lean_ctor_get(v_v_407_, 0);
v_name_409_ = lean_ctor_get(v_v_407_, 1);
v___x_410_ = lean_name_eq(v_pkg_408_, v___x_399_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_inc(v_name_409_);
lean_inc(v_pkg_408_);
lean_dec(v_v_407_);
lean_dec_ref(v_bs_402_);
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0));
v___x_412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_409_, v___x_405_);
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
lean_dec_ref(v___x_412_);
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1));
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
v___x_416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_408_, v___x_405_);
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
lean_dec_ref(v___x_416_);
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2));
v___x_419_ = lean_string_append(v___x_417_, v___x_418_);
v___x_420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_399_, v___x_405_);
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
lean_dec_ref(v___x_420_);
v___x_422_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
v___x_424_ = 3;
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
v___x_426_ = lean_array_get_size(v___y_403_);
v___x_427_ = lean_array_push(v___y_403_, v___x_425_);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v_bs_x27_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v_bs_x27_430_ = lean_array_uset(v_bs_402_, v_i_401_, v___x_429_);
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_401_, v___x_431_);
v___x_433_ = lean_array_uset(v_bs_x27_430_, v_i_401_, v_v_407_);
v_i_401_ = v___x_432_;
v_bs_402_ = v___x_433_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___boxed(lean_object* v___x_435_, lean_object* v_sz_436_, lean_object* v_i_437_, lean_object* v_bs_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
size_t v_sz_boxed_441_; size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_sz_boxed_441_ = lean_unbox_usize(v_sz_436_);
lean_dec(v_sz_436_);
v_i_boxed_442_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v___x_435_, v_sz_boxed_441_, v_i_boxed_442_, v_bs_438_, v___y_439_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object* v_t_444_, lean_object* v_k_445_){
_start:
{
if (lean_obj_tag(v_t_444_) == 0)
{
lean_object* v_k_446_; lean_object* v_v_447_; lean_object* v_l_448_; lean_object* v_r_449_; uint8_t v___x_450_; 
v_k_446_ = lean_ctor_get(v_t_444_, 1);
v_v_447_ = lean_ctor_get(v_t_444_, 2);
v_l_448_ = lean_ctor_get(v_t_444_, 3);
v_r_449_ = lean_ctor_get(v_t_444_, 4);
v___x_450_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_445_, v_k_446_);
switch(v___x_450_)
{
case 0:
{
v_t_444_ = v_l_448_;
goto _start;
}
case 1:
{
lean_object* v___x_452_; 
lean_inc(v_v_447_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_v_447_);
return v___x_452_;
}
default: 
{
v_t_444_ = v_r_449_;
goto _start;
}
}
}
else
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_455_, lean_object* v_k_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_455_, v_k_456_);
lean_dec(v_k_456_);
lean_dec(v_t_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object* v_a_460_, lean_object* v___x_461_, size_t v_sz_462_, size_t v_i_463_, lean_object* v_bs_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_lt(v_i_463_, v_sz_462_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec_ref(v___x_461_);
lean_dec_ref(v_a_460_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_bs_464_);
lean_ctor_set(v___x_468_, 1, v___y_465_);
return v___x_468_;
}
else
{
lean_object* v_toTreeMap_469_; lean_object* v_v_470_; lean_object* v___x_471_; 
v_toTreeMap_469_ = lean_ctor_get(v_a_460_, 0);
v_v_470_ = lean_array_uget_borrowed(v_bs_464_, v_i_463_);
v___x_471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_469_, v_v_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; lean_object* v_name_473_; lean_object* v___x_474_; lean_object* v_bs_x27_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
v_name_473_ = lean_ctor_get(v_val_472_, 1);
lean_inc(v_name_473_);
lean_dec(v_val_472_);
v___x_474_ = lean_unsigned_to_nat(0u);
v_bs_x27_475_ = lean_array_uset(v_bs_464_, v_i_463_, v___x_474_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_add(v_i_463_, v___x_476_);
v___x_478_ = lean_array_uset(v_bs_x27_475_, v_i_463_, v_name_473_);
v_i_463_ = v___x_477_;
v_bs_464_ = v___x_478_;
goto _start;
}
else
{
lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_496_; 
lean_inc(v_v_470_);
lean_dec(v___x_471_);
lean_dec_ref(v_bs_464_);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_460_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_497_ = lean_ctor_get(v_a_460_, 1);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_a_460_, 0);
lean_dec(v_unused_498_);
v___x_481_ = v_a_460_;
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
else
{
lean_dec(v_a_460_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0));
v___x_484_ = lean_string_append(v___x_461_, v___x_483_);
v___x_485_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_470_, v___x_467_);
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_489_ = 3;
v___x_490_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1, v___x_489_);
v___x_491_ = lean_array_get_size(v___y_465_);
v___x_492_ = lean_array_push(v___y_465_, v___x_490_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 1);
lean_ctor_set(v___x_481_, 1, v___x_492_);
lean_ctor_set(v___x_481_, 0, v___x_491_);
v___x_494_ = v___x_481_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object* v_a_499_, lean_object* v___x_500_, lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_bs_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_507_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_499_, v___x_500_, v_sz_boxed_506_, v_i_boxed_507_, v_bs_503_, v___y_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(lean_object* v_f_509_, lean_object* v_as_510_, size_t v_i_511_, size_t v_stop_512_, lean_object* v_b_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_511_, v_stop_512_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_array_uget_borrowed(v_as_510_, v_i_511_);
lean_inc_ref(v_f_509_);
lean_inc(v___x_515_);
v___x_516_ = lean_apply_1(v_f_509_, v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_b_513_);
lean_dec_ref(v_f_509_);
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; size_t v___x_528_; size_t v___x_529_; 
v_a_525_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_516_, 1);
v___x_526_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_515_);
v___x_527_ = l_Lake_RBArray_insert___redArg(v___x_526_, v_b_513_, v___x_515_, v_a_525_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_511_, v___x_528_);
v_i_511_ = v___x_529_;
v_b_513_ = v___x_527_;
goto _start;
}
}
else
{
lean_object* v___x_531_; 
lean_dec_ref(v_f_509_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v_b_513_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_532_, lean_object* v_as_533_, lean_object* v_i_534_, lean_object* v_stop_535_, lean_object* v_b_536_){
_start:
{
size_t v_i_boxed_537_; size_t v_stop_boxed_538_; lean_object* v_res_539_; 
v_i_boxed_537_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_stop_boxed_538_ = lean_unbox_usize(v_stop_535_);
lean_dec(v_stop_535_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_532_, v_as_533_, v_i_boxed_537_, v_stop_boxed_538_, v_b_536_);
lean_dec_ref(v_as_533_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object* v_env_540_, lean_object* v_attr_541_, lean_object* v_f_542_){
_start:
{
lean_object* v_entries_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_entries_543_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_541_, v_env_540_);
v___x_544_ = lean_array_get_size(v_entries_543_);
v___x_545_ = l_Lake_RBArray_mkEmpty___redArg(v___x_544_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_nat_dec_lt(v___x_546_, v___x_544_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v_entries_543_);
lean_dec_ref(v_f_542_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_545_);
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_le(v___x_544_, v___x_544_);
if (v___x_549_ == 0)
{
if (v___x_547_ == 0)
{
lean_object* v___x_550_; 
lean_dec_ref(v_entries_543_);
lean_dec_ref(v_f_542_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_545_);
return v___x_550_;
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_544_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_542_, v_entries_543_, v___x_551_, v___x_552_, v___x_545_);
lean_dec_ref(v_entries_543_);
return v___x_553_;
}
}
else
{
size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((size_t)0ULL);
v___x_555_ = lean_usize_of_nat(v___x_544_);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_542_, v_entries_543_, v___x_554_, v___x_555_, v___x_545_);
lean_dec_ref(v_entries_543_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_env_557_, lean_object* v_attr_558_, lean_object* v_f_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_557_, v_attr_558_, v_f_559_);
lean_dec_ref(v_attr_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_561_, lean_object* v_as_562_, size_t v_i_563_, size_t v_stop_564_, lean_object* v_b_565_, lean_object* v___y_566_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_eq(v_i_563_, v_stop_564_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_array_uget_borrowed(v_as_562_, v_i_563_);
lean_inc_ref(v_f_561_);
lean_inc(v___x_569_);
v___x_570_ = lean_apply_3(v_f_561_, v___x_569_, v___y_566_, lean_box(0));
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
v_a_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_570_, 2);
lean_inc(v___x_569_);
v___x_573_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_569_, v_a_571_, v_b_565_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_563_, v___x_574_);
v_i_563_ = v___x_575_;
v_b_565_ = v___x_573_;
v___y_566_ = v_a_572_;
goto _start;
}
else
{
lean_object* v_a_577_; lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_b_565_);
lean_dec_ref(v_f_561_);
v_a_577_ = lean_ctor_get(v___x_570_, 0);
v_a_578_ = lean_ctor_get(v___x_570_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_570_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_inc(v_a_577_);
lean_dec(v___x_570_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_577_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_586_; 
lean_dec_ref(v_f_561_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_b_565_);
lean_ctor_set(v___x_586_, 1, v___y_566_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_587_, lean_object* v_as_588_, lean_object* v_i_589_, lean_object* v_stop_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
size_t v_i_boxed_594_; size_t v_stop_boxed_595_; lean_object* v_res_596_; 
v_i_boxed_594_ = lean_unbox_usize(v_i_589_);
lean_dec(v_i_589_);
v_stop_boxed_595_ = lean_unbox_usize(v_stop_590_);
lean_dec(v_stop_590_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_587_, v_as_588_, v_i_boxed_594_, v_stop_boxed_595_, v_b_591_, v___y_592_);
lean_dec_ref(v_as_588_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_597_, lean_object* v_attr_598_, lean_object* v_f_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_entries_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_entries_602_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_598_, v_env_597_);
v___x_603_ = lean_box(1);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_array_get_size(v_entries_602_);
v___x_606_ = lean_nat_dec_lt(v___x_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_dec_ref(v_entries_602_);
lean_dec_ref(v_f_599_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_603_);
lean_ctor_set(v___x_607_, 1, v___y_600_);
return v___x_607_;
}
else
{
uint8_t v___x_608_; 
v___x_608_ = lean_nat_dec_le(v___x_605_, v___x_605_);
if (v___x_608_ == 0)
{
if (v___x_606_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_entries_602_);
lean_dec_ref(v_f_599_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_603_);
lean_ctor_set(v___x_609_, 1, v___y_600_);
return v___x_609_;
}
else
{
size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((size_t)0ULL);
v___x_611_ = lean_usize_of_nat(v___x_605_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_599_, v_entries_602_, v___x_610_, v___x_611_, v___x_603_, v___y_600_);
lean_dec_ref(v_entries_602_);
return v___x_612_;
}
}
else
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((size_t)0ULL);
v___x_614_ = lean_usize_of_nat(v___x_605_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_599_, v_entries_602_, v___x_613_, v___x_614_, v___x_603_, v___y_600_);
lean_dec_ref(v_entries_602_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_616_, lean_object* v_attr_617_, lean_object* v_f_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_616_, v_attr_617_, v_f_618_, v___y_619_);
lean_dec_ref(v_attr_617_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_622_, lean_object* v_opts_623_, lean_object* v_as_624_, size_t v_sz_625_, size_t v_i_626_, lean_object* v_b_627_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_lt(v_i_626_, v_sz_625_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec_ref(v_env_622_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_627_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v_a_631_; lean_object* v___x_632_; 
v___x_630_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
v_a_631_ = lean_array_uget_borrowed(v_as_624_, v_i_626_);
lean_inc(v_a_631_);
lean_inc_ref(v_env_622_);
v___x_632_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_622_, v_opts_623_, v___x_630_, v_a_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v_b_627_);
lean_dec_ref(v_env_622_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v_name_642_; lean_object* v_config_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_a_641_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_632_, 1);
v_name_642_ = lean_ctor_get(v_a_641_, 0);
v_config_643_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_645_ = v_a_641_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_config_643_);
lean_inc(v_name_642_);
lean_dec(v_a_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
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
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_name_642_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_config_643_);
v___x_648_ = v_reuseFailAlloc_653_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; 
v___x_649_ = lean_array_push(v_b_627_, v___x_648_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_626_, v___x_650_);
v_i_626_ = v___x_651_;
v_b_627_ = v___x_649_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object* v_env_655_, lean_object* v_opts_656_, lean_object* v_as_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_b_660_){
_start:
{
size_t v_sz_boxed_661_; size_t v_i_boxed_662_; lean_object* v_res_663_; 
v_sz_boxed_661_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_662_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_655_, v_opts_656_, v_as_657_, v_sz_boxed_661_, v_i_boxed_662_, v_b_660_);
lean_dec_ref(v_as_657_);
lean_dec_ref(v_opts_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v___x_667_, lean_object* v_as_668_, size_t v_i_669_, size_t v_stop_670_, lean_object* v_b_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_a_675_; lean_object* v_a_676_; uint8_t v___x_680_; 
v___x_680_ = lean_usize_dec_eq(v_i_669_, v_stop_670_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v_name_682_; lean_object* v_kind_683_; lean_object* v_config_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_681_ = lean_array_uget_borrowed(v_as_668_, v_i_669_);
v_name_682_ = lean_ctor_get(v___x_681_, 1);
v_kind_683_ = lean_ctor_get(v___x_681_, 2);
v_config_684_ = lean_ctor_get(v___x_681_, 3);
v___x_685_ = l_Lake_LeanExe_keyword;
v___x_686_ = lean_name_eq(v_kind_683_, v___x_685_);
if (v___x_686_ == 0)
{
v_a_675_ = v_b_671_;
v_a_676_ = v___y_672_;
goto v___jp_674_;
}
else
{
lean_object* v_root_687_; lean_object* v___x_688_; 
v_root_687_ = lean_ctor_get(v_config_684_, 2);
v___x_688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_671_, v_root_687_);
if (lean_obj_tag(v___x_688_) == 1)
{
lean_object* v_val_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_b_671_);
v_val_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0));
v___x_691_ = lean_string_append(v___x_667_, v___x_690_);
lean_inc(v_name_682_);
v___x_692_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_682_, v___x_686_);
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
lean_dec_ref(v___x_692_);
v___x_694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1));
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
lean_inc(v_root_687_);
v___x_696_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_687_, v___x_686_);
v___x_697_ = lean_string_append(v___x_695_, v___x_696_);
lean_dec_ref(v___x_696_);
v___x_698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2));
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
v___x_700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_689_, v___x_686_);
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
lean_dec_ref(v___x_700_);
v___x_702_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_703_ = lean_string_append(v___x_701_, v___x_702_);
v___x_704_ = 3;
v___x_705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_704_);
v___x_706_ = lean_array_get_size(v___y_672_);
v___x_707_ = lean_array_push(v___y_672_, v___x_705_);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; 
lean_dec(v___x_688_);
lean_inc(v_name_682_);
lean_inc(v_root_687_);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_687_, v_name_682_, v_b_671_);
v_a_675_ = v___x_709_;
v_a_676_ = v___y_672_;
goto v___jp_674_;
}
}
}
else
{
lean_object* v___x_710_; 
lean_dec_ref(v___x_667_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_b_671_);
lean_ctor_set(v___x_710_, 1, v___y_672_);
return v___x_710_;
}
v___jp_674_:
{
size_t v___x_677_; size_t v___x_678_; 
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_669_, v___x_677_);
v_i_669_ = v___x_678_;
v_b_671_ = v_a_675_;
v___y_672_ = v_a_676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v___x_711_, lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_stop_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
size_t v_i_boxed_718_; size_t v_stop_boxed_719_; lean_object* v_res_720_; 
v_i_boxed_718_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_stop_boxed_719_ = lean_unbox_usize(v_stop_714_);
lean_dec(v_stop_714_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_711_, v_as_712_, v_i_boxed_718_, v_stop_boxed_719_, v_b_715_, v___y_716_);
lean_dec_ref(v_as_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v___x_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_bs_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_727_, v_sz_726_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v___x_725_);
lean_dec_ref(v_a_723_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_bs_728_);
lean_ctor_set(v___x_732_, 1, v___y_729_);
return v___x_732_;
}
else
{
lean_object* v_toTreeMap_733_; lean_object* v_v_734_; lean_object* v___x_735_; lean_object* v_bs_x27_736_; lean_object* v_a_738_; lean_object* v_a_739_; lean_object* v___x_744_; 
v_toTreeMap_733_ = lean_ctor_get(v_a_723_, 0);
v_v_734_ = lean_array_uget(v_bs_728_, v_i_727_);
v___x_735_ = lean_unsigned_to_nat(0u);
v_bs_x27_736_ = lean_array_uset(v_bs_728_, v_i_727_, v___x_735_);
v___x_744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_733_, v_v_734_);
if (lean_obj_tag(v___x_744_) == 1)
{
lean_object* v_val_745_; lean_object* v_name_746_; 
lean_dec(v_v_734_);
v_val_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v___x_744_, 1);
v_name_746_ = lean_ctor_get(v_val_745_, 1);
lean_inc(v_name_746_);
lean_dec(v_val_745_);
v_a_738_ = v_name_746_;
v_a_739_ = v___y_729_;
goto v___jp_737_;
}
else
{
uint8_t v___x_747_; 
lean_dec(v___x_744_);
v___x_747_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_734_, v_a_724_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_bs_x27_736_);
v_isSharedCheck_764_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; 
v_unused_765_ = lean_ctor_get(v_a_723_, 1);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_a_723_, 0);
lean_dec(v_unused_766_);
v___x_749_ = v_a_723_;
v_isShared_750_ = v_isSharedCheck_764_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_a_723_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_764_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_752_ = lean_string_append(v___x_725_, v___x_751_);
v___x_753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_734_, v___x_731_);
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
lean_dec_ref(v___x_753_);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
v___x_757_ = 3;
v___x_758_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*1, v___x_757_);
v___x_759_ = lean_array_get_size(v___y_729_);
v___x_760_ = lean_array_push(v___y_729_, v___x_758_);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 1);
lean_ctor_set(v___x_749_, 1, v___x_760_);
lean_ctor_set(v___x_749_, 0, v___x_759_);
v___x_762_ = v___x_749_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
v_a_738_ = v_v_734_;
v_a_739_ = v___y_729_;
goto v___jp_737_;
}
}
v___jp_737_:
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_add(v_i_727_, v___x_740_);
v___x_742_ = lean_array_uset(v_bs_x27_736_, v_i_727_, v_a_738_);
v_i_727_ = v___x_741_;
v_bs_728_ = v___x_742_;
v___y_729_ = v_a_739_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v___x_769_, lean_object* v_sz_770_, lean_object* v_i_771_, lean_object* v_bs_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v_sz_boxed_775_ = lean_unbox_usize(v_sz_770_);
lean_dec(v_sz_770_);
v_i_boxed_776_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_767_, v_a_768_, v___x_769_, v_sz_boxed_775_, v_i_boxed_776_, v_bs_772_, v___y_773_);
lean_dec(v_a_768_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v___x_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_bs_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v___x_781_);
lean_dec_ref(v_a_779_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_bs_784_);
lean_ctor_set(v___x_788_, 1, v___y_785_);
return v___x_788_;
}
else
{
lean_object* v_toTreeMap_789_; lean_object* v_v_790_; lean_object* v___x_791_; lean_object* v_bs_x27_792_; lean_object* v_a_794_; lean_object* v_a_795_; lean_object* v___x_800_; 
v_toTreeMap_789_ = lean_ctor_get(v_a_779_, 0);
v_v_790_ = lean_array_uget(v_bs_784_, v_i_783_);
v___x_791_ = lean_unsigned_to_nat(0u);
v_bs_x27_792_ = lean_array_uset(v_bs_784_, v_i_783_, v___x_791_);
v___x_800_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_789_, v_v_790_);
if (lean_obj_tag(v___x_800_) == 1)
{
lean_object* v_val_801_; lean_object* v_name_802_; 
lean_dec(v_v_790_);
v_val_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v___x_800_, 1);
v_name_802_ = lean_ctor_get(v_val_801_, 1);
lean_inc(v_name_802_);
lean_dec(v_val_801_);
v_a_794_ = v_name_802_;
v_a_795_ = v___y_785_;
goto v___jp_793_;
}
else
{
uint8_t v___x_803_; 
lean_dec(v___x_800_);
v___x_803_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_790_, v_a_780_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_bs_x27_792_);
v_isSharedCheck_820_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_821_ = lean_ctor_get(v_a_779_, 1);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_a_779_, 0);
lean_dec(v_unused_822_);
v___x_805_ = v_a_779_;
v_isShared_806_ = v_isSharedCheck_820_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_a_779_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_820_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_808_ = lean_string_append(v___x_781_, v___x_807_);
v___x_809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_790_, v___x_787_);
v___x_810_ = lean_string_append(v___x_808_, v___x_809_);
lean_dec_ref(v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0));
v___x_812_ = lean_string_append(v___x_810_, v___x_811_);
v___x_813_ = 3;
v___x_814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_813_);
v___x_815_ = lean_array_get_size(v___y_785_);
v___x_816_ = lean_array_push(v___y_785_, v___x_814_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
lean_ctor_set(v___x_805_, 1, v___x_816_);
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_818_ = v___x_805_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
v_a_794_ = v_v_790_;
v_a_795_ = v___y_785_;
goto v___jp_793_;
}
}
v___jp_793_:
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_783_, v___x_796_);
v___x_798_ = lean_array_uset(v_bs_x27_792_, v_i_783_, v_a_794_);
v_i_783_ = v___x_797_;
v_bs_784_ = v___x_798_;
v___y_785_ = v_a_795_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v___x_825_, lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_bs_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
size_t v_sz_boxed_831_; size_t v_i_boxed_832_; lean_object* v_res_833_; 
v_sz_boxed_831_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_832_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_823_, v_a_824_, v___x_825_, v_sz_boxed_831_, v_i_boxed_832_, v_bs_828_, v___y_829_);
lean_dec(v_a_824_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_835_, lean_object* v___x_836_, size_t v_sz_837_, size_t v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec_ref(v___x_836_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_bs_839_);
lean_ctor_set(v___x_843_, 1, v___y_840_);
return v___x_843_;
}
else
{
lean_object* v_v_844_; lean_object* v___x_845_; 
v_v_844_ = lean_array_uget_borrowed(v_bs_839_, v_i_838_);
v___x_845_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_835_, v_v_844_);
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v_val_846_; lean_object* v___x_847_; lean_object* v_bs_x27_848_; size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; 
v_val_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = lean_unsigned_to_nat(0u);
v_bs_x27_848_ = lean_array_uset(v_bs_839_, v_i_838_, v___x_847_);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_838_, v___x_849_);
v___x_851_ = lean_array_uset(v_bs_x27_848_, v_i_838_, v_val_846_);
v_i_838_ = v___x_850_;
v_bs_839_ = v___x_851_;
goto _start;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc(v_v_844_);
lean_dec(v___x_845_);
lean_dec_ref(v_bs_839_);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_854_ = lean_string_append(v___x_836_, v___x_853_);
v___x_855_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_844_, v___x_842_);
v___x_856_ = lean_string_append(v___x_854_, v___x_855_);
lean_dec_ref(v___x_855_);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_858_ = lean_string_append(v___x_856_, v___x_857_);
v___x_859_ = 3;
v___x_860_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*1, v___x_859_);
v___x_861_ = lean_array_get_size(v___y_840_);
v___x_862_ = lean_array_push(v___y_840_, v___x_860_);
v___x_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_864_, lean_object* v___x_865_, lean_object* v_sz_866_, lean_object* v_i_867_, lean_object* v_bs_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
size_t v_sz_boxed_871_; size_t v_i_boxed_872_; lean_object* v_res_873_; 
v_sz_boxed_871_ = lean_unbox_usize(v_sz_866_);
lean_dec(v_sz_866_);
v_i_boxed_872_ = lean_unbox_usize(v_i_867_);
lean_dec(v_i_867_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_864_, v___x_865_, v_sz_boxed_871_, v_i_boxed_872_, v_bs_868_, v___y_869_);
lean_dec(v_a_864_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_874_, lean_object* v_opts_875_, size_t v_sz_876_, size_t v_i_877_, lean_object* v_bs_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_877_, v_sz_876_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_dec_ref(v_env_874_);
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v_bs_878_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; lean_object* v_v_882_; lean_object* v___x_883_; 
v___x_881_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_;
v_v_882_ = lean_array_uget_borrowed(v_bs_878_, v_i_877_);
lean_inc(v_v_882_);
lean_inc_ref(v_env_874_);
v___x_883_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_874_, v_opts_875_, v___x_881_, v_v_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_bs_878_);
lean_dec_ref(v_env_874_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v_bs_x27_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v_a_892_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_883_, 1);
v___x_893_ = lean_unsigned_to_nat(0u);
v_bs_x27_894_ = lean_array_uset(v_bs_878_, v_i_877_, v___x_893_);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_877_, v___x_895_);
v___x_897_ = lean_array_uset(v_bs_x27_894_, v_i_877_, v_a_892_);
v_i_877_ = v___x_896_;
v_bs_878_ = v___x_897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_899_, lean_object* v_opts_900_, lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_bs_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_905_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_899_, v_opts_900_, v_sz_boxed_904_, v_i_boxed_905_, v_bs_903_);
lean_dec_ref(v_opts_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_907_, lean_object* v_opts_908_, lean_object* v_as_909_, size_t v_sz_910_, size_t v_i_911_, lean_object* v_b_912_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = lean_usize_dec_lt(v_i_911_, v_sz_910_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec_ref(v_env_907_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_b_912_);
return v___x_914_;
}
else
{
lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_917_; 
v___x_915_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
v_a_916_ = lean_array_uget_borrowed(v_as_909_, v_i_911_);
lean_inc(v_a_916_);
lean_inc_ref(v_env_907_);
v___x_917_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_907_, v_opts_908_, v___x_915_, v_a_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v_b_912_);
lean_dec_ref(v_env_907_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v_name_927_; lean_object* v_config_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_939_; 
v_a_926_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_917_, 1);
v_name_927_ = lean_ctor_get(v_a_926_, 0);
v_config_928_ = lean_ctor_get(v_a_926_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_939_ == 0)
{
v___x_930_ = v_a_926_;
v_isShared_931_ = v_isSharedCheck_939_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_config_928_);
lean_inc(v_name_927_);
lean_dec(v_a_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_939_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_name_927_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_config_928_);
v___x_933_ = v_reuseFailAlloc_938_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; size_t v___x_935_; size_t v___x_936_; 
v___x_934_ = lean_array_push(v_b_912_, v___x_933_);
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_911_, v___x_935_);
v_i_911_ = v___x_936_;
v_b_912_ = v___x_934_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_940_, lean_object* v_opts_941_, lean_object* v_as_942_, lean_object* v_sz_943_, lean_object* v_i_944_, lean_object* v_b_945_){
_start:
{
size_t v_sz_boxed_946_; size_t v_i_boxed_947_; lean_object* v_res_948_; 
v_sz_boxed_946_ = lean_unbox_usize(v_sz_943_);
lean_dec(v_sz_943_);
v_i_boxed_947_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_res_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_940_, v_opts_941_, v_as_942_, v_sz_boxed_946_, v_i_boxed_947_, v_b_945_);
lean_dec_ref(v_as_942_);
lean_dec_ref(v_opts_941_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_949_, lean_object* v_opts_950_, lean_object* v_as_951_, size_t v_sz_952_, size_t v_i_953_, lean_object* v_b_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v_env_949_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_954_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_959_; 
v___x_957_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
v_a_958_ = lean_array_uget_borrowed(v_as_951_, v_i_953_);
lean_inc(v_a_958_);
lean_inc_ref(v_env_949_);
v___x_959_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_949_, v_opts_950_, v___x_957_, v_a_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v_b_954_);
lean_dec_ref(v_env_949_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
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
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v_name_969_; lean_object* v_config_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_981_; 
v_a_968_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_959_, 1);
v_name_969_ = lean_ctor_get(v_a_968_, 0);
v_config_970_ = lean_ctor_get(v_a_968_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_a_968_);
if (v_isSharedCheck_981_ == 0)
{
v___x_972_ = v_a_968_;
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_config_970_);
lean_inc(v_name_969_);
lean_dec(v_a_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_name_969_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_config_970_);
v___x_975_ = v_reuseFailAlloc_980_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; size_t v___x_977_; size_t v___x_978_; 
v___x_976_ = lean_array_push(v_b_954_, v___x_975_);
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_953_, v___x_977_);
v_i_953_ = v___x_978_;
v_b_954_ = v___x_976_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_982_, lean_object* v_opts_983_, lean_object* v_as_984_, lean_object* v_sz_985_, lean_object* v_i_986_, lean_object* v_b_987_){
_start:
{
size_t v_sz_boxed_988_; size_t v_i_boxed_989_; lean_object* v_res_990_; 
v_sz_boxed_988_ = lean_unbox_usize(v_sz_985_);
lean_dec(v_sz_985_);
v_i_boxed_989_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_982_, v_opts_983_, v_as_984_, v_sz_boxed_988_, v_i_boxed_989_, v_b_987_);
lean_dec_ref(v_as_984_);
lean_dec_ref(v_opts_983_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_t_991_, lean_object* v_k_992_){
_start:
{
if (lean_obj_tag(v_t_991_) == 0)
{
lean_object* v_k_993_; lean_object* v_v_994_; lean_object* v_l_995_; lean_object* v_r_996_; uint8_t v___x_997_; 
v_k_993_ = lean_ctor_get(v_t_991_, 1);
v_v_994_ = lean_ctor_get(v_t_991_, 2);
v_l_995_ = lean_ctor_get(v_t_991_, 3);
v_r_996_ = lean_ctor_get(v_t_991_, 4);
v___x_997_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_992_, v_k_993_);
switch(v___x_997_)
{
case 0:
{
v_t_991_ = v_l_995_;
goto _start;
}
case 1:
{
lean_object* v___x_999_; 
lean_inc(v_v_994_);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v_v_994_);
return v___x_999_;
}
default: 
{
v_t_991_ = v_r_996_;
goto _start;
}
}
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_t_1002_, lean_object* v_k_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_1002_, v_k_1003_);
lean_dec(v_k_1003_);
lean_dec(v_t_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(lean_object* v_k_1005_, lean_object* v_v_1006_, lean_object* v_t_1007_){
_start:
{
if (lean_obj_tag(v_t_1007_) == 0)
{
lean_object* v_size_1008_; lean_object* v_k_1009_; lean_object* v_v_1010_; lean_object* v_l_1011_; lean_object* v_r_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1292_; 
v_size_1008_ = lean_ctor_get(v_t_1007_, 0);
v_k_1009_ = lean_ctor_get(v_t_1007_, 1);
v_v_1010_ = lean_ctor_get(v_t_1007_, 2);
v_l_1011_ = lean_ctor_get(v_t_1007_, 3);
v_r_1012_ = lean_ctor_get(v_t_1007_, 4);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_t_1007_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1014_ = v_t_1007_;
v_isShared_1015_ = v_isSharedCheck_1292_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_r_1012_);
lean_inc(v_l_1011_);
lean_inc(v_v_1010_);
lean_inc(v_k_1009_);
lean_inc(v_size_1008_);
lean_dec(v_t_1007_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1292_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
uint8_t v___x_1016_; 
v___x_1016_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1005_, v_k_1009_);
switch(v___x_1016_)
{
case 0:
{
lean_object* v_impl_1017_; lean_object* v___x_1018_; 
lean_dec(v_size_1008_);
v_impl_1017_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1005_, v_v_1006_, v_l_1011_);
v___x_1018_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1012_) == 0)
{
lean_object* v_size_1019_; lean_object* v_size_1020_; lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v_l_1023_; lean_object* v_r_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_size_1019_ = lean_ctor_get(v_r_1012_, 0);
v_size_1020_ = lean_ctor_get(v_impl_1017_, 0);
lean_inc(v_size_1020_);
v_k_1021_ = lean_ctor_get(v_impl_1017_, 1);
lean_inc(v_k_1021_);
v_v_1022_ = lean_ctor_get(v_impl_1017_, 2);
lean_inc(v_v_1022_);
v_l_1023_ = lean_ctor_get(v_impl_1017_, 3);
lean_inc(v_l_1023_);
v_r_1024_ = lean_ctor_get(v_impl_1017_, 4);
lean_inc(v_r_1024_);
v___x_1025_ = lean_unsigned_to_nat(3u);
v___x_1026_ = lean_nat_mul(v___x_1025_, v_size_1019_);
v___x_1027_ = lean_nat_dec_lt(v___x_1026_, v_size_1020_);
lean_dec(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec(v_r_1024_);
lean_dec(v_l_1023_);
lean_dec(v_v_1022_);
lean_dec(v_k_1021_);
v___x_1028_ = lean_nat_add(v___x_1018_, v_size_1020_);
lean_dec(v_size_1020_);
v___x_1029_ = lean_nat_add(v___x_1028_, v_size_1019_);
lean_dec(v___x_1028_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 3, v_impl_1017_);
lean_ctor_set(v___x_1014_, 0, v___x_1029_);
v___x_1031_ = v___x_1014_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_impl_1017_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_r_1012_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1098_; 
v_isSharedCheck_1098_ = !lean_is_exclusive(v_impl_1017_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; 
v_unused_1099_ = lean_ctor_get(v_impl_1017_, 4);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_impl_1017_, 3);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_impl_1017_, 2);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_impl_1017_, 1);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_impl_1017_, 0);
lean_dec(v_unused_1103_);
v___x_1034_ = v_impl_1017_;
v_isShared_1035_ = v_isSharedCheck_1098_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_impl_1017_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1098_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_size_1036_; lean_object* v_size_1037_; lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v_l_1040_; lean_object* v_r_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_size_1036_ = lean_ctor_get(v_l_1023_, 0);
v_size_1037_ = lean_ctor_get(v_r_1024_, 0);
v_k_1038_ = lean_ctor_get(v_r_1024_, 1);
v_v_1039_ = lean_ctor_get(v_r_1024_, 2);
v_l_1040_ = lean_ctor_get(v_r_1024_, 3);
v_r_1041_ = lean_ctor_get(v_r_1024_, 4);
v___x_1042_ = lean_unsigned_to_nat(2u);
v___x_1043_ = lean_nat_mul(v___x_1042_, v_size_1036_);
v___x_1044_ = lean_nat_dec_lt(v_size_1037_, v___x_1043_);
lean_dec(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1073_; 
lean_inc(v_r_1041_);
lean_inc(v_l_1040_);
lean_inc(v_v_1039_);
lean_inc(v_k_1038_);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_r_1024_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1074_ = lean_ctor_get(v_r_1024_, 4);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_r_1024_, 3);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_r_1024_, 2);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_r_1024_, 1);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_r_1024_, 0);
lean_dec(v_unused_1078_);
v___x_1046_ = v_r_1024_;
v_isShared_1047_ = v_isSharedCheck_1073_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v_r_1024_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1073_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___x_1061_; lean_object* v___y_1063_; 
v___x_1048_ = lean_nat_add(v___x_1018_, v_size_1020_);
lean_dec(v_size_1020_);
v___x_1049_ = lean_nat_add(v___x_1048_, v_size_1019_);
lean_dec(v___x_1048_);
v___x_1061_ = lean_nat_add(v___x_1018_, v_size_1036_);
if (lean_obj_tag(v_l_1040_) == 0)
{
lean_object* v_size_1071_; 
v_size_1071_ = lean_ctor_get(v_l_1040_, 0);
lean_inc(v_size_1071_);
v___y_1063_ = v_size_1071_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___y_1063_ = v___x_1072_;
goto v___jp_1062_;
}
v___jp_1050_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1054_ = lean_nat_add(v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v_r_1012_);
lean_ctor_set(v___x_1046_, 3, v_r_1041_);
lean_ctor_set(v___x_1046_, 2, v_v_1010_);
lean_ctor_set(v___x_1046_, 1, v_k_1009_);
lean_ctor_set(v___x_1046_, 0, v___x_1054_);
v___x_1056_ = v___x_1046_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_r_1041_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_r_1012_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v___x_1056_);
lean_ctor_set(v___x_1034_, 3, v___y_1051_);
lean_ctor_set(v___x_1034_, 2, v_v_1039_);
lean_ctor_set(v___x_1034_, 1, v_k_1038_);
lean_ctor_set(v___x_1034_, 0, v___x_1049_);
v___x_1058_ = v___x_1034_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v___y_1051_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_nat_add(v___x_1061_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec(v___x_1061_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_l_1040_);
lean_ctor_set(v___x_1014_, 3, v_l_1023_);
lean_ctor_set(v___x_1014_, 2, v_v_1022_);
lean_ctor_set(v___x_1014_, 1, v_k_1021_);
lean_ctor_set(v___x_1014_, 0, v___x_1064_);
v___x_1066_ = v___x_1014_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_l_1023_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_l_1040_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_nat_add(v___x_1018_, v_size_1019_);
if (lean_obj_tag(v_r_1041_) == 0)
{
lean_object* v_size_1068_; 
v_size_1068_ = lean_ctor_get(v_r_1041_, 0);
lean_inc(v_size_1068_);
v___y_1051_ = v___x_1066_;
v___y_1052_ = v___x_1067_;
v___y_1053_ = v_size_1068_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___y_1051_ = v___x_1066_;
v___y_1052_ = v___x_1067_;
v___y_1053_ = v___x_1069_;
goto v___jp_1050_;
}
}
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_del_object(v___x_1014_);
v___x_1079_ = lean_nat_add(v___x_1018_, v_size_1020_);
lean_dec(v_size_1020_);
v___x_1080_ = lean_nat_add(v___x_1079_, v_size_1019_);
lean_dec(v___x_1079_);
v___x_1081_ = lean_nat_add(v___x_1018_, v_size_1019_);
v___x_1082_ = lean_nat_add(v___x_1081_, v_size_1037_);
lean_dec(v___x_1081_);
lean_inc_ref(v_r_1012_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v_r_1012_);
lean_ctor_set(v___x_1034_, 3, v_r_1024_);
lean_ctor_set(v___x_1034_, 2, v_v_1010_);
lean_ctor_set(v___x_1034_, 1, v_k_1009_);
lean_ctor_set(v___x_1034_, 0, v___x_1082_);
v___x_1084_ = v___x_1034_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_r_1024_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_r_1012_);
v___x_1084_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_isSharedCheck_1091_ = !lean_is_exclusive(v_r_1012_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1092_ = lean_ctor_get(v_r_1012_, 4);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_1012_, 3);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_r_1012_, 2);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_r_1012_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_r_1012_, 0);
lean_dec(v_unused_1096_);
v___x_1086_ = v_r_1012_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_dec(v_r_1012_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 4, v___x_1084_);
lean_ctor_set(v___x_1086_, 3, v_l_1023_);
lean_ctor_set(v___x_1086_, 2, v_v_1022_);
lean_ctor_set(v___x_1086_, 1, v_k_1021_);
lean_ctor_set(v___x_1086_, 0, v___x_1080_);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_l_1023_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v___x_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1104_; 
v_l_1104_ = lean_ctor_get(v_impl_1017_, 3);
lean_inc(v_l_1104_);
if (lean_obj_tag(v_l_1104_) == 0)
{
lean_object* v_r_1105_; lean_object* v_k_1106_; lean_object* v_v_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v_r_1105_ = lean_ctor_get(v_impl_1017_, 4);
v_k_1106_ = lean_ctor_get(v_impl_1017_, 1);
v_v_1107_ = lean_ctor_get(v_impl_1017_, 2);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_impl_1017_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1119_ = lean_ctor_get(v_impl_1017_, 3);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_impl_1017_, 0);
lean_dec(v_unused_1120_);
v___x_1109_ = v_impl_1017_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_r_1105_);
lean_inc(v_v_1107_);
lean_inc(v_k_1106_);
lean_dec(v_impl_1017_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1105_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 3, v_r_1105_);
lean_ctor_set(v___x_1109_, 2, v_v_1010_);
lean_ctor_set(v___x_1109_, 1, v_k_1009_);
lean_ctor_set(v___x_1109_, 0, v___x_1018_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_r_1105_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_r_1105_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v___x_1113_);
lean_ctor_set(v___x_1014_, 3, v_l_1104_);
lean_ctor_set(v___x_1014_, 2, v_v_1107_);
lean_ctor_set(v___x_1014_, 1, v_k_1106_);
lean_ctor_set(v___x_1014_, 0, v___x_1111_);
v___x_1115_ = v___x_1014_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_1107_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_l_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_r_1121_; 
v_r_1121_ = lean_ctor_get(v_impl_1017_, 4);
lean_inc(v_r_1121_);
if (lean_obj_tag(v_r_1121_) == 0)
{
lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1146_; 
v_k_1122_ = lean_ctor_get(v_impl_1017_, 1);
v_v_1123_ = lean_ctor_get(v_impl_1017_, 2);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_impl_1017_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; lean_object* v_unused_1148_; lean_object* v_unused_1149_; 
v_unused_1147_ = lean_ctor_get(v_impl_1017_, 4);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_impl_1017_, 3);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_impl_1017_, 0);
lean_dec(v_unused_1149_);
v___x_1125_ = v_impl_1017_;
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_impl_1017_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1142_; 
v_k_1127_ = lean_ctor_get(v_r_1121_, 1);
v_v_1128_ = lean_ctor_get(v_r_1121_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_r_1121_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1143_ = lean_ctor_get(v_r_1121_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_r_1121_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_r_1121_, 0);
lean_dec(v_unused_1145_);
v___x_1130_ = v_r_1121_;
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
lean_dec(v_r_1121_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(3u);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v_l_1104_);
lean_ctor_set(v___x_1130_, 3, v_l_1104_);
lean_ctor_set(v___x_1130_, 2, v_v_1123_);
lean_ctor_set(v___x_1130_, 1, v_k_1122_);
lean_ctor_set(v___x_1130_, 0, v___x_1018_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_l_1104_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_l_1104_);
v___x_1134_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_l_1104_);
lean_ctor_set(v___x_1125_, 2, v_v_1010_);
lean_ctor_set(v___x_1125_, 1, v_k_1009_);
lean_ctor_set(v___x_1125_, 0, v___x_1018_);
v___x_1136_ = v___x_1125_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_l_1104_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_l_1104_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v___x_1136_);
lean_ctor_set(v___x_1014_, 3, v___x_1134_);
lean_ctor_set(v___x_1014_, 2, v_v_1128_);
lean_ctor_set(v___x_1014_, 1, v_k_1127_);
lean_ctor_set(v___x_1014_, 0, v___x_1132_);
v___x_1138_ = v___x_1014_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_unsigned_to_nat(2u);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_r_1121_);
lean_ctor_set(v___x_1014_, 3, v_impl_1017_);
lean_ctor_set(v___x_1014_, 0, v___x_1150_);
v___x_1152_ = v___x_1014_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_impl_1017_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_r_1121_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1155_; 
lean_dec(v_v_1010_);
lean_dec(v_k_1009_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 2, v_v_1006_);
lean_ctor_set(v___x_1014_, 1, v_k_1005_);
v___x_1155_ = v___x_1014_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_size_1008_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_k_1005_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_v_1006_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_l_1011_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_r_1012_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
default: 
{
lean_object* v_impl_1157_; lean_object* v___x_1158_; 
lean_dec(v_size_1008_);
v_impl_1157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1005_, v_v_1006_, v_r_1012_);
v___x_1158_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1011_) == 0)
{
lean_object* v_size_1159_; lean_object* v_size_1160_; lean_object* v_k_1161_; lean_object* v_v_1162_; lean_object* v_l_1163_; lean_object* v_r_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_size_1159_ = lean_ctor_get(v_l_1011_, 0);
v_size_1160_ = lean_ctor_get(v_impl_1157_, 0);
lean_inc(v_size_1160_);
v_k_1161_ = lean_ctor_get(v_impl_1157_, 1);
lean_inc(v_k_1161_);
v_v_1162_ = lean_ctor_get(v_impl_1157_, 2);
lean_inc(v_v_1162_);
v_l_1163_ = lean_ctor_get(v_impl_1157_, 3);
lean_inc(v_l_1163_);
v_r_1164_ = lean_ctor_get(v_impl_1157_, 4);
lean_inc(v_r_1164_);
v___x_1165_ = lean_unsigned_to_nat(3u);
v___x_1166_ = lean_nat_mul(v___x_1165_, v_size_1159_);
v___x_1167_ = lean_nat_dec_lt(v___x_1166_, v_size_1160_);
lean_dec(v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_dec(v_r_1164_);
lean_dec(v_l_1163_);
lean_dec(v_v_1162_);
lean_dec(v_k_1161_);
v___x_1168_ = lean_nat_add(v___x_1158_, v_size_1159_);
v___x_1169_ = lean_nat_add(v___x_1168_, v_size_1160_);
lean_dec(v_size_1160_);
lean_dec(v___x_1168_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_impl_1157_);
lean_ctor_set(v___x_1014_, 0, v___x_1169_);
v___x_1171_ = v___x_1014_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_l_1011_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_impl_1157_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v_impl_1157_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; lean_object* v_unused_1241_; 
v_unused_1237_ = lean_ctor_get(v_impl_1157_, 4);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_impl_1157_, 3);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_impl_1157_, 2);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_impl_1157_, 1);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v_impl_1157_, 0);
lean_dec(v_unused_1241_);
v___x_1174_ = v_impl_1157_;
v_isShared_1175_ = v_isSharedCheck_1236_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_impl_1157_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1236_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_size_1176_; lean_object* v_k_1177_; lean_object* v_v_1178_; lean_object* v_l_1179_; lean_object* v_r_1180_; lean_object* v_size_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_size_1176_ = lean_ctor_get(v_l_1163_, 0);
v_k_1177_ = lean_ctor_get(v_l_1163_, 1);
v_v_1178_ = lean_ctor_get(v_l_1163_, 2);
v_l_1179_ = lean_ctor_get(v_l_1163_, 3);
v_r_1180_ = lean_ctor_get(v_l_1163_, 4);
v_size_1181_ = lean_ctor_get(v_r_1164_, 0);
v___x_1182_ = lean_unsigned_to_nat(2u);
v___x_1183_ = lean_nat_mul(v___x_1182_, v_size_1181_);
v___x_1184_ = lean_nat_dec_lt(v_size_1176_, v___x_1183_);
lean_dec(v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1212_; 
lean_inc(v_r_1180_);
lean_inc(v_l_1179_);
lean_inc(v_v_1178_);
lean_inc(v_k_1177_);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_l_1163_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; lean_object* v_unused_1214_; lean_object* v_unused_1215_; lean_object* v_unused_1216_; lean_object* v_unused_1217_; 
v_unused_1213_ = lean_ctor_get(v_l_1163_, 4);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_l_1163_, 3);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_l_1163_, 2);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_l_1163_, 1);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_l_1163_, 0);
lean_dec(v_unused_1217_);
v___x_1186_ = v_l_1163_;
v_isShared_1187_ = v_isSharedCheck_1212_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_l_1163_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1212_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1202_; 
v___x_1188_ = lean_nat_add(v___x_1158_, v_size_1159_);
v___x_1189_ = lean_nat_add(v___x_1188_, v_size_1160_);
lean_dec(v_size_1160_);
if (lean_obj_tag(v_l_1179_) == 0)
{
lean_object* v_size_1210_; 
v_size_1210_ = lean_ctor_get(v_l_1179_, 0);
lean_inc(v_size_1210_);
v___y_1202_ = v_size_1210_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v___y_1202_ = v___x_1211_;
goto v___jp_1201_;
}
v___jp_1190_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_nat_add(v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 4, v_r_1164_);
lean_ctor_set(v___x_1186_, 3, v_r_1180_);
lean_ctor_set(v___x_1186_, 2, v_v_1162_);
lean_ctor_set(v___x_1186_, 1, v_k_1161_);
lean_ctor_set(v___x_1186_, 0, v___x_1194_);
v___x_1196_ = v___x_1186_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_k_1161_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_v_1162_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_r_1164_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v___x_1196_);
lean_ctor_set(v___x_1174_, 3, v___y_1191_);
lean_ctor_set(v___x_1174_, 2, v_v_1178_);
lean_ctor_set(v___x_1174_, 1, v_k_1177_);
lean_ctor_set(v___x_1174_, 0, v___x_1189_);
v___x_1198_ = v___x_1174_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_k_1177_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_v_1178_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v___y_1191_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
v___jp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_nat_add(v___x_1188_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec(v___x_1188_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_l_1179_);
lean_ctor_set(v___x_1014_, 0, v___x_1203_);
v___x_1205_ = v___x_1014_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_l_1011_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_l_1179_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_nat_add(v___x_1158_, v_size_1181_);
if (lean_obj_tag(v_r_1180_) == 0)
{
lean_object* v_size_1207_; 
v_size_1207_ = lean_ctor_get(v_r_1180_, 0);
lean_inc(v_size_1207_);
v___y_1191_ = v___x_1205_;
v___y_1192_ = v___x_1206_;
v___y_1193_ = v_size_1207_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_unsigned_to_nat(0u);
v___y_1191_ = v___x_1205_;
v___y_1192_ = v___x_1206_;
v___y_1193_ = v___x_1208_;
goto v___jp_1190_;
}
}
}
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_del_object(v___x_1014_);
v___x_1218_ = lean_nat_add(v___x_1158_, v_size_1159_);
v___x_1219_ = lean_nat_add(v___x_1218_, v_size_1160_);
lean_dec(v_size_1160_);
v___x_1220_ = lean_nat_add(v___x_1218_, v_size_1176_);
lean_dec(v___x_1218_);
lean_inc_ref(v_l_1011_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v_l_1163_);
lean_ctor_set(v___x_1174_, 3, v_l_1011_);
lean_ctor_set(v___x_1174_, 2, v_v_1010_);
lean_ctor_set(v___x_1174_, 1, v_k_1009_);
lean_ctor_set(v___x_1174_, 0, v___x_1220_);
v___x_1222_ = v___x_1174_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_l_1011_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_l_1163_);
v___x_1222_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_isSharedCheck_1229_ = !lean_is_exclusive(v_l_1011_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; lean_object* v_unused_1231_; lean_object* v_unused_1232_; lean_object* v_unused_1233_; lean_object* v_unused_1234_; 
v_unused_1230_ = lean_ctor_get(v_l_1011_, 4);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_l_1011_, 3);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_l_1011_, 2);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_l_1011_, 1);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_l_1011_, 0);
lean_dec(v_unused_1234_);
v___x_1224_ = v_l_1011_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v_l_1011_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 4, v_r_1164_);
lean_ctor_set(v___x_1224_, 3, v___x_1222_);
lean_ctor_set(v___x_1224_, 2, v_v_1162_);
lean_ctor_set(v___x_1224_, 1, v_k_1161_);
lean_ctor_set(v___x_1224_, 0, v___x_1219_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1161_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1162_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1164_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1242_; 
v_l_1242_ = lean_ctor_get(v_impl_1157_, 3);
lean_inc(v_l_1242_);
if (lean_obj_tag(v_l_1242_) == 0)
{
lean_object* v_r_1243_; lean_object* v_k_1244_; lean_object* v_v_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1268_; 
v_r_1243_ = lean_ctor_get(v_impl_1157_, 4);
v_k_1244_ = lean_ctor_get(v_impl_1157_, 1);
v_v_1245_ = lean_ctor_get(v_impl_1157_, 2);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_impl_1157_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; lean_object* v_unused_1270_; 
v_unused_1269_ = lean_ctor_get(v_impl_1157_, 3);
lean_dec(v_unused_1269_);
v_unused_1270_ = lean_ctor_get(v_impl_1157_, 0);
lean_dec(v_unused_1270_);
v___x_1247_ = v_impl_1157_;
v_isShared_1248_ = v_isSharedCheck_1268_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_r_1243_);
lean_inc(v_v_1245_);
lean_inc(v_k_1244_);
lean_dec(v_impl_1157_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1268_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1264_; 
v_k_1249_ = lean_ctor_get(v_l_1242_, 1);
v_v_1250_ = lean_ctor_get(v_l_1242_, 2);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_l_1242_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; lean_object* v_unused_1266_; lean_object* v_unused_1267_; 
v_unused_1265_ = lean_ctor_get(v_l_1242_, 4);
lean_dec(v_unused_1265_);
v_unused_1266_ = lean_ctor_get(v_l_1242_, 3);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v_l_1242_, 0);
lean_dec(v_unused_1267_);
v___x_1252_ = v_l_1242_;
v_isShared_1253_ = v_isSharedCheck_1264_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_dec(v_l_1242_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1264_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1243_, 2);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_r_1243_);
lean_ctor_set(v___x_1252_, 3, v_r_1243_);
lean_ctor_set(v___x_1252_, 2, v_v_1010_);
lean_ctor_set(v___x_1252_, 1, v_k_1009_);
lean_ctor_set(v___x_1252_, 0, v___x_1158_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_r_1243_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_r_1243_);
v___x_1256_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
lean_inc(v_r_1243_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 3, v_r_1243_);
lean_ctor_set(v___x_1247_, 0, v___x_1158_);
v___x_1258_ = v___x_1247_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_k_1244_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_v_1245_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_r_1243_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_r_1243_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v___x_1258_);
lean_ctor_set(v___x_1014_, 3, v___x_1256_);
lean_ctor_set(v___x_1014_, 2, v_v_1250_);
lean_ctor_set(v___x_1014_, 1, v_k_1249_);
lean_ctor_set(v___x_1014_, 0, v___x_1254_);
v___x_1260_ = v___x_1014_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
else
{
lean_object* v_r_1271_; 
v_r_1271_ = lean_ctor_get(v_impl_1157_, 4);
lean_inc(v_r_1271_);
if (lean_obj_tag(v_r_1271_) == 0)
{
lean_object* v_k_1272_; lean_object* v_v_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1284_; 
v_k_1272_ = lean_ctor_get(v_impl_1157_, 1);
v_v_1273_ = lean_ctor_get(v_impl_1157_, 2);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_impl_1157_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; lean_object* v_unused_1286_; lean_object* v_unused_1287_; 
v_unused_1285_ = lean_ctor_get(v_impl_1157_, 4);
lean_dec(v_unused_1285_);
v_unused_1286_ = lean_ctor_get(v_impl_1157_, 3);
lean_dec(v_unused_1286_);
v_unused_1287_ = lean_ctor_get(v_impl_1157_, 0);
lean_dec(v_unused_1287_);
v___x_1275_ = v_impl_1157_;
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_v_1273_);
lean_inc(v_k_1272_);
lean_dec(v_impl_1157_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_unsigned_to_nat(3u);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v_l_1242_);
lean_ctor_set(v___x_1275_, 2, v_v_1010_);
lean_ctor_set(v___x_1275_, 1, v_k_1009_);
lean_ctor_set(v___x_1275_, 0, v___x_1158_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_l_1242_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_r_1271_);
lean_ctor_set(v___x_1014_, 3, v___x_1279_);
lean_ctor_set(v___x_1014_, 2, v_v_1273_);
lean_ctor_set(v___x_1014_, 1, v_k_1272_);
lean_ctor_set(v___x_1014_, 0, v___x_1277_);
v___x_1281_ = v___x_1014_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_r_1271_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_unsigned_to_nat(2u);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_impl_1157_);
lean_ctor_set(v___x_1014_, 3, v_r_1271_);
lean_ctor_set(v___x_1014_, 0, v___x_1288_);
v___x_1290_ = v___x_1014_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_r_1271_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_impl_1157_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
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
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_k_1005_);
lean_ctor_set(v___x_1294_, 2, v_v_1006_);
lean_ctor_set(v___x_1294_, 3, v_t_1007_);
lean_ctor_set(v___x_1294_, 4, v_t_1007_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object* v___x_1298_, lean_object* v_as_1299_, size_t v_i_1300_, size_t v_stop_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_eq(v_i_1300_, v_stop_1301_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v_name_1307_; lean_object* v_kind_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_array_uget_borrowed(v_as_1299_, v_i_1300_);
v_name_1307_ = lean_ctor_get(v___x_1306_, 1);
v_kind_1308_ = lean_ctor_get(v___x_1306_, 2);
v___x_1309_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_b_1302_, v_name_1307_);
if (lean_obj_tag(v___x_1309_) == 1)
{
lean_object* v_val_1310_; lean_object* v_kind_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v_b_1302_);
v_val_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v_kind_1311_ = lean_ctor_get(v_val_1310_, 2);
lean_inc(v_kind_1311_);
lean_dec(v_val_1310_);
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0));
v___x_1313_ = lean_string_append(v___x_1298_, v___x_1312_);
v___x_1314_ = 1;
lean_inc(v_name_1307_);
v___x_1315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1307_, v___x_1314_);
v___x_1316_ = lean_string_append(v___x_1313_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1311_, v___x_1314_);
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2));
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
lean_inc(v_kind_1308_);
v___x_1323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1308_, v___x_1314_);
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
v___x_1327_ = 3;
v___x_1328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*1, v___x_1327_);
v___x_1329_ = lean_array_get_size(v___y_1303_);
v___x_1330_ = lean_array_push(v___y_1303_, v___x_1328_);
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; 
lean_dec(v___x_1309_);
lean_inc(v___x_1306_);
lean_inc(v_name_1307_);
v___x_1332_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_name_1307_, v___x_1306_, v_b_1302_);
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_add(v_i_1300_, v___x_1333_);
v_i_1300_ = v___x_1334_;
v_b_1302_ = v___x_1332_;
goto _start;
}
}
else
{
lean_object* v___x_1336_; 
lean_dec_ref(v___x_1298_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_b_1302_);
lean_ctor_set(v___x_1336_, 1, v___y_1303_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object* v___x_1337_, lean_object* v_as_1338_, lean_object* v_i_1339_, lean_object* v_stop_1340_, lean_object* v_b_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
size_t v_i_boxed_1344_; size_t v_stop_boxed_1345_; lean_object* v_res_1346_; 
v_i_boxed_1344_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_stop_boxed_1345_ = lean_unbox_usize(v_stop_1340_);
lean_dec(v_stop_1340_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1337_, v_as_1338_, v_i_boxed_1344_, v_stop_boxed_1345_, v_b_1341_, v___y_1342_);
lean_dec_ref(v_as_1338_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1353_, lean_object* v_opts_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_a_1358_; lean_object* v_a_1359_; lean_object* v_a_1362_; lean_object* v_a_1363_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc_ref(v_env_1353_);
v___x_1365_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1353_, v_opts_1354_);
v___x_1366_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1354_);
lean_inc_ref_n(v_env_1353_, 2);
v___f_1369_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1369_, 0, v_env_1353_);
lean_closure_set(v___f_1369_, 1, v_opts_1354_);
lean_closure_set(v___f_1369_, 2, v___x_1368_);
v___x_1370_ = l_Lake_targetAttr;
v___x_1371_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1353_, v___x_1370_, v___f_1369_);
v___x_1372_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v_baseName_1374_; lean_object* v_keyName_1375_; lean_object* v_config_1376_; lean_object* v_toArray_1377_; size_t v_sz_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v_baseName_1374_ = lean_ctor_get(v_a_1367_, 0);
v_keyName_1375_ = lean_ctor_get(v_a_1367_, 1);
v_config_1376_ = lean_ctor_get(v_a_1367_, 3);
v_toArray_1377_ = lean_ctor_get(v_a_1373_, 1);
v_sz_1378_ = lean_array_size(v_toArray_1377_);
v___x_1379_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1377_);
lean_inc(v_keyName_1375_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v_keyName_1375_, v_sz_1378_, v___x_1379_, v_toArray_1377_, v_a_1355_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1649_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_a_1382_ = lean_ctor_get(v___x_1380_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1384_ = v___x_1380_;
v_isShared_1385_ = v_isSharedCheck_1649_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1649_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v_a_1452_; lean_object* v_a_1453_; lean_object* v___y_1491_; lean_object* v_a_1492_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___x_1620_; lean_object* v_a_1622_; lean_object* v_a_1623_; lean_object* v___y_1631_; uint8_t v___x_1643_; 
v___x_1412_ = l_Lake_instTypeNameScriptFn_unsafe__1;
v___x_1413_ = 0;
lean_inc(v_baseName_1374_);
v___x_1414_ = l_Lean_Name_toString(v_baseName_1374_, v___x_1413_);
v___x_1415_ = lean_box(v___x_1413_);
lean_inc_ref(v___x_1414_);
lean_inc_ref(v_opts_1354_);
lean_inc_ref(v_env_1353_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1416_, 0, v___x_1415_);
lean_closure_set(v___f_1416_, 1, v_env_1353_);
lean_closure_set(v___f_1416_, 2, v_opts_1354_);
lean_closure_set(v___f_1416_, 3, v___x_1412_);
lean_closure_set(v___f_1416_, 4, v___x_1414_);
v___x_1417_ = lean_box(1);
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_array_get_size(v_a_1381_);
v___x_1643_ = lean_nat_dec_lt(v___x_1418_, v___x_1620_);
if (v___x_1643_ == 0)
{
v_a_1622_ = v___x_1417_;
v_a_1623_ = v_a_1382_;
goto v___jp_1621_;
}
else
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_nat_dec_le(v___x_1620_, v___x_1620_);
if (v___x_1644_ == 0)
{
if (v___x_1643_ == 0)
{
v_a_1622_ = v___x_1417_;
v_a_1623_ = v_a_1382_;
goto v___jp_1621_;
}
else
{
size_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_usize_of_nat(v___x_1620_);
lean_inc_ref(v___x_1414_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1414_, v_a_1381_, v___x_1379_, v___x_1645_, v___x_1417_, v_a_1382_);
v___y_1631_ = v___x_1646_;
goto v___jp_1630_;
}
}
else
{
size_t v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_usize_of_nat(v___x_1620_);
lean_inc_ref(v___x_1414_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1414_, v_a_1381_, v___x_1379_, v___x_1647_, v___x_1417_, v_a_1382_);
v___y_1631_ = v___x_1648_;
goto v___jp_1630_;
}
}
v___jp_1386_:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1399_, 0, v_a_1367_);
lean_ctor_set(v___x_1399_, 1, v___y_1393_);
lean_ctor_set(v___x_1399_, 2, v_a_1398_);
lean_ctor_set(v___x_1399_, 3, v_a_1381_);
lean_ctor_set(v___x_1399_, 4, v___y_1388_);
lean_ctor_set(v___x_1399_, 5, v___y_1387_);
lean_ctor_set(v___x_1399_, 6, v___y_1390_);
lean_ctor_set(v___x_1399_, 7, v___y_1394_);
lean_ctor_set(v___x_1399_, 8, v___y_1395_);
lean_ctor_set(v___x_1399_, 9, v___y_1392_);
lean_ctor_set(v___x_1399_, 10, v___y_1389_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v___y_1391_);
lean_ctor_set(v___x_1384_, 0, v___x_1399_);
v___x_1401_ = v___x_1384_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___y_1391_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v_a_1381_);
lean_dec(v_a_1367_);
v_a_1403_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1404_ = lean_io_error_to_string(v_a_1403_);
v___x_1405_ = 3;
v___x_1406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set_uint8(v___x_1406_, sizeof(void*)*1, v___x_1405_);
v___x_1407_ = lean_array_get_size(v___y_1391_);
v___x_1408_ = lean_array_push(v___y_1391_, v___x_1406_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 1);
lean_ctor_set(v___x_1384_, 1, v___x_1408_);
lean_ctor_set(v___x_1384_, 0, v___x_1407_);
v___x_1410_ = v___x_1384_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; size_t v_sz_1432_; lean_object* v___x_1433_; 
v___x_1429_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1430_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1353_, 2);
v___x_1431_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1430_, v_env_1353_);
v_sz_1432_ = lean_array_size(v___x_1431_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1353_, v_opts_1354_, v___x_1431_, v_sz_1432_, v___x_1379_, v___x_1429_);
lean_dec_ref(v___x_1431_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v___y_1387_ = v___y_1421_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v_a_1427_;
v___y_1390_ = v___y_1422_;
v___y_1391_ = v_a_1428_;
v___y_1392_ = v___y_1423_;
v___y_1393_ = v___y_1424_;
v___y_1394_ = v___y_1425_;
v___y_1395_ = v___y_1426_;
v___y_1396_ = v___x_1433_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; size_t v_sz_1437_; lean_object* v___x_1438_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1353_, 2);
v___x_1436_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1435_, v_env_1353_);
v_sz_1437_ = lean_array_size(v___x_1436_);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1353_, v_opts_1354_, v___x_1436_, v_sz_1437_, v___x_1379_, v_a_1434_);
lean_dec_ref(v___x_1436_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v___y_1387_ = v___y_1421_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v_a_1427_;
v___y_1390_ = v___y_1422_;
v___y_1391_ = v_a_1428_;
v___y_1392_ = v___y_1423_;
v___y_1393_ = v___y_1424_;
v___y_1394_ = v___y_1425_;
v___y_1395_ = v___y_1426_;
v___y_1396_ = v___x_1438_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; size_t v_sz_1442_; lean_object* v___x_1443_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1353_);
v___x_1441_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1440_, v_env_1353_);
v_sz_1442_ = lean_array_size(v___x_1441_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1353_, v_opts_1354_, v___x_1441_, v_sz_1442_, v___x_1379_, v_a_1439_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_opts_1354_);
v___y_1387_ = v___y_1421_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v_a_1427_;
v___y_1390_ = v___y_1422_;
v___y_1391_ = v_a_1428_;
v___y_1392_ = v___y_1423_;
v___y_1393_ = v___y_1424_;
v___y_1394_ = v___y_1425_;
v___y_1395_ = v___y_1426_;
v___y_1396_ = v___x_1443_;
goto v___jp_1386_;
}
}
}
v___jp_1444_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; size_t v_sz_1456_; lean_object* v___x_1457_; 
v___x_1454_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1353_);
v___x_1455_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1454_, v_env_1353_);
v_sz_1456_ = lean_array_size(v___x_1455_);
lean_inc_ref(v___x_1414_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1373_, v___y_1448_, v___x_1414_, v_sz_1456_, v___x_1379_, v___x_1455_, v_a_1453_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v_a_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
v_a_1459_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1457_, 2);
v___x_1460_ = lean_array_get_size(v_a_1458_);
v___x_1461_ = lean_nat_dec_lt(v___y_1445_, v___x_1460_);
if (v___x_1461_ == 0)
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_nat_dec_lt(v___x_1418_, v___x_1460_);
if (v___x_1462_ == 0)
{
lean_object* v_lintDriver_1463_; 
lean_dec(v_a_1458_);
lean_dec_ref(v___x_1414_);
v_lintDriver_1463_ = lean_ctor_get(v_config_1376_, 14);
lean_inc_ref(v_lintDriver_1463_);
v___y_1420_ = v___y_1447_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___y_1448_;
v___y_1423_ = v_a_1452_;
v___y_1424_ = v___y_1449_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1451_;
v_a_1427_ = v_lintDriver_1463_;
v_a_1428_ = v_a_1459_;
goto v___jp_1419_;
}
else
{
lean_object* v_lintDriver_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_lintDriver_1464_ = lean_ctor_get(v_config_1376_, 14);
v___x_1465_ = lean_string_utf8_byte_size(v_lintDriver_1464_);
v___x_1466_ = lean_nat_dec_eq(v___x_1465_, v___x_1418_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v___x_1467_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1468_ = lean_string_append(v___x_1414_, v___x_1467_);
v___x_1469_ = 3;
v___x_1470_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*1, v___x_1469_);
v___x_1471_ = lean_array_get_size(v_a_1459_);
v___x_1472_ = lean_array_push(v_a_1459_, v___x_1470_);
v_a_1362_ = v___x_1471_;
v_a_1363_ = v___x_1472_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v___x_1414_);
v___x_1473_ = lean_array_fget(v_a_1458_, v___x_1418_);
lean_dec(v_a_1458_);
v___x_1474_ = l_Lean_Name_toString(v___x_1473_, v___x_1466_);
v___y_1420_ = v___y_1447_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___y_1448_;
v___y_1423_ = v_a_1452_;
v___y_1424_ = v___y_1449_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1451_;
v_a_1427_ = v___x_1474_;
v_a_1428_ = v_a_1459_;
goto v___jp_1419_;
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v___x_1475_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1476_ = lean_string_append(v___x_1414_, v___x_1475_);
v___x_1477_ = 3;
v___x_1478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*1, v___x_1477_);
v___x_1479_ = lean_array_get_size(v_a_1459_);
v___x_1480_ = lean_array_push(v_a_1459_, v___x_1478_);
v_a_1362_ = v___x_1479_;
v_a_1363_ = v___x_1480_;
goto v___jp_1361_;
}
}
else
{
lean_object* v_a_1481_; lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_a_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1481_ = lean_ctor_get(v___x_1457_, 0);
v_a_1482_ = lean_ctor_get(v___x_1457_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1457_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_inc(v_a_1481_);
lean_dec(v___x_1457_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
v___jp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; size_t v_sz_1495_; lean_object* v___x_1496_; 
v___x_1493_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1353_);
v___x_1494_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1493_, v_env_1353_);
v_sz_1495_ = lean_array_size(v___x_1494_);
lean_inc_ref(v___x_1414_);
lean_inc(v_a_1373_);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1373_, v___x_1414_, v_sz_1495_, v___x_1379_, v___x_1494_, v_a_1492_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
v_a_1498_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1496_, 2);
v___x_1499_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1353_);
v___x_1500_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1353_, v___x_1499_, v___f_1416_, v_a_1498_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; size_t v_sz_1505_; lean_object* v___x_1506_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1500_, 2);
v___x_1503_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1353_);
v___x_1504_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1503_, v_env_1353_);
v_sz_1505_ = lean_array_size(v___x_1504_);
lean_inc_ref(v___x_1414_);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1501_, v___x_1414_, v_sz_1505_, v___x_1379_, v___x_1504_, v_a_1502_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; size_t v_sz_1511_; lean_object* v___x_1512_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
v_a_1508_ = lean_ctor_get(v___x_1506_, 1);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1506_, 2);
v___x_1509_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1353_, 2);
v___x_1510_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1509_, v_env_1353_);
v_sz_1511_ = lean_array_size(v___x_1510_);
lean_inc(v_keyName_1375_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1353_, v_opts_1354_, v_keyName_1375_, v_sz_1511_, v___x_1379_, v___x_1510_, v_a_1508_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1570_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_a_1514_ = lean_ctor_get(v___x_1512_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1516_ = v___x_1512_;
v_isShared_1517_ = v_isSharedCheck_1570_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1570_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1518_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1353_, 2);
v___x_1519_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1518_, v_env_1353_);
v_sz_1520_ = lean_array_size(v___x_1519_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1353_, v_opts_1354_, v_sz_1520_, v___x_1379_, v___x_1519_);
v___x_1522_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; size_t v_sz_1526_; lean_object* v___x_1527_; 
lean_del_object(v___x_1516_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1353_);
v___x_1525_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1524_, v_env_1353_);
v_sz_1526_ = lean_array_size(v___x_1525_);
lean_inc_ref(v___x_1414_);
lean_inc(v_a_1373_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1373_, v_a_1501_, v___x_1414_, v_sz_1526_, v___x_1379_, v___x_1525_, v_a_1514_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
v_a_1529_ = lean_ctor_get(v___x_1527_, 1);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1527_, 2);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_array_get_size(v_a_1528_);
v___x_1532_ = lean_nat_dec_lt(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_nat_dec_lt(v___x_1418_, v___x_1531_);
if (v___x_1533_ == 0)
{
lean_object* v_testDriver_1534_; 
lean_dec(v_a_1528_);
v_testDriver_1534_ = lean_ctor_get(v_config_1376_, 12);
lean_inc_ref(v_testDriver_1534_);
v___y_1445_ = v___x_1530_;
v___y_1446_ = v_a_1497_;
v___y_1447_ = v___y_1491_;
v___y_1448_ = v_a_1501_;
v___y_1449_ = v_a_1523_;
v___y_1450_ = v_a_1507_;
v___y_1451_ = v_a_1513_;
v_a_1452_ = v_testDriver_1534_;
v_a_1453_ = v_a_1529_;
goto v___jp_1444_;
}
else
{
lean_object* v_testDriver_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_testDriver_1535_ = lean_ctor_get(v_config_1376_, 12);
v___x_1536_ = lean_string_utf8_byte_size(v_testDriver_1535_);
v___x_1537_ = lean_nat_dec_eq(v___x_1536_, v___x_1418_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v_a_1528_);
lean_dec(v_a_1523_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1501_);
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v___x_1538_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1539_ = lean_string_append(v___x_1414_, v___x_1538_);
v___x_1540_ = 3;
v___x_1541_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*1, v___x_1540_);
v___x_1542_ = lean_array_get_size(v_a_1529_);
v___x_1543_ = lean_array_push(v_a_1529_, v___x_1541_);
v_a_1358_ = v___x_1542_;
v_a_1359_ = v___x_1543_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_array_fget(v_a_1528_, v___x_1418_);
lean_dec(v_a_1528_);
v___x_1545_ = l_Lean_Name_toString(v___x_1544_, v___x_1537_);
v___y_1445_ = v___x_1530_;
v___y_1446_ = v_a_1497_;
v___y_1447_ = v___y_1491_;
v___y_1448_ = v_a_1501_;
v___y_1449_ = v_a_1523_;
v___y_1450_ = v_a_1507_;
v___y_1451_ = v_a_1513_;
v_a_1452_ = v___x_1545_;
v_a_1453_ = v_a_1529_;
goto v___jp_1444_;
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v_a_1528_);
lean_dec(v_a_1523_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1501_);
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v___x_1546_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1547_ = lean_string_append(v___x_1414_, v___x_1546_);
v___x_1548_ = 3;
v___x_1549_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*1, v___x_1548_);
v___x_1550_ = lean_array_get_size(v_a_1529_);
v___x_1551_ = lean_array_push(v_a_1529_, v___x_1549_);
v_a_1358_ = v___x_1550_;
v_a_1359_ = v___x_1551_;
goto v___jp_1357_;
}
}
else
{
lean_object* v_a_1552_; lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1523_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1501_);
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1552_ = lean_ctor_get(v___x_1527_, 0);
v_a_1553_ = lean_ctor_get(v___x_1527_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1527_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_inc(v_a_1552_);
lean_dec(v___x_1527_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1552_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1501_);
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1561_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1562_ = lean_io_error_to_string(v_a_1561_);
v___x_1563_ = 3;
v___x_1564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set_uint8(v___x_1564_, sizeof(void*)*1, v___x_1563_);
v___x_1565_ = lean_array_get_size(v_a_1514_);
v___x_1566_ = lean_array_push(v_a_1514_, v___x_1564_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 1);
lean_ctor_set(v___x_1516_, 1, v___x_1566_);
lean_ctor_set(v___x_1516_, 0, v___x_1565_);
v___x_1568_ = v___x_1516_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1566_);
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
lean_dec(v_a_1507_);
lean_dec(v_a_1501_);
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1571_ = lean_ctor_get(v___x_1512_, 0);
v_a_1572_ = lean_ctor_get(v___x_1512_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1512_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_inc(v_a_1571_);
lean_dec(v___x_1512_);
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
else
{
lean_object* v_a_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1501_);
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1580_ = lean_ctor_get(v___x_1506_, 0);
v_a_1581_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1506_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_inc(v_a_1580_);
lean_dec(v___x_1506_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_a_1497_);
lean_dec(v___y_1491_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1589_ = lean_ctor_get(v___x_1500_, 0);
v_a_1590_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1500_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_inc(v_a_1589_);
lean_dec(v___x_1500_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v___y_1491_);
lean_dec_ref(v___f_1416_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1598_ = lean_ctor_get(v___x_1496_, 0);
v_a_1599_ = lean_ctor_get(v___x_1496_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1496_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_inc(v_a_1598_);
lean_dec(v___x_1496_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
v___jp_1607_:
{
if (lean_obj_tag(v___y_1609_) == 0)
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___y_1609_, 1);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___y_1609_, 2);
v___y_1491_ = v___y_1608_;
v_a_1492_ = v_a_1610_;
goto v___jp_1490_;
}
else
{
lean_object* v_a_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v___y_1608_);
lean_dec_ref(v___f_1416_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1611_ = lean_ctor_get(v___y_1609_, 0);
v_a_1612_ = lean_ctor_get(v___y_1609_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___y_1609_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___y_1609_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_inc(v_a_1611_);
lean_dec(v___y_1609_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1611_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
v___jp_1621_:
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_lt(v___x_1418_, v___x_1620_);
if (v___x_1624_ == 0)
{
v___y_1491_ = v_a_1622_;
v_a_1492_ = v_a_1623_;
goto v___jp_1490_;
}
else
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_nat_dec_le(v___x_1620_, v___x_1620_);
if (v___x_1625_ == 0)
{
if (v___x_1624_ == 0)
{
v___y_1491_ = v_a_1622_;
v_a_1492_ = v_a_1623_;
goto v___jp_1490_;
}
else
{
size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_usize_of_nat(v___x_1620_);
lean_inc_ref(v___x_1414_);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1414_, v_a_1381_, v___x_1379_, v___x_1626_, v___x_1417_, v_a_1623_);
v___y_1608_ = v_a_1622_;
v___y_1609_ = v___x_1627_;
goto v___jp_1607_;
}
}
else
{
size_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_usize_of_nat(v___x_1620_);
lean_inc_ref(v___x_1414_);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1414_, v_a_1381_, v___x_1379_, v___x_1628_, v___x_1417_, v_a_1623_);
v___y_1608_ = v_a_1622_;
v___y_1609_ = v___x_1629_;
goto v___jp_1607_;
}
}
}
v___jp_1630_:
{
if (lean_obj_tag(v___y_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v_a_1633_; 
v_a_1632_ = lean_ctor_get(v___y_1631_, 0);
lean_inc(v_a_1632_);
v_a_1633_ = lean_ctor_get(v___y_1631_, 1);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___y_1631_, 2);
v_a_1622_ = v_a_1632_;
v_a_1623_ = v_a_1633_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v___f_1416_);
lean_dec_ref(v___x_1414_);
lean_del_object(v___x_1384_);
lean_dec(v_a_1381_);
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1634_ = lean_ctor_get(v___y_1631_, 0);
v_a_1635_ = lean_ctor_get(v___y_1631_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___y_1631_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___y_1631_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_inc(v_a_1634_);
lean_dec(v___y_1631_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1634_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_a_1373_);
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1650_ = lean_ctor_get(v___x_1380_, 0);
v_a_1651_ = lean_ctor_get(v___x_1380_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1380_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_inc(v_a_1650_);
lean_dec(v___x_1380_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1650_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1659_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1660_ = lean_io_error_to_string(v_a_1659_);
v___x_1661_ = 3;
v___x_1662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set_uint8(v___x_1662_, sizeof(void*)*1, v___x_1661_);
v___x_1663_ = lean_array_get_size(v_a_1355_);
v___x_1664_ = lean_array_push(v_a_1355_, v___x_1662_);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
return v___x_1665_;
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_env_1353_);
v_a_1666_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1667_ = lean_io_error_to_string(v_a_1666_);
v___x_1668_ = 3;
v___x_1669_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*1, v___x_1668_);
v___x_1670_ = lean_array_get_size(v_a_1355_);
v___x_1671_ = lean_array_push(v_a_1355_, v___x_1669_);
v___x_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
return v___x_1672_;
}
v___jp_1357_:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1358_);
lean_ctor_set(v___x_1360_, 1, v_a_1359_);
return v___x_1360_;
}
v___jp_1361_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1362_);
lean_ctor_set(v___x_1364_, 1, v_a_1363_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1673_, lean_object* v_opts_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1673_, v_opts_1674_, v_a_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1678_, lean_object* v_env_1679_, lean_object* v_attr_1680_, lean_object* v_f_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1679_, v_attr_1680_, v_f_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1683_, lean_object* v_env_1684_, lean_object* v_attr_1685_, lean_object* v_f_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1683_, v_env_1684_, v_attr_1685_, v_f_1686_);
lean_dec_ref(v_attr_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1688_, lean_object* v_inst_1689_, lean_object* v_t_1690_, lean_object* v_k_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_1690_, v_k_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1693_, lean_object* v_inst_1694_, lean_object* v_t_1695_, lean_object* v_k_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1693_, v_inst_1694_, v_t_1695_, v_k_1696_);
lean_dec(v_k_1696_);
lean_dec(v_t_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v_00_u03b2_1698_, lean_object* v_k_1699_, lean_object* v_v_1700_, lean_object* v_t_1701_, lean_object* v_hl_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1699_, v_v_1700_, v_t_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1704_, lean_object* v_t_1705_, lean_object* v_k_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1705_, v_k_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1708_, lean_object* v_t_1709_, lean_object* v_k_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1708_, v_t_1709_, v_k_1710_);
lean_dec(v_k_1710_);
lean_dec(v_t_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1712_, lean_object* v_env_1713_, lean_object* v_attr_1714_, lean_object* v_f_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1713_, v_attr_1714_, v_f_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1719_, lean_object* v_env_1720_, lean_object* v_attr_1721_, lean_object* v_f_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1719_, v_env_1720_, v_attr_1721_, v_f_1722_, v___y_1723_);
lean_dec_ref(v_attr_1721_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_1726_, lean_object* v___x_1727_, lean_object* v_as_1728_, size_t v_i_1729_, size_t v_stop_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1726_, v_as_1728_, v_i_1729_, v_stop_1730_, v_b_1731_, v___y_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_1735_, lean_object* v___x_1736_, lean_object* v_as_1737_, lean_object* v_i_1738_, lean_object* v_stop_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
size_t v_i_boxed_1743_; size_t v_stop_boxed_1744_; lean_object* v_res_1745_; 
v_i_boxed_1743_ = lean_unbox_usize(v_i_1738_);
lean_dec(v_i_1738_);
v_stop_boxed_1744_ = lean_unbox_usize(v_stop_1739_);
lean_dec(v_stop_1739_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1735_, v___x_1736_, v_as_1737_, v_i_boxed_1743_, v_stop_boxed_1744_, v_b_1740_, v___y_1741_);
lean_dec_ref(v_as_1737_);
lean_dec(v___x_1736_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(lean_object* v_00_u03b2_1746_, lean_object* v_f_1747_, lean_object* v_as_1748_, size_t v_i_1749_, size_t v_stop_1750_, lean_object* v_b_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_1747_, v_as_1748_, v_i_1749_, v_stop_1750_, v_b_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1753_, lean_object* v_f_1754_, lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_stop_1757_, lean_object* v_b_1758_){
_start:
{
size_t v_i_boxed_1759_; size_t v_stop_boxed_1760_; lean_object* v_res_1761_; 
v_i_boxed_1759_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_stop_boxed_1760_ = lean_unbox_usize(v_stop_1757_);
lean_dec(v_stop_1757_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(v_00_u03b2_1753_, v_f_1754_, v_as_1755_, v_i_boxed_1759_, v_stop_boxed_1760_, v_b_1758_);
lean_dec_ref(v_as_1755_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1762_, lean_object* v_f_1763_, lean_object* v_as_1764_, size_t v_i_1765_, size_t v_stop_1766_, lean_object* v_b_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1763_, v_as_1764_, v_i_1765_, v_stop_1766_, v_b_1767_, v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1771_, lean_object* v_f_1772_, lean_object* v_as_1773_, lean_object* v_i_1774_, lean_object* v_stop_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
size_t v_i_boxed_1779_; size_t v_stop_boxed_1780_; lean_object* v_res_1781_; 
v_i_boxed_1779_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_stop_boxed_1780_ = lean_unbox_usize(v_stop_1775_);
lean_dec(v_stop_1775_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1771_, v_f_1772_, v_as_1773_, v_i_boxed_1779_, v_stop_boxed_1780_, v_b_1776_, v___y_1777_);
lean_dec_ref(v_as_1773_);
return v_res_1781_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakefileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_AttributesCore(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
