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
lean_object* v___f_89_; uint8_t v___x_90_; 
lean_inc(v_toBind_81_);
lean_inc(v_toPure_82_);
v___f_89_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_89_, 0, v_toPure_82_);
lean_closure_set(v___f_89_, 1, v_f_79_);
lean_closure_set(v___f_89_, 2, v_toBind_81_);
v___x_90_ = lean_nat_dec_le(v___x_86_, v___x_86_);
if (v___x_90_ == 0)
{
if (v___x_87_ == 0)
{
lean_object* v___x_91_; 
lean_inc(v_toPure_82_);
lean_dec_ref(v___f_89_);
lean_dec_ref(v_entries_83_);
lean_dec_ref(v_inst_78_);
v___x_91_ = lean_apply_2(v_toPure_82_, lean_box(0), v___x_84_);
return v___x_91_;
}
else
{
size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_86_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_78_, v___f_89_, v_entries_83_, v___x_92_, v___x_93_, v___x_84_);
return v___x_94_;
}
}
else
{
size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((size_t)0ULL);
v___x_96_ = lean_usize_of_nat(v___x_86_);
v___x_97_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_78_, v___f_89_, v_entries_83_, v___x_95_, v___x_96_, v___x_84_);
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___boxed(lean_object* v_env_98_, lean_object* v_attr_99_, lean_object* v_inst_100_, lean_object* v_f_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(v_env_98_, v_attr_99_, v_inst_100_, v_f_101_);
lean_dec_ref(v_attr_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(lean_object* v_m_103_, lean_object* v_00_u03b2_104_, lean_object* v_env_105_, lean_object* v_attr_106_, lean_object* v_inst_107_, lean_object* v_f_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(v_env_105_, v_attr_106_, v_inst_107_, v_f_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___boxed(lean_object* v_m_110_, lean_object* v_00_u03b2_111_, lean_object* v_env_112_, lean_object* v_attr_113_, lean_object* v_inst_114_, lean_object* v_f_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(v_m_110_, v_00_u03b2_111_, v_env_112_, v_attr_113_, v_inst_114_, v_f_115_);
lean_dec_ref(v_attr_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0(lean_object* v_declName_117_, lean_object* v_map_118_, lean_object* v_toPure_119_, lean_object* v_____do__lift_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_117_, v_____do__lift_120_, v_map_118_);
v___x_122_ = lean_apply_2(v_toPure_119_, lean_box(0), v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1(lean_object* v_toPure_123_, lean_object* v_f_124_, lean_object* v_toBind_125_, lean_object* v_map_126_, lean_object* v_declName_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_inc(v_declName_127_);
v___f_128_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_128_, 0, v_declName_127_);
lean_closure_set(v___f_128_, 1, v_map_126_);
lean_closure_set(v___f_128_, 2, v_toPure_123_);
v___x_129_ = lean_apply_1(v_f_124_, v_declName_127_);
v___x_130_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v___x_129_, v___f_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(lean_object* v_env_131_, lean_object* v_attr_132_, lean_object* v_inst_133_, lean_object* v_f_134_){
_start:
{
lean_object* v_toApplicative_135_; lean_object* v_toBind_136_; lean_object* v_toPure_137_; lean_object* v_entries_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_toApplicative_135_ = lean_ctor_get(v_inst_133_, 0);
v_toBind_136_ = lean_ctor_get(v_inst_133_, 1);
v_toPure_137_ = lean_ctor_get(v_toApplicative_135_, 1);
v_entries_138_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_132_, v_env_131_);
v___x_139_ = lean_box(1);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_get_size(v_entries_138_);
v___x_142_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_inc(v_toPure_137_);
lean_dec_ref(v_entries_138_);
lean_dec(v_f_134_);
lean_dec_ref(v_inst_133_);
v___x_143_ = lean_apply_2(v_toPure_137_, lean_box(0), v___x_139_);
return v___x_143_;
}
else
{
lean_object* v___f_144_; uint8_t v___x_145_; 
lean_inc(v_toBind_136_);
lean_inc(v_toPure_137_);
v___f_144_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_144_, 0, v_toPure_137_);
lean_closure_set(v___f_144_, 1, v_f_134_);
lean_closure_set(v___f_144_, 2, v_toBind_136_);
v___x_145_ = lean_nat_dec_le(v___x_141_, v___x_141_);
if (v___x_145_ == 0)
{
if (v___x_142_ == 0)
{
lean_object* v___x_146_; 
lean_inc(v_toPure_137_);
lean_dec_ref(v___f_144_);
lean_dec_ref(v_entries_138_);
lean_dec_ref(v_inst_133_);
v___x_146_ = lean_apply_2(v_toPure_137_, lean_box(0), v___x_139_);
return v___x_146_;
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_141_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_133_, v___f_144_, v_entries_138_, v___x_147_, v___x_148_, v___x_139_);
return v___x_149_;
}
}
else
{
size_t v___x_150_; size_t v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_141_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_133_, v___f_144_, v_entries_138_, v___x_150_, v___x_151_, v___x_139_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___boxed(lean_object* v_env_153_, lean_object* v_attr_154_, lean_object* v_inst_155_, lean_object* v_f_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(v_env_153_, v_attr_154_, v_inst_155_, v_f_156_);
lean_dec_ref(v_attr_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(lean_object* v_m_158_, lean_object* v_00_u03b2_159_, lean_object* v_env_160_, lean_object* v_attr_161_, lean_object* v_inst_162_, lean_object* v_f_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(v_env_160_, v_attr_161_, v_inst_162_, v_f_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___boxed(lean_object* v_m_165_, lean_object* v_00_u03b2_166_, lean_object* v_env_167_, lean_object* v_attr_168_, lean_object* v_inst_169_, lean_object* v_f_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(v_m_165_, v_00_u03b2_166_, v_env_167_, v_attr_168_, v_inst_169_, v_f_170_);
lean_dec_ref(v_attr_168_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0(lean_object* v_map_172_, lean_object* v_declName_173_, lean_object* v_toPure_174_, lean_object* v_____do__lift_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
v___x_177_ = l_Lake_RBArray_insert___redArg(v___x_176_, v_map_172_, v_declName_173_, v_____do__lift_175_);
v___x_178_ = lean_apply_2(v_toPure_174_, lean_box(0), v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1(lean_object* v_toPure_179_, lean_object* v_f_180_, lean_object* v_toBind_181_, lean_object* v_map_182_, lean_object* v_declName_183_){
_start:
{
lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc(v_declName_183_);
v___f_184_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0), 4, 3);
lean_closure_set(v___f_184_, 0, v_map_182_);
lean_closure_set(v___f_184_, 1, v_declName_183_);
lean_closure_set(v___f_184_, 2, v_toPure_179_);
v___x_185_ = lean_apply_1(v_f_180_, v_declName_183_);
v___x_186_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v___x_185_, v___f_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(lean_object* v_env_187_, lean_object* v_attr_188_, lean_object* v_inst_189_, lean_object* v_f_190_){
_start:
{
lean_object* v_toApplicative_191_; lean_object* v_toBind_192_; lean_object* v_toPure_193_; lean_object* v_entries_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_toApplicative_191_ = lean_ctor_get(v_inst_189_, 0);
v_toBind_192_ = lean_ctor_get(v_inst_189_, 1);
v_toPure_193_ = lean_ctor_get(v_toApplicative_191_, 1);
v_entries_194_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_188_, v_env_187_);
v___x_195_ = lean_array_get_size(v_entries_194_);
v___x_196_ = l_Lake_RBArray_mkEmpty___redArg(v___x_195_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v___x_195_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_inc(v_toPure_193_);
lean_dec_ref(v_entries_194_);
lean_dec(v_f_190_);
lean_dec_ref(v_inst_189_);
v___x_199_ = lean_apply_2(v_toPure_193_, lean_box(0), v___x_196_);
return v___x_199_;
}
else
{
lean_object* v___f_200_; uint8_t v___x_201_; 
lean_inc(v_toBind_192_);
lean_inc(v_toPure_193_);
v___f_200_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1), 5, 3);
lean_closure_set(v___f_200_, 0, v_toPure_193_);
lean_closure_set(v___f_200_, 1, v_f_190_);
lean_closure_set(v___f_200_, 2, v_toBind_192_);
v___x_201_ = lean_nat_dec_le(v___x_195_, v___x_195_);
if (v___x_201_ == 0)
{
if (v___x_198_ == 0)
{
lean_object* v___x_202_; 
lean_inc(v_toPure_193_);
lean_dec_ref(v___f_200_);
lean_dec_ref(v_entries_194_);
lean_dec_ref(v_inst_189_);
v___x_202_ = lean_apply_2(v_toPure_193_, lean_box(0), v___x_196_);
return v___x_202_;
}
else
{
size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((size_t)0ULL);
v___x_204_ = lean_usize_of_nat(v___x_195_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_189_, v___f_200_, v_entries_194_, v___x_203_, v___x_204_, v___x_196_);
return v___x_205_;
}
}
else
{
size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; 
v___x_206_ = ((size_t)0ULL);
v___x_207_ = lean_usize_of_nat(v___x_195_);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_189_, v___f_200_, v_entries_194_, v___x_206_, v___x_207_, v___x_196_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___boxed(lean_object* v_env_209_, lean_object* v_attr_210_, lean_object* v_inst_211_, lean_object* v_f_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(v_env_209_, v_attr_210_, v_inst_211_, v_f_212_);
lean_dec_ref(v_attr_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(lean_object* v_m_214_, lean_object* v_00_u03b2_215_, lean_object* v_env_216_, lean_object* v_attr_217_, lean_object* v_inst_218_, lean_object* v_f_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(v_env_216_, v_attr_217_, v_inst_218_, v_f_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___boxed(lean_object* v_m_221_, lean_object* v_00_u03b2_222_, lean_object* v_env_223_, lean_object* v_attr_224_, lean_object* v_inst_225_, lean_object* v_f_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(v_m_221_, v_00_u03b2_222_, v_env_223_, v_attr_224_, v_inst_225_, v_f_226_);
lean_dec_ref(v_attr_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(lean_object* v_env_234_, lean_object* v_opts_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = l_Lake_packageAttr;
lean_inc_ref(v_env_234_);
v___x_237_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_236_, v_env_234_);
v___x_238_ = lean_array_to_list(v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; 
lean_dec_ref(v_env_234_);
v___x_239_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1));
return v___x_239_;
}
else
{
lean_object* v_tail_240_; 
v_tail_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc(v_tail_240_);
if (lean_obj_tag(v_tail_240_) == 0)
{
lean_object* v_head_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_head_241_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_head_241_);
lean_dec_ref_known(v___x_238_, 2);
v___x_242_ = l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
v___x_243_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_234_, v_opts_235_, v___x_242_, v_head_241_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
lean_dec_ref_known(v___x_238_, 2);
lean_dec(v_tail_240_);
lean_dec_ref(v_env_234_);
v___x_244_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3));
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___boxed(lean_object* v_env_245_, lean_object* v_opts_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_245_, v_opts_246_);
lean_dec_ref(v_opts_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(lean_object* v_e_248_){
_start:
{
if (lean_obj_tag(v_e_248_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_258_; 
v_a_250_ = lean_ctor_get(v_e_248_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_e_248_);
if (v_isSharedCheck_258_ == 0)
{
v___x_252_ = v_e_248_;
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v_e_248_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_mk_io_user_error(v_a_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 1);
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_a_259_ = lean_ctor_get(v_e_248_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_e_248_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v_e_248_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v_e_248_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 0);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg___boxed(lean_object* v_e_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(lean_object* v_00_u03b1_270_, lean_object* v_e_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___boxed(lean_object* v_00_u03b1_274_, lean_object* v_e_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(v_00_u03b1_274_, v_e_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0(lean_object* v_env_278_, lean_object* v_opts_279_, lean_object* v___x_280_, lean_object* v_name_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_278_, v_opts_279_, v___x_280_, v_name_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed(lean_object* v_env_283_, lean_object* v_opts_284_, lean_object* v___x_285_, lean_object* v_name_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lake_LakefileConfig_loadFromEnv___lam__0(v_env_283_, v_opts_284_, v___x_285_, v_name_286_);
lean_dec_ref(v_opts_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1(uint8_t v___x_289_, lean_object* v_env_290_, lean_object* v_opts_291_, lean_object* v___x_292_, lean_object* v___x_293_, lean_object* v_scriptName_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc_n(v_scriptName_294_, 2);
v___x_297_ = l_Lean_Name_toString(v_scriptName_294_, v___x_289_);
lean_inc_ref(v_env_290_);
v___x_298_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_290_, v_opts_291_, v___x_292_, v_scriptName_294_);
v___x_299_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = 1;
v___x_302_ = l_Lean_Options_empty;
v___x_303_ = lean_box(0);
v___x_304_ = lean_box(0);
v___x_305_ = l_Lean_findDocString_x3f(v_env_290_, v_scriptName_294_, v___x_301_, v___x_302_, v___x_303_, v___x_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0));
v___x_308_ = lean_string_append(v___x_293_, v___x_307_);
v___x_309_ = lean_string_append(v___x_308_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_a_300_);
lean_ctor_set(v___x_310_, 2, v_a_306_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___y_295_);
return v___x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_a_300_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_293_);
v_a_312_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_305_, 1);
v___x_313_ = lean_io_error_to_string(v_a_312_);
v___x_314_ = 3;
v___x_315_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*1, v___x_314_);
v___x_316_ = lean_array_get_size(v___y_295_);
v___x_317_ = lean_array_push(v___y_295_, v___x_315_);
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
return v___x_318_;
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref(v___x_297_);
lean_dec(v_scriptName_294_);
lean_dec_ref(v___x_293_);
lean_dec_ref(v_env_290_);
v_a_319_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_299_, 1);
v___x_320_ = lean_io_error_to_string(v_a_319_);
v___x_321_ = 3;
v___x_322_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_321_);
v___x_323_ = lean_array_get_size(v___y_295_);
v___x_324_ = lean_array_push(v___y_295_, v___x_322_);
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object* v___x_326_, lean_object* v_env_327_, lean_object* v_opts_328_, lean_object* v___x_329_, lean_object* v___x_330_, lean_object* v_scriptName_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
uint8_t v___x_51094__boxed_334_; lean_object* v_res_335_; 
v___x_51094__boxed_334_ = lean_unbox(v___x_326_);
v_res_335_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_51094__boxed_334_, v_env_327_, v_opts_328_, v___x_329_, v___x_330_, v_scriptName_331_, v___y_332_);
lean_dec_ref(v_opts_328_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object* v_env_338_, lean_object* v_opts_339_, lean_object* v___x_340_, size_t v_sz_341_, size_t v_i_342_, lean_object* v_bs_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_a_347_; lean_object* v_a_348_; uint8_t v___x_350_; 
v___x_350_ = lean_usize_dec_lt(v_i_342_, v_sz_341_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec(v___x_340_);
lean_dec_ref(v_env_338_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_bs_343_);
lean_ctor_set(v___x_351_, 1, v___y_344_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v_v_353_; lean_object* v___x_354_; 
v___x_352_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_353_ = lean_array_uget_borrowed(v_bs_343_, v_i_342_);
lean_inc(v_v_353_);
lean_inc_ref(v_env_338_);
v___x_354_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_338_, v_opts_339_, v___x_352_, v_v_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec_ref(v_bs_343_);
lean_dec(v___x_340_);
lean_dec_ref(v_env_338_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = 3;
v___x_357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_357_, 0, v_a_355_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1, v___x_356_);
v___x_358_ = lean_array_get_size(v___y_344_);
v___x_359_ = lean_array_push(v___y_344_, v___x_357_);
v_a_347_ = v___x_358_;
v_a_348_ = v___x_359_;
goto v___jp_346_;
}
else
{
lean_object* v_a_360_; lean_object* v_pkg_361_; lean_object* v_fn_362_; uint8_t v___x_363_; 
v_a_360_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_354_, 1);
v_pkg_361_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_pkg_361_);
v_fn_362_ = lean_ctor_get(v_a_360_, 1);
lean_inc_ref(v_fn_362_);
lean_dec(v_a_360_);
v___x_363_ = lean_name_eq(v_pkg_361_, v___x_340_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v_fn_362_);
lean_dec_ref(v_bs_343_);
lean_dec_ref(v_env_338_);
v___x_364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0));
v___x_365_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_361_, v___x_350_);
v___x_366_ = lean_string_append(v___x_364_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
v___x_369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_340_, v___x_350_);
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
lean_dec_ref(v___x_369_);
v___x_371_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
v___x_373_ = 3;
v___x_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_373_);
v___x_375_ = lean_array_get_size(v___y_344_);
v___x_376_ = lean_array_push(v___y_344_, v___x_374_);
v_a_347_ = v___x_375_;
v_a_348_ = v___x_376_;
goto v___jp_346_;
}
else
{
lean_object* v___x_377_; lean_object* v_bs_x27_378_; size_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; 
lean_dec(v_pkg_361_);
v___x_377_ = lean_unsigned_to_nat(0u);
v_bs_x27_378_ = lean_array_uset(v_bs_343_, v_i_342_, v___x_377_);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_342_, v___x_379_);
v___x_381_ = lean_array_uset(v_bs_x27_378_, v_i_342_, v_fn_362_);
v_i_342_ = v___x_380_;
v_bs_343_ = v___x_381_;
goto _start;
}
}
}
v___jp_346_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v_a_347_);
lean_ctor_set(v___x_349_, 1, v_a_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object* v_env_383_, lean_object* v_opts_384_, lean_object* v___x_385_, lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_bs_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_392_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_383_, v_opts_384_, v___x_385_, v_sz_boxed_391_, v_i_boxed_392_, v_bs_388_, v___y_389_);
lean_dec_ref(v_opts_384_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object* v___x_397_, size_t v_sz_398_, size_t v_i_399_, lean_object* v_bs_400_, lean_object* v___y_401_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_lt(v_i_399_, v_sz_398_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
lean_dec(v___x_397_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_bs_400_);
lean_ctor_set(v___x_404_, 1, v___y_401_);
return v___x_404_;
}
else
{
lean_object* v_v_405_; lean_object* v_pkg_406_; lean_object* v_name_407_; uint8_t v___x_408_; 
v_v_405_ = lean_array_uget(v_bs_400_, v_i_399_);
v_pkg_406_ = lean_ctor_get(v_v_405_, 0);
v_name_407_ = lean_ctor_get(v_v_405_, 1);
v___x_408_ = lean_name_eq(v_pkg_406_, v___x_397_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc(v_name_407_);
lean_inc(v_pkg_406_);
lean_dec(v_v_405_);
lean_dec_ref(v_bs_400_);
v___x_409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0));
v___x_410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_407_, v___x_403_);
v___x_411_ = lean_string_append(v___x_409_, v___x_410_);
lean_dec_ref(v___x_410_);
v___x_412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
v___x_414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_406_, v___x_403_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_397_, v___x_403_);
v___x_419_ = lean_string_append(v___x_417_, v___x_418_);
lean_dec_ref(v___x_418_);
v___x_420_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = 3;
v___x_423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_422_);
v___x_424_ = lean_array_get_size(v___y_401_);
v___x_425_ = lean_array_push(v___y_401_, v___x_423_);
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v_bs_x27_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v_bs_x27_428_ = lean_array_uset(v_bs_400_, v_i_399_, v___x_427_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_add(v_i_399_, v___x_429_);
v___x_431_ = lean_array_uset(v_bs_x27_428_, v_i_399_, v_v_405_);
v_i_399_ = v___x_430_;
v_bs_400_ = v___x_431_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___boxed(lean_object* v___x_433_, lean_object* v_sz_434_, lean_object* v_i_435_, lean_object* v_bs_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
size_t v_sz_boxed_439_; size_t v_i_boxed_440_; lean_object* v_res_441_; 
v_sz_boxed_439_ = lean_unbox_usize(v_sz_434_);
lean_dec(v_sz_434_);
v_i_boxed_440_ = lean_unbox_usize(v_i_435_);
lean_dec(v_i_435_);
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v___x_433_, v_sz_boxed_439_, v_i_boxed_440_, v_bs_436_, v___y_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object* v_t_442_, lean_object* v_k_443_){
_start:
{
if (lean_obj_tag(v_t_442_) == 0)
{
lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v_l_446_; lean_object* v_r_447_; uint8_t v___x_448_; 
v_k_444_ = lean_ctor_get(v_t_442_, 1);
v_v_445_ = lean_ctor_get(v_t_442_, 2);
v_l_446_ = lean_ctor_get(v_t_442_, 3);
v_r_447_ = lean_ctor_get(v_t_442_, 4);
v___x_448_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_443_, v_k_444_);
switch(v___x_448_)
{
case 0:
{
v_t_442_ = v_l_446_;
goto _start;
}
case 1:
{
lean_object* v___x_450_; 
lean_inc(v_v_445_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_v_445_);
return v___x_450_;
}
default: 
{
v_t_442_ = v_r_447_;
goto _start;
}
}
}
else
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_453_, lean_object* v_k_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_453_, v_k_454_);
lean_dec(v_k_454_);
lean_dec(v_t_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object* v_a_458_, lean_object* v___x_459_, size_t v_sz_460_, size_t v_i_461_, lean_object* v_bs_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_lt(v_i_461_, v_sz_460_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec_ref(v___x_459_);
lean_dec_ref(v_a_458_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_bs_462_);
lean_ctor_set(v___x_466_, 1, v___y_463_);
return v___x_466_;
}
else
{
lean_object* v_toTreeMap_467_; lean_object* v_v_468_; lean_object* v___x_469_; 
v_toTreeMap_467_ = lean_ctor_get(v_a_458_, 0);
v_v_468_ = lean_array_uget_borrowed(v_bs_462_, v_i_461_);
v___x_469_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_467_, v_v_468_);
if (lean_obj_tag(v___x_469_) == 1)
{
lean_object* v_val_470_; lean_object* v_name_471_; lean_object* v___x_472_; lean_object* v_bs_x27_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v_val_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___x_469_, 1);
v_name_471_ = lean_ctor_get(v_val_470_, 1);
lean_inc(v_name_471_);
lean_dec(v_val_470_);
v___x_472_ = lean_unsigned_to_nat(0u);
v_bs_x27_473_ = lean_array_uset(v_bs_462_, v_i_461_, v___x_472_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_461_, v___x_474_);
v___x_476_ = lean_array_uset(v_bs_x27_473_, v_i_461_, v_name_471_);
v_i_461_ = v___x_475_;
v_bs_462_ = v___x_476_;
goto _start;
}
else
{
lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_494_; 
lean_inc(v_v_468_);
lean_dec(v___x_469_);
lean_dec_ref(v_bs_462_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_458_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_495_ = lean_ctor_get(v_a_458_, 1);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_a_458_, 0);
lean_dec(v_unused_496_);
v___x_479_ = v_a_458_;
v_isShared_480_ = v_isSharedCheck_494_;
goto v_resetjp_478_;
}
else
{
lean_dec(v_a_458_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_494_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0));
v___x_482_ = lean_string_append(v___x_459_, v___x_481_);
v___x_483_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_468_, v___x_465_);
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___x_487_ = 3;
v___x_488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*1, v___x_487_);
v___x_489_ = lean_array_get_size(v___y_463_);
v___x_490_ = lean_array_push(v___y_463_, v___x_488_);
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 1);
lean_ctor_set(v___x_479_, 1, v___x_490_);
lean_ctor_set(v___x_479_, 0, v___x_489_);
v___x_492_ = v___x_479_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object* v_a_497_, lean_object* v___x_498_, lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_bs_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_505_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_497_, v___x_498_, v_sz_boxed_504_, v_i_boxed_505_, v_bs_501_, v___y_502_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(lean_object* v_f_507_, lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_, lean_object* v_b_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_array_uget_borrowed(v_as_508_, v_i_509_);
lean_inc_ref(v_f_507_);
lean_inc(v___x_513_);
v___x_514_ = lean_apply_1(v_f_507_, v___x_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_b_511_);
lean_dec_ref(v_f_507_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; size_t v___x_526_; size_t v___x_527_; 
v_a_523_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_514_, 1);
v___x_524_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_513_);
v___x_525_ = l_Lake_RBArray_insert___redArg(v___x_524_, v_b_511_, v___x_513_, v_a_523_);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_509_, v___x_526_);
v_i_509_ = v___x_527_;
v_b_511_ = v___x_525_;
goto _start;
}
}
else
{
lean_object* v___x_529_; 
lean_dec_ref(v_f_507_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_b_511_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_530_, lean_object* v_as_531_, lean_object* v_i_532_, lean_object* v_stop_533_, lean_object* v_b_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_533_);
lean_dec(v_stop_533_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_530_, v_as_531_, v_i_boxed_535_, v_stop_boxed_536_, v_b_534_);
lean_dec_ref(v_as_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object* v_env_538_, lean_object* v_attr_539_, lean_object* v_f_540_){
_start:
{
lean_object* v_entries_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_entries_541_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_539_, v_env_538_);
v___x_542_ = lean_array_get_size(v_entries_541_);
v___x_543_ = l_Lake_RBArray_mkEmpty___redArg(v___x_542_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_nat_dec_lt(v___x_544_, v___x_542_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec_ref(v_entries_541_);
lean_dec_ref(v_f_540_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_543_);
return v___x_546_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = lean_nat_dec_le(v___x_542_, v___x_542_);
if (v___x_547_ == 0)
{
if (v___x_545_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v_entries_541_);
lean_dec_ref(v_f_540_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_543_);
return v___x_548_;
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_542_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_540_, v_entries_541_, v___x_549_, v___x_550_, v___x_543_);
lean_dec_ref(v_entries_541_);
return v___x_551_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_542_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_540_, v_entries_541_, v___x_552_, v___x_553_, v___x_543_);
lean_dec_ref(v_entries_541_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_env_555_, lean_object* v_attr_556_, lean_object* v_f_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_555_, v_attr_556_, v_f_557_);
lean_dec_ref(v_attr_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_559_, lean_object* v_as_560_, size_t v_i_561_, size_t v_stop_562_, lean_object* v_b_563_, lean_object* v___y_564_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_eq(v_i_561_, v_stop_562_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_array_uget_borrowed(v_as_560_, v_i_561_);
lean_inc_ref(v_f_559_);
lean_inc(v___x_567_);
v___x_568_ = lean_apply_3(v_f_559_, v___x_567_, v___y_564_, lean_box(0));
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_571_; size_t v___x_572_; size_t v___x_573_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
v_a_570_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_568_, 2);
lean_inc(v___x_567_);
v___x_571_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_567_, v_a_569_, v_b_563_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_561_, v___x_572_);
v_i_561_ = v___x_573_;
v_b_563_ = v___x_571_;
v___y_564_ = v_a_570_;
goto _start;
}
else
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_b_563_);
lean_dec_ref(v_f_559_);
v_a_575_ = lean_ctor_get(v___x_568_, 0);
v_a_576_ = lean_ctor_get(v___x_568_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_568_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_inc(v_a_575_);
lean_dec(v___x_568_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_575_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v___x_584_; 
lean_dec_ref(v_f_559_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_b_563_);
lean_ctor_set(v___x_584_, 1, v___y_564_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_585_, lean_object* v_as_586_, lean_object* v_i_587_, lean_object* v_stop_588_, lean_object* v_b_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
size_t v_i_boxed_592_; size_t v_stop_boxed_593_; lean_object* v_res_594_; 
v_i_boxed_592_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_stop_boxed_593_ = lean_unbox_usize(v_stop_588_);
lean_dec(v_stop_588_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_585_, v_as_586_, v_i_boxed_592_, v_stop_boxed_593_, v_b_589_, v___y_590_);
lean_dec_ref(v_as_586_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_595_, lean_object* v_attr_596_, lean_object* v_f_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_entries_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_entries_600_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_596_, v_env_595_);
v___x_601_ = lean_box(1);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_array_get_size(v_entries_600_);
v___x_604_ = lean_nat_dec_lt(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_entries_600_);
lean_dec_ref(v_f_597_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_601_);
lean_ctor_set(v___x_605_, 1, v___y_598_);
return v___x_605_;
}
else
{
uint8_t v___x_606_; 
v___x_606_ = lean_nat_dec_le(v___x_603_, v___x_603_);
if (v___x_606_ == 0)
{
if (v___x_604_ == 0)
{
lean_object* v___x_607_; 
lean_dec_ref(v_entries_600_);
lean_dec_ref(v_f_597_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_601_);
lean_ctor_set(v___x_607_, 1, v___y_598_);
return v___x_607_;
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_603_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_597_, v_entries_600_, v___x_608_, v___x_609_, v___x_601_, v___y_598_);
lean_dec_ref(v_entries_600_);
return v___x_610_;
}
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_603_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_597_, v_entries_600_, v___x_611_, v___x_612_, v___x_601_, v___y_598_);
lean_dec_ref(v_entries_600_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_614_, lean_object* v_attr_615_, lean_object* v_f_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_614_, v_attr_615_, v_f_616_, v___y_617_);
lean_dec_ref(v_attr_615_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_620_, lean_object* v_opts_621_, lean_object* v_as_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_b_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v_env_620_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_625_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v_a_629_; lean_object* v___x_630_; 
v___x_628_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
v_a_629_ = lean_array_uget_borrowed(v_as_622_, v_i_624_);
lean_inc(v_a_629_);
lean_inc_ref(v_env_620_);
v___x_630_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_620_, v_opts_621_, v___x_628_, v_a_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_b_625_);
lean_dec_ref(v_env_620_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v_name_640_; lean_object* v_config_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_652_; 
v_a_639_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_630_, 1);
v_name_640_ = lean_ctor_get(v_a_639_, 0);
v_config_641_ = lean_ctor_get(v_a_639_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_652_ == 0)
{
v___x_643_ = v_a_639_;
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_config_641_);
lean_inc(v_name_640_);
lean_dec(v_a_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_name_640_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_config_641_);
v___x_646_ = v_reuseFailAlloc_651_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; 
v___x_647_ = lean_array_push(v_b_625_, v___x_646_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_624_, v___x_648_);
v_i_624_ = v___x_649_;
v_b_625_ = v___x_647_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object* v_env_653_, lean_object* v_opts_654_, lean_object* v_as_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_b_658_){
_start:
{
size_t v_sz_boxed_659_; size_t v_i_boxed_660_; lean_object* v_res_661_; 
v_sz_boxed_659_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_660_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_653_, v_opts_654_, v_as_655_, v_sz_boxed_659_, v_i_boxed_660_, v_b_658_);
lean_dec_ref(v_as_655_);
lean_dec_ref(v_opts_654_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v___x_665_, lean_object* v_as_666_, size_t v_i_667_, size_t v_stop_668_, lean_object* v_b_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_a_673_; lean_object* v_a_674_; uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_eq(v_i_667_, v_stop_668_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v_name_680_; lean_object* v_kind_681_; lean_object* v_config_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_679_ = lean_array_uget_borrowed(v_as_666_, v_i_667_);
v_name_680_ = lean_ctor_get(v___x_679_, 1);
v_kind_681_ = lean_ctor_get(v___x_679_, 2);
v_config_682_ = lean_ctor_get(v___x_679_, 3);
v___x_683_ = l_Lake_LeanExe_keyword;
v___x_684_ = lean_name_eq(v_kind_681_, v___x_683_);
if (v___x_684_ == 0)
{
v_a_673_ = v_b_669_;
v_a_674_ = v___y_670_;
goto v___jp_672_;
}
else
{
lean_object* v_root_685_; lean_object* v___x_686_; 
v_root_685_ = lean_ctor_get(v_config_682_, 2);
v___x_686_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_669_, v_root_685_);
if (lean_obj_tag(v___x_686_) == 1)
{
lean_object* v_val_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_b_669_);
v_val_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0));
v___x_689_ = lean_string_append(v___x_665_, v___x_688_);
lean_inc(v_name_680_);
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_680_, v___x_684_);
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
lean_dec_ref(v___x_690_);
v___x_692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1));
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
lean_inc(v_root_685_);
v___x_694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_685_, v___x_684_);
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
lean_dec_ref(v___x_694_);
v___x_696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2));
v___x_697_ = lean_string_append(v___x_695_, v___x_696_);
v___x_698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_687_, v___x_684_);
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v___x_702_ = 3;
v___x_703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v___x_702_);
v___x_704_ = lean_array_get_size(v___y_670_);
v___x_705_ = lean_array_push(v___y_670_, v___x_703_);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; 
lean_dec(v___x_686_);
lean_inc(v_name_680_);
lean_inc(v_root_685_);
v___x_707_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_685_, v_name_680_, v_b_669_);
v_a_673_ = v___x_707_;
v_a_674_ = v___y_670_;
goto v___jp_672_;
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec_ref(v___x_665_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_b_669_);
lean_ctor_set(v___x_708_, 1, v___y_670_);
return v___x_708_;
}
v___jp_672_:
{
size_t v___x_675_; size_t v___x_676_; 
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_667_, v___x_675_);
v_i_667_ = v___x_676_;
v_b_669_ = v_a_673_;
v___y_670_ = v_a_674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v___x_709_, lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
size_t v_i_boxed_716_; size_t v_stop_boxed_717_; lean_object* v_res_718_; 
v_i_boxed_716_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_717_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_709_, v_as_710_, v_i_boxed_716_, v_stop_boxed_717_, v_b_713_, v___y_714_);
lean_dec_ref(v_as_710_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v___x_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_bs_726_, lean_object* v___y_727_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = lean_usize_dec_lt(v_i_725_, v_sz_724_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec_ref(v___x_723_);
lean_dec_ref(v_a_721_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_bs_726_);
lean_ctor_set(v___x_730_, 1, v___y_727_);
return v___x_730_;
}
else
{
lean_object* v_toTreeMap_731_; lean_object* v_v_732_; lean_object* v___x_733_; lean_object* v_bs_x27_734_; lean_object* v_a_736_; lean_object* v_a_737_; lean_object* v___x_742_; 
v_toTreeMap_731_ = lean_ctor_get(v_a_721_, 0);
v_v_732_ = lean_array_uget(v_bs_726_, v_i_725_);
v___x_733_ = lean_unsigned_to_nat(0u);
v_bs_x27_734_ = lean_array_uset(v_bs_726_, v_i_725_, v___x_733_);
v___x_742_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_731_, v_v_732_);
if (lean_obj_tag(v___x_742_) == 1)
{
lean_object* v_val_743_; lean_object* v_name_744_; 
lean_dec(v_v_732_);
v_val_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v___x_742_, 1);
v_name_744_ = lean_ctor_get(v_val_743_, 1);
lean_inc(v_name_744_);
lean_dec(v_val_743_);
v_a_736_ = v_name_744_;
v_a_737_ = v___y_727_;
goto v___jp_735_;
}
else
{
uint8_t v___x_745_; 
lean_dec(v___x_742_);
v___x_745_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_732_, v_a_722_);
if (v___x_745_ == 0)
{
lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_762_; 
lean_dec_ref(v_bs_x27_734_);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_721_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_763_ = lean_ctor_get(v_a_721_, 1);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_a_721_, 0);
lean_dec(v_unused_764_);
v___x_747_ = v_a_721_;
v_isShared_748_ = v_isSharedCheck_762_;
goto v_resetjp_746_;
}
else
{
lean_dec(v_a_721_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_762_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_750_ = lean_string_append(v___x_723_, v___x_749_);
v___x_751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_732_, v___x_729_);
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
lean_dec_ref(v___x_751_);
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
v___x_755_ = 3;
v___x_756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*1, v___x_755_);
v___x_757_ = lean_array_get_size(v___y_727_);
v___x_758_ = lean_array_push(v___y_727_, v___x_756_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 1);
lean_ctor_set(v___x_747_, 1, v___x_758_);
lean_ctor_set(v___x_747_, 0, v___x_757_);
v___x_760_ = v___x_747_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
v_a_736_ = v_v_732_;
v_a_737_ = v___y_727_;
goto v___jp_735_;
}
}
v___jp_735_:
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_add(v_i_725_, v___x_738_);
v___x_740_ = lean_array_uset(v_bs_x27_734_, v_i_725_, v_a_736_);
v_i_725_ = v___x_739_;
v_bs_726_ = v___x_740_;
v___y_727_ = v_a_737_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v___x_767_, lean_object* v_sz_768_, lean_object* v_i_769_, lean_object* v_bs_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
size_t v_sz_boxed_773_; size_t v_i_boxed_774_; lean_object* v_res_775_; 
v_sz_boxed_773_ = lean_unbox_usize(v_sz_768_);
lean_dec(v_sz_768_);
v_i_boxed_774_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_765_, v_a_766_, v___x_767_, v_sz_boxed_773_, v_i_boxed_774_, v_bs_770_, v___y_771_);
lean_dec(v_a_766_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v___x_779_, size_t v_sz_780_, size_t v_i_781_, lean_object* v_bs_782_, lean_object* v___y_783_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = lean_usize_dec_lt(v_i_781_, v_sz_780_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_779_);
lean_dec_ref(v_a_777_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_bs_782_);
lean_ctor_set(v___x_786_, 1, v___y_783_);
return v___x_786_;
}
else
{
lean_object* v_toTreeMap_787_; lean_object* v_v_788_; lean_object* v___x_789_; lean_object* v_bs_x27_790_; lean_object* v_a_792_; lean_object* v_a_793_; lean_object* v___x_798_; 
v_toTreeMap_787_ = lean_ctor_get(v_a_777_, 0);
v_v_788_ = lean_array_uget(v_bs_782_, v_i_781_);
v___x_789_ = lean_unsigned_to_nat(0u);
v_bs_x27_790_ = lean_array_uset(v_bs_782_, v_i_781_, v___x_789_);
v___x_798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_787_, v_v_788_);
if (lean_obj_tag(v___x_798_) == 1)
{
lean_object* v_val_799_; lean_object* v_name_800_; 
lean_dec(v_v_788_);
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_798_, 1);
v_name_800_ = lean_ctor_get(v_val_799_, 1);
lean_inc(v_name_800_);
lean_dec(v_val_799_);
v_a_792_ = v_name_800_;
v_a_793_ = v___y_783_;
goto v___jp_791_;
}
else
{
uint8_t v___x_801_; 
lean_dec(v___x_798_);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_788_, v_a_778_);
if (v___x_801_ == 0)
{
lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_bs_x27_790_);
v_isSharedCheck_818_ = !lean_is_exclusive(v_a_777_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_819_ = lean_ctor_get(v_a_777_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_a_777_, 0);
lean_dec(v_unused_820_);
v___x_803_ = v_a_777_;
v_isShared_804_ = v_isSharedCheck_818_;
goto v_resetjp_802_;
}
else
{
lean_dec(v_a_777_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_818_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_806_ = lean_string_append(v___x_779_, v___x_805_);
v___x_807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_788_, v___x_785_);
v___x_808_ = lean_string_append(v___x_806_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0));
v___x_810_ = lean_string_append(v___x_808_, v___x_809_);
v___x_811_ = 3;
v___x_812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*1, v___x_811_);
v___x_813_ = lean_array_get_size(v___y_783_);
v___x_814_ = lean_array_push(v___y_783_, v___x_812_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 1);
lean_ctor_set(v___x_803_, 1, v___x_814_);
lean_ctor_set(v___x_803_, 0, v___x_813_);
v___x_816_ = v___x_803_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
v_a_792_ = v_v_788_;
v_a_793_ = v___y_783_;
goto v___jp_791_;
}
}
v___jp_791_:
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_781_, v___x_794_);
v___x_796_ = lean_array_uset(v_bs_x27_790_, v_i_781_, v_a_792_);
v_i_781_ = v___x_795_;
v_bs_782_ = v___x_796_;
v___y_783_ = v_a_793_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v___x_823_, lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_bs_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
size_t v_sz_boxed_829_; size_t v_i_boxed_830_; lean_object* v_res_831_; 
v_sz_boxed_829_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_830_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_821_, v_a_822_, v___x_823_, v_sz_boxed_829_, v_i_boxed_830_, v_bs_826_, v___y_827_);
lean_dec(v_a_822_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_833_, lean_object* v___x_834_, size_t v_sz_835_, size_t v_i_836_, lean_object* v_bs_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_lt(v_i_836_, v_sz_835_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec_ref(v___x_834_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_bs_837_);
lean_ctor_set(v___x_841_, 1, v___y_838_);
return v___x_841_;
}
else
{
lean_object* v_v_842_; lean_object* v___x_843_; 
v_v_842_ = lean_array_uget_borrowed(v_bs_837_, v_i_836_);
v___x_843_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_833_, v_v_842_);
if (lean_obj_tag(v___x_843_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_845_; lean_object* v_bs_x27_846_; size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
v_val_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = lean_unsigned_to_nat(0u);
v_bs_x27_846_ = lean_array_uset(v_bs_837_, v_i_836_, v___x_845_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_836_, v___x_847_);
v___x_849_ = lean_array_uset(v_bs_x27_846_, v_i_836_, v_val_844_);
v_i_836_ = v___x_848_;
v_bs_837_ = v___x_849_;
goto _start;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc(v_v_842_);
lean_dec(v___x_843_);
lean_dec_ref(v_bs_837_);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_852_ = lean_string_append(v___x_834_, v___x_851_);
v___x_853_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_842_, v___x_840_);
v___x_854_ = lean_string_append(v___x_852_, v___x_853_);
lean_dec_ref(v___x_853_);
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_856_ = lean_string_append(v___x_854_, v___x_855_);
v___x_857_ = 3;
v___x_858_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*1, v___x_857_);
v___x_859_ = lean_array_get_size(v___y_838_);
v___x_860_ = lean_array_push(v___y_838_, v___x_858_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_862_, lean_object* v___x_863_, lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_bs_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
size_t v_sz_boxed_869_; size_t v_i_boxed_870_; lean_object* v_res_871_; 
v_sz_boxed_869_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_870_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_862_, v___x_863_, v_sz_boxed_869_, v_i_boxed_870_, v_bs_866_, v___y_867_);
lean_dec(v_a_862_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_872_, lean_object* v_opts_873_, size_t v_sz_874_, size_t v_i_875_, lean_object* v_bs_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_lt(v_i_875_, v_sz_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec_ref(v_env_872_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_bs_876_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; lean_object* v_v_880_; lean_object* v___x_881_; 
v___x_879_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_;
v_v_880_ = lean_array_uget_borrowed(v_bs_876_, v_i_875_);
lean_inc(v_v_880_);
lean_inc_ref(v_env_872_);
v___x_881_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_872_, v_opts_873_, v___x_879_, v_v_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_bs_876_);
lean_dec_ref(v_env_872_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v_bs_x27_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v_a_890_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_881_, 1);
v___x_891_ = lean_unsigned_to_nat(0u);
v_bs_x27_892_ = lean_array_uset(v_bs_876_, v_i_875_, v___x_891_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_add(v_i_875_, v___x_893_);
v___x_895_ = lean_array_uset(v_bs_x27_892_, v_i_875_, v_a_890_);
v_i_875_ = v___x_894_;
v_bs_876_ = v___x_895_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_897_, lean_object* v_opts_898_, lean_object* v_sz_899_, lean_object* v_i_900_, lean_object* v_bs_901_){
_start:
{
size_t v_sz_boxed_902_; size_t v_i_boxed_903_; lean_object* v_res_904_; 
v_sz_boxed_902_ = lean_unbox_usize(v_sz_899_);
lean_dec(v_sz_899_);
v_i_boxed_903_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_897_, v_opts_898_, v_sz_boxed_902_, v_i_boxed_903_, v_bs_901_);
lean_dec_ref(v_opts_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_905_, lean_object* v_opts_906_, lean_object* v_as_907_, size_t v_sz_908_, size_t v_i_909_, lean_object* v_b_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_909_, v_sz_908_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_dec_ref(v_env_905_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_b_910_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_915_; 
v___x_913_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
v_a_914_ = lean_array_uget_borrowed(v_as_907_, v_i_909_);
lean_inc(v_a_914_);
lean_inc_ref(v_env_905_);
v___x_915_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_905_, v_opts_906_, v___x_913_, v_a_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_b_910_);
lean_dec_ref(v_env_905_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v_name_925_; lean_object* v_config_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
v_a_924_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_915_, 1);
v_name_925_ = lean_ctor_get(v_a_924_, 0);
v_config_926_ = lean_ctor_get(v_a_924_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_928_ = v_a_924_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_config_926_);
lean_inc(v_name_925_);
lean_dec(v_a_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_name_925_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_config_926_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; 
v___x_932_ = lean_array_push(v_b_910_, v___x_931_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_909_, v___x_933_);
v_i_909_ = v___x_934_;
v_b_910_ = v___x_932_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_938_, lean_object* v_opts_939_, lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_945_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_938_, v_opts_939_, v_as_940_, v_sz_boxed_944_, v_i_boxed_945_, v_b_943_);
lean_dec_ref(v_as_940_);
lean_dec_ref(v_opts_939_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_947_, lean_object* v_opts_948_, lean_object* v_as_949_, size_t v_sz_950_, size_t v_i_951_, lean_object* v_b_952_){
_start:
{
uint8_t v___x_953_; 
v___x_953_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec_ref(v_env_947_);
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v_b_952_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_957_; 
v___x_955_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
v_a_956_ = lean_array_uget_borrowed(v_as_949_, v_i_951_);
lean_inc(v_a_956_);
lean_inc_ref(v_env_947_);
v___x_957_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_947_, v_opts_948_, v___x_955_, v_a_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_b_952_);
lean_dec_ref(v_env_947_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v_name_967_; lean_object* v_config_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_979_; 
v_a_966_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_957_, 1);
v_name_967_ = lean_ctor_get(v_a_966_, 0);
v_config_968_ = lean_ctor_get(v_a_966_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_a_966_);
if (v_isSharedCheck_979_ == 0)
{
v___x_970_ = v_a_966_;
v_isShared_971_ = v_isSharedCheck_979_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_config_968_);
lean_inc(v_name_967_);
lean_dec(v_a_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_979_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_name_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_config_968_);
v___x_973_ = v_reuseFailAlloc_978_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; size_t v___x_975_; size_t v___x_976_; 
v___x_974_ = lean_array_push(v_b_952_, v___x_973_);
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_951_, v___x_975_);
v_i_951_ = v___x_976_;
v_b_952_ = v___x_974_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_980_, lean_object* v_opts_981_, lean_object* v_as_982_, lean_object* v_sz_983_, lean_object* v_i_984_, lean_object* v_b_985_){
_start:
{
size_t v_sz_boxed_986_; size_t v_i_boxed_987_; lean_object* v_res_988_; 
v_sz_boxed_986_ = lean_unbox_usize(v_sz_983_);
lean_dec(v_sz_983_);
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_980_, v_opts_981_, v_as_982_, v_sz_boxed_986_, v_i_boxed_987_, v_b_985_);
lean_dec_ref(v_as_982_);
lean_dec_ref(v_opts_981_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_t_989_, lean_object* v_k_990_){
_start:
{
if (lean_obj_tag(v_t_989_) == 0)
{
lean_object* v_k_991_; lean_object* v_v_992_; lean_object* v_l_993_; lean_object* v_r_994_; uint8_t v___x_995_; 
v_k_991_ = lean_ctor_get(v_t_989_, 1);
v_v_992_ = lean_ctor_get(v_t_989_, 2);
v_l_993_ = lean_ctor_get(v_t_989_, 3);
v_r_994_ = lean_ctor_get(v_t_989_, 4);
v___x_995_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_990_, v_k_991_);
switch(v___x_995_)
{
case 0:
{
v_t_989_ = v_l_993_;
goto _start;
}
case 1:
{
lean_object* v___x_997_; 
lean_inc(v_v_992_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v_v_992_);
return v___x_997_;
}
default: 
{
v_t_989_ = v_r_994_;
goto _start;
}
}
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_t_1000_, lean_object* v_k_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_1000_, v_k_1001_);
lean_dec(v_k_1001_);
lean_dec(v_t_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(lean_object* v_k_1003_, lean_object* v_v_1004_, lean_object* v_t_1005_){
_start:
{
if (lean_obj_tag(v_t_1005_) == 0)
{
lean_object* v_size_1006_; lean_object* v_k_1007_; lean_object* v_v_1008_; lean_object* v_l_1009_; lean_object* v_r_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1290_; 
v_size_1006_ = lean_ctor_get(v_t_1005_, 0);
v_k_1007_ = lean_ctor_get(v_t_1005_, 1);
v_v_1008_ = lean_ctor_get(v_t_1005_, 2);
v_l_1009_ = lean_ctor_get(v_t_1005_, 3);
v_r_1010_ = lean_ctor_get(v_t_1005_, 4);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_t_1005_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1012_ = v_t_1005_;
v_isShared_1013_ = v_isSharedCheck_1290_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_r_1010_);
lean_inc(v_l_1009_);
lean_inc(v_v_1008_);
lean_inc(v_k_1007_);
lean_inc(v_size_1006_);
lean_dec(v_t_1005_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1290_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v___x_1014_; 
v___x_1014_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1003_, v_k_1007_);
switch(v___x_1014_)
{
case 0:
{
lean_object* v_impl_1015_; lean_object* v___x_1016_; 
lean_dec(v_size_1006_);
v_impl_1015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1003_, v_v_1004_, v_l_1009_);
v___x_1016_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1010_) == 0)
{
lean_object* v_size_1017_; lean_object* v_size_1018_; lean_object* v_k_1019_; lean_object* v_v_1020_; lean_object* v_l_1021_; lean_object* v_r_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_size_1017_ = lean_ctor_get(v_r_1010_, 0);
v_size_1018_ = lean_ctor_get(v_impl_1015_, 0);
lean_inc(v_size_1018_);
v_k_1019_ = lean_ctor_get(v_impl_1015_, 1);
lean_inc(v_k_1019_);
v_v_1020_ = lean_ctor_get(v_impl_1015_, 2);
lean_inc(v_v_1020_);
v_l_1021_ = lean_ctor_get(v_impl_1015_, 3);
lean_inc(v_l_1021_);
v_r_1022_ = lean_ctor_get(v_impl_1015_, 4);
lean_inc(v_r_1022_);
v___x_1023_ = lean_unsigned_to_nat(3u);
v___x_1024_ = lean_nat_mul(v___x_1023_, v_size_1017_);
v___x_1025_ = lean_nat_dec_lt(v___x_1024_, v_size_1018_);
lean_dec(v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_dec(v_r_1022_);
lean_dec(v_l_1021_);
lean_dec(v_v_1020_);
lean_dec(v_k_1019_);
v___x_1026_ = lean_nat_add(v___x_1016_, v_size_1018_);
lean_dec(v_size_1018_);
v___x_1027_ = lean_nat_add(v___x_1026_, v_size_1017_);
lean_dec(v___x_1026_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 3, v_impl_1015_);
lean_ctor_set(v___x_1012_, 0, v___x_1027_);
v___x_1029_ = v___x_1012_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_impl_1015_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_r_1010_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v_impl_1015_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1097_ = lean_ctor_get(v_impl_1015_, 4);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_impl_1015_, 3);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_impl_1015_, 2);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_impl_1015_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_impl_1015_, 0);
lean_dec(v_unused_1101_);
v___x_1032_ = v_impl_1015_;
v_isShared_1033_ = v_isSharedCheck_1096_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v_impl_1015_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1096_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_size_1034_; lean_object* v_size_1035_; lean_object* v_k_1036_; lean_object* v_v_1037_; lean_object* v_l_1038_; lean_object* v_r_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_size_1034_ = lean_ctor_get(v_l_1021_, 0);
v_size_1035_ = lean_ctor_get(v_r_1022_, 0);
v_k_1036_ = lean_ctor_get(v_r_1022_, 1);
v_v_1037_ = lean_ctor_get(v_r_1022_, 2);
v_l_1038_ = lean_ctor_get(v_r_1022_, 3);
v_r_1039_ = lean_ctor_get(v_r_1022_, 4);
v___x_1040_ = lean_unsigned_to_nat(2u);
v___x_1041_ = lean_nat_mul(v___x_1040_, v_size_1034_);
v___x_1042_ = lean_nat_dec_lt(v_size_1035_, v___x_1041_);
lean_dec(v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1071_; 
lean_inc(v_r_1039_);
lean_inc(v_l_1038_);
lean_inc(v_v_1037_);
lean_inc(v_k_1036_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_r_1022_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1072_ = lean_ctor_get(v_r_1022_, 4);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_r_1022_, 3);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_r_1022_, 2);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_r_1022_, 1);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_r_1022_, 0);
lean_dec(v_unused_1076_);
v___x_1044_ = v_r_1022_;
v_isShared_1045_ = v_isSharedCheck_1071_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v_r_1022_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1071_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___x_1059_; lean_object* v___y_1061_; 
v___x_1046_ = lean_nat_add(v___x_1016_, v_size_1018_);
lean_dec(v_size_1018_);
v___x_1047_ = lean_nat_add(v___x_1046_, v_size_1017_);
lean_dec(v___x_1046_);
v___x_1059_ = lean_nat_add(v___x_1016_, v_size_1034_);
if (lean_obj_tag(v_l_1038_) == 0)
{
lean_object* v_size_1069_; 
v_size_1069_ = lean_ctor_get(v_l_1038_, 0);
lean_inc(v_size_1069_);
v___y_1061_ = v_size_1069_;
goto v___jp_1060_;
}
else
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_unsigned_to_nat(0u);
v___y_1061_ = v___x_1070_;
goto v___jp_1060_;
}
v___jp_1048_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_nat_add(v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 4, v_r_1010_);
lean_ctor_set(v___x_1044_, 3, v_r_1039_);
lean_ctor_set(v___x_1044_, 2, v_v_1008_);
lean_ctor_set(v___x_1044_, 1, v_k_1007_);
lean_ctor_set(v___x_1044_, 0, v___x_1052_);
v___x_1054_ = v___x_1044_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_r_1039_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_r_1010_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 4, v___x_1054_);
lean_ctor_set(v___x_1032_, 3, v___y_1049_);
lean_ctor_set(v___x_1032_, 2, v_v_1037_);
lean_ctor_set(v___x_1032_, 1, v_k_1036_);
lean_ctor_set(v___x_1032_, 0, v___x_1047_);
v___x_1056_ = v___x_1032_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_1036_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_1037_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v___y_1049_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_nat_add(v___x_1059_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec(v___x_1059_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v_l_1038_);
lean_ctor_set(v___x_1012_, 3, v_l_1021_);
lean_ctor_set(v___x_1012_, 2, v_v_1020_);
lean_ctor_set(v___x_1012_, 1, v_k_1019_);
lean_ctor_set(v___x_1012_, 0, v___x_1062_);
v___x_1064_ = v___x_1012_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_k_1019_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_v_1020_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_l_1021_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_l_1038_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_nat_add(v___x_1016_, v_size_1017_);
if (lean_obj_tag(v_r_1039_) == 0)
{
lean_object* v_size_1066_; 
v_size_1066_ = lean_ctor_get(v_r_1039_, 0);
lean_inc(v_size_1066_);
v___y_1049_ = v___x_1064_;
v___y_1050_ = v___x_1065_;
v___y_1051_ = v_size_1066_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___y_1049_ = v___x_1064_;
v___y_1050_ = v___x_1065_;
v___y_1051_ = v___x_1067_;
goto v___jp_1048_;
}
}
}
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_del_object(v___x_1012_);
v___x_1077_ = lean_nat_add(v___x_1016_, v_size_1018_);
lean_dec(v_size_1018_);
v___x_1078_ = lean_nat_add(v___x_1077_, v_size_1017_);
lean_dec(v___x_1077_);
v___x_1079_ = lean_nat_add(v___x_1016_, v_size_1017_);
v___x_1080_ = lean_nat_add(v___x_1079_, v_size_1035_);
lean_dec(v___x_1079_);
lean_inc_ref(v_r_1010_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 4, v_r_1010_);
lean_ctor_set(v___x_1032_, 3, v_r_1022_);
lean_ctor_set(v___x_1032_, 2, v_v_1008_);
lean_ctor_set(v___x_1032_, 1, v_k_1007_);
lean_ctor_set(v___x_1032_, 0, v___x_1080_);
v___x_1082_ = v___x_1032_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_r_1022_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_r_1010_);
v___x_1082_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_isSharedCheck_1089_ = !lean_is_exclusive(v_r_1010_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1090_ = lean_ctor_get(v_r_1010_, 4);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_r_1010_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_r_1010_, 2);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_1010_, 1);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_r_1010_, 0);
lean_dec(v_unused_1094_);
v___x_1084_ = v_r_1010_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v_r_1010_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 4, v___x_1082_);
lean_ctor_set(v___x_1084_, 3, v_l_1021_);
lean_ctor_set(v___x_1084_, 2, v_v_1020_);
lean_ctor_set(v___x_1084_, 1, v_k_1019_);
lean_ctor_set(v___x_1084_, 0, v___x_1078_);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_1019_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_1020_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_l_1021_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___x_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1102_; 
v_l_1102_ = lean_ctor_get(v_impl_1015_, 3);
lean_inc(v_l_1102_);
if (lean_obj_tag(v_l_1102_) == 0)
{
lean_object* v_r_1103_; lean_object* v_k_1104_; lean_object* v_v_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1116_; 
v_r_1103_ = lean_ctor_get(v_impl_1015_, 4);
v_k_1104_ = lean_ctor_get(v_impl_1015_, 1);
v_v_1105_ = lean_ctor_get(v_impl_1015_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_impl_1015_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1117_ = lean_ctor_get(v_impl_1015_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_impl_1015_, 0);
lean_dec(v_unused_1118_);
v___x_1107_ = v_impl_1015_;
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_r_1103_);
lean_inc(v_v_1105_);
lean_inc(v_k_1104_);
lean_dec(v_impl_1015_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1103_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 3, v_r_1103_);
lean_ctor_set(v___x_1107_, 2, v_v_1008_);
lean_ctor_set(v___x_1107_, 1, v_k_1007_);
lean_ctor_set(v___x_1107_, 0, v___x_1016_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_r_1103_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_r_1103_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v___x_1111_);
lean_ctor_set(v___x_1012_, 3, v_l_1102_);
lean_ctor_set(v___x_1012_, 2, v_v_1105_);
lean_ctor_set(v___x_1012_, 1, v_k_1104_);
lean_ctor_set(v___x_1012_, 0, v___x_1109_);
v___x_1113_ = v___x_1012_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_r_1119_; 
v_r_1119_ = lean_ctor_get(v_impl_1015_, 4);
lean_inc(v_r_1119_);
if (lean_obj_tag(v_r_1119_) == 0)
{
lean_object* v_k_1120_; lean_object* v_v_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1144_; 
v_k_1120_ = lean_ctor_get(v_impl_1015_, 1);
v_v_1121_ = lean_ctor_get(v_impl_1015_, 2);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_impl_1015_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1145_ = lean_ctor_get(v_impl_1015_, 4);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_impl_1015_, 3);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_impl_1015_, 0);
lean_dec(v_unused_1147_);
v___x_1123_ = v_impl_1015_;
v_isShared_1124_ = v_isSharedCheck_1144_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_v_1121_);
lean_inc(v_k_1120_);
lean_dec(v_impl_1015_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1144_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1140_; 
v_k_1125_ = lean_ctor_get(v_r_1119_, 1);
v_v_1126_ = lean_ctor_get(v_r_1119_, 2);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_r_1119_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; lean_object* v_unused_1142_; lean_object* v_unused_1143_; 
v_unused_1141_ = lean_ctor_get(v_r_1119_, 4);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_r_1119_, 3);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_r_1119_, 0);
lean_dec(v_unused_1143_);
v___x_1128_ = v_r_1119_;
v_isShared_1129_ = v_isSharedCheck_1140_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_v_1126_);
lean_inc(v_k_1125_);
lean_dec(v_r_1119_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1140_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_unsigned_to_nat(3u);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v_l_1102_);
lean_ctor_set(v___x_1128_, 3, v_l_1102_);
lean_ctor_set(v___x_1128_, 2, v_v_1121_);
lean_ctor_set(v___x_1128_, 1, v_k_1120_);
lean_ctor_set(v___x_1128_, 0, v___x_1016_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1120_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1121_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_l_1102_);
v___x_1132_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v_l_1102_);
lean_ctor_set(v___x_1123_, 2, v_v_1008_);
lean_ctor_set(v___x_1123_, 1, v_k_1007_);
lean_ctor_set(v___x_1123_, 0, v___x_1016_);
v___x_1134_ = v___x_1123_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_l_1102_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v___x_1134_);
lean_ctor_set(v___x_1012_, 3, v___x_1132_);
lean_ctor_set(v___x_1012_, 2, v_v_1126_);
lean_ctor_set(v___x_1012_, 1, v_k_1125_);
lean_ctor_set(v___x_1012_, 0, v___x_1130_);
v___x_1136_ = v___x_1012_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_1125_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_1126_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_unsigned_to_nat(2u);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v_r_1119_);
lean_ctor_set(v___x_1012_, 3, v_impl_1015_);
lean_ctor_set(v___x_1012_, 0, v___x_1148_);
v___x_1150_ = v___x_1012_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_impl_1015_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_r_1119_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1153_; 
lean_dec(v_v_1008_);
lean_dec(v_k_1007_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v_v_1004_);
lean_ctor_set(v___x_1012_, 1, v_k_1003_);
v___x_1153_ = v___x_1012_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_size_1006_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_1003_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_1004_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_l_1009_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_r_1010_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
default: 
{
lean_object* v_impl_1155_; lean_object* v___x_1156_; 
lean_dec(v_size_1006_);
v_impl_1155_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1003_, v_v_1004_, v_r_1010_);
v___x_1156_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1009_) == 0)
{
lean_object* v_size_1157_; lean_object* v_size_1158_; lean_object* v_k_1159_; lean_object* v_v_1160_; lean_object* v_l_1161_; lean_object* v_r_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_size_1157_ = lean_ctor_get(v_l_1009_, 0);
v_size_1158_ = lean_ctor_get(v_impl_1155_, 0);
lean_inc(v_size_1158_);
v_k_1159_ = lean_ctor_get(v_impl_1155_, 1);
lean_inc(v_k_1159_);
v_v_1160_ = lean_ctor_get(v_impl_1155_, 2);
lean_inc(v_v_1160_);
v_l_1161_ = lean_ctor_get(v_impl_1155_, 3);
lean_inc(v_l_1161_);
v_r_1162_ = lean_ctor_get(v_impl_1155_, 4);
lean_inc(v_r_1162_);
v___x_1163_ = lean_unsigned_to_nat(3u);
v___x_1164_ = lean_nat_mul(v___x_1163_, v_size_1157_);
v___x_1165_ = lean_nat_dec_lt(v___x_1164_, v_size_1158_);
lean_dec(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_dec(v_r_1162_);
lean_dec(v_l_1161_);
lean_dec(v_v_1160_);
lean_dec(v_k_1159_);
v___x_1166_ = lean_nat_add(v___x_1156_, v_size_1157_);
v___x_1167_ = lean_nat_add(v___x_1166_, v_size_1158_);
lean_dec(v_size_1158_);
lean_dec(v___x_1166_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v_impl_1155_);
lean_ctor_set(v___x_1012_, 0, v___x_1167_);
v___x_1169_ = v___x_1012_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_l_1009_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_impl_1155_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1234_; 
v_isSharedCheck_1234_ = !lean_is_exclusive(v_impl_1155_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; 
v_unused_1235_ = lean_ctor_get(v_impl_1155_, 4);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_impl_1155_, 3);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_impl_1155_, 2);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_impl_1155_, 1);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_impl_1155_, 0);
lean_dec(v_unused_1239_);
v___x_1172_ = v_impl_1155_;
v_isShared_1173_ = v_isSharedCheck_1234_;
goto v_resetjp_1171_;
}
else
{
lean_dec(v_impl_1155_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1234_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_size_1174_; lean_object* v_k_1175_; lean_object* v_v_1176_; lean_object* v_l_1177_; lean_object* v_r_1178_; lean_object* v_size_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_size_1174_ = lean_ctor_get(v_l_1161_, 0);
v_k_1175_ = lean_ctor_get(v_l_1161_, 1);
v_v_1176_ = lean_ctor_get(v_l_1161_, 2);
v_l_1177_ = lean_ctor_get(v_l_1161_, 3);
v_r_1178_ = lean_ctor_get(v_l_1161_, 4);
v_size_1179_ = lean_ctor_get(v_r_1162_, 0);
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = lean_nat_mul(v___x_1180_, v_size_1179_);
v___x_1182_ = lean_nat_dec_lt(v_size_1174_, v___x_1181_);
lean_dec(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1210_; 
lean_inc(v_r_1178_);
lean_inc(v_l_1177_);
lean_inc(v_v_1176_);
lean_inc(v_k_1175_);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_l_1161_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; lean_object* v_unused_1212_; lean_object* v_unused_1213_; lean_object* v_unused_1214_; lean_object* v_unused_1215_; 
v_unused_1211_ = lean_ctor_get(v_l_1161_, 4);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_l_1161_, 3);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_l_1161_, 2);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_l_1161_, 1);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_l_1161_, 0);
lean_dec(v_unused_1215_);
v___x_1184_ = v_l_1161_;
v_isShared_1185_ = v_isSharedCheck_1210_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_l_1161_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1210_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1200_; 
v___x_1186_ = lean_nat_add(v___x_1156_, v_size_1157_);
v___x_1187_ = lean_nat_add(v___x_1186_, v_size_1158_);
lean_dec(v_size_1158_);
if (lean_obj_tag(v_l_1177_) == 0)
{
lean_object* v_size_1208_; 
v_size_1208_ = lean_ctor_get(v_l_1177_, 0);
lean_inc(v_size_1208_);
v___y_1200_ = v_size_1208_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___y_1200_ = v___x_1209_;
goto v___jp_1199_;
}
v___jp_1188_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_nat_add(v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec(v___y_1190_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 4, v_r_1162_);
lean_ctor_set(v___x_1184_, 3, v_r_1178_);
lean_ctor_set(v___x_1184_, 2, v_v_1160_);
lean_ctor_set(v___x_1184_, 1, v_k_1159_);
lean_ctor_set(v___x_1184_, 0, v___x_1192_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_k_1159_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_v_1160_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_r_1178_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v_r_1162_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 4, v___x_1194_);
lean_ctor_set(v___x_1172_, 3, v___y_1189_);
lean_ctor_set(v___x_1172_, 2, v_v_1176_);
lean_ctor_set(v___x_1172_, 1, v_k_1175_);
lean_ctor_set(v___x_1172_, 0, v___x_1187_);
v___x_1196_ = v___x_1172_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_1175_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_1176_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v___y_1189_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
v___jp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_nat_add(v___x_1186_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec(v___x_1186_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v_l_1177_);
lean_ctor_set(v___x_1012_, 0, v___x_1201_);
v___x_1203_ = v___x_1012_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_l_1009_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_l_1177_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_nat_add(v___x_1156_, v_size_1179_);
if (lean_obj_tag(v_r_1178_) == 0)
{
lean_object* v_size_1205_; 
v_size_1205_ = lean_ctor_get(v_r_1178_, 0);
lean_inc(v_size_1205_);
v___y_1189_ = v___x_1203_;
v___y_1190_ = v___x_1204_;
v___y_1191_ = v_size_1205_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___y_1189_ = v___x_1203_;
v___y_1190_ = v___x_1204_;
v___y_1191_ = v___x_1206_;
goto v___jp_1188_;
}
}
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
lean_del_object(v___x_1012_);
v___x_1216_ = lean_nat_add(v___x_1156_, v_size_1157_);
v___x_1217_ = lean_nat_add(v___x_1216_, v_size_1158_);
lean_dec(v_size_1158_);
v___x_1218_ = lean_nat_add(v___x_1216_, v_size_1174_);
lean_dec(v___x_1216_);
lean_inc_ref(v_l_1009_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 4, v_l_1161_);
lean_ctor_set(v___x_1172_, 3, v_l_1009_);
lean_ctor_set(v___x_1172_, 2, v_v_1008_);
lean_ctor_set(v___x_1172_, 1, v_k_1007_);
lean_ctor_set(v___x_1172_, 0, v___x_1218_);
v___x_1220_ = v___x_1172_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_l_1009_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_l_1161_);
v___x_1220_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_isSharedCheck_1227_ = !lean_is_exclusive(v_l_1009_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; lean_object* v_unused_1229_; lean_object* v_unused_1230_; lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1228_ = lean_ctor_get(v_l_1009_, 4);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_l_1009_, 3);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_l_1009_, 2);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_l_1009_, 1);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_l_1009_, 0);
lean_dec(v_unused_1232_);
v___x_1222_ = v_l_1009_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_dec(v_l_1009_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 4, v_r_1162_);
lean_ctor_set(v___x_1222_, 3, v___x_1220_);
lean_ctor_set(v___x_1222_, 2, v_v_1160_);
lean_ctor_set(v___x_1222_, 1, v_k_1159_);
lean_ctor_set(v___x_1222_, 0, v___x_1217_);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_1159_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_v_1160_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_r_1162_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1240_; 
v_l_1240_ = lean_ctor_get(v_impl_1155_, 3);
lean_inc(v_l_1240_);
if (lean_obj_tag(v_l_1240_) == 0)
{
lean_object* v_r_1241_; lean_object* v_k_1242_; lean_object* v_v_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1266_; 
v_r_1241_ = lean_ctor_get(v_impl_1155_, 4);
v_k_1242_ = lean_ctor_get(v_impl_1155_, 1);
v_v_1243_ = lean_ctor_get(v_impl_1155_, 2);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_impl_1155_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; lean_object* v_unused_1268_; 
v_unused_1267_ = lean_ctor_get(v_impl_1155_, 3);
lean_dec(v_unused_1267_);
v_unused_1268_ = lean_ctor_get(v_impl_1155_, 0);
lean_dec(v_unused_1268_);
v___x_1245_ = v_impl_1155_;
v_isShared_1246_ = v_isSharedCheck_1266_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_r_1241_);
lean_inc(v_v_1243_);
lean_inc(v_k_1242_);
lean_dec(v_impl_1155_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1266_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_k_1247_; lean_object* v_v_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1262_; 
v_k_1247_ = lean_ctor_get(v_l_1240_, 1);
v_v_1248_ = lean_ctor_get(v_l_1240_, 2);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_l_1240_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; lean_object* v_unused_1264_; lean_object* v_unused_1265_; 
v_unused_1263_ = lean_ctor_get(v_l_1240_, 4);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v_l_1240_, 3);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_l_1240_, 0);
lean_dec(v_unused_1265_);
v___x_1250_ = v_l_1240_;
v_isShared_1251_ = v_isSharedCheck_1262_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_v_1248_);
lean_inc(v_k_1247_);
lean_dec(v_l_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1262_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1241_, 2);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 4, v_r_1241_);
lean_ctor_set(v___x_1250_, 3, v_r_1241_);
lean_ctor_set(v___x_1250_, 2, v_v_1008_);
lean_ctor_set(v___x_1250_, 1, v_k_1007_);
lean_ctor_set(v___x_1250_, 0, v___x_1156_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_r_1241_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1241_);
v___x_1254_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
lean_inc(v_r_1241_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 3, v_r_1241_);
lean_ctor_set(v___x_1245_, 0, v___x_1156_);
v___x_1256_ = v___x_1245_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1242_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1243_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_r_1241_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_r_1241_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v___x_1256_);
lean_ctor_set(v___x_1012_, 3, v___x_1254_);
lean_ctor_set(v___x_1012_, 2, v_v_1248_);
lean_ctor_set(v___x_1012_, 1, v_k_1247_);
lean_ctor_set(v___x_1012_, 0, v___x_1252_);
v___x_1258_ = v___x_1012_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_k_1247_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_v_1248_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
else
{
lean_object* v_r_1269_; 
v_r_1269_ = lean_ctor_get(v_impl_1155_, 4);
lean_inc(v_r_1269_);
if (lean_obj_tag(v_r_1269_) == 0)
{
lean_object* v_k_1270_; lean_object* v_v_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1282_; 
v_k_1270_ = lean_ctor_get(v_impl_1155_, 1);
v_v_1271_ = lean_ctor_get(v_impl_1155_, 2);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_impl_1155_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; lean_object* v_unused_1284_; lean_object* v_unused_1285_; 
v_unused_1283_ = lean_ctor_get(v_impl_1155_, 4);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v_impl_1155_, 3);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_impl_1155_, 0);
lean_dec(v_unused_1285_);
v___x_1273_ = v_impl_1155_;
v_isShared_1274_ = v_isSharedCheck_1282_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_v_1271_);
lean_inc(v_k_1270_);
lean_dec(v_impl_1155_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1282_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_unsigned_to_nat(3u);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 4, v_l_1240_);
lean_ctor_set(v___x_1273_, 2, v_v_1008_);
lean_ctor_set(v___x_1273_, 1, v_k_1007_);
lean_ctor_set(v___x_1273_, 0, v___x_1156_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_l_1240_);
v___x_1277_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v_r_1269_);
lean_ctor_set(v___x_1012_, 3, v___x_1277_);
lean_ctor_set(v___x_1012_, 2, v_v_1271_);
lean_ctor_set(v___x_1012_, 1, v_k_1270_);
lean_ctor_set(v___x_1012_, 0, v___x_1275_);
v___x_1279_ = v___x_1012_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_1270_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_1271_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_r_1269_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_unsigned_to_nat(2u);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v_impl_1155_);
lean_ctor_set(v___x_1012_, 3, v_r_1269_);
lean_ctor_set(v___x_1012_, 0, v___x_1286_);
v___x_1288_ = v___x_1012_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_r_1269_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_impl_1155_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
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
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_k_1003_);
lean_ctor_set(v___x_1292_, 2, v_v_1004_);
lean_ctor_set(v___x_1292_, 3, v_t_1005_);
lean_ctor_set(v___x_1292_, 4, v_t_1005_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object* v___x_1296_, lean_object* v_as_1297_, size_t v_i_1298_, size_t v_stop_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_usize_dec_eq(v_i_1298_, v_stop_1299_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v_name_1305_; lean_object* v_kind_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_array_uget_borrowed(v_as_1297_, v_i_1298_);
v_name_1305_ = lean_ctor_get(v___x_1304_, 1);
v_kind_1306_ = lean_ctor_get(v___x_1304_, 2);
v___x_1307_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_b_1300_, v_name_1305_);
if (lean_obj_tag(v___x_1307_) == 1)
{
lean_object* v_val_1308_; lean_object* v_kind_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec(v_b_1300_);
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v_kind_1309_ = lean_ctor_get(v_val_1308_, 2);
lean_inc(v_kind_1309_);
lean_dec(v_val_1308_);
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0));
v___x_1311_ = lean_string_append(v___x_1296_, v___x_1310_);
v___x_1312_ = 1;
lean_inc(v_name_1305_);
v___x_1313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1305_, v___x_1312_);
v___x_1314_ = lean_string_append(v___x_1311_, v___x_1313_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1));
v___x_1316_ = lean_string_append(v___x_1314_, v___x_1315_);
v___x_1317_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1309_, v___x_1312_);
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2));
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
lean_inc(v_kind_1306_);
v___x_1321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1306_, v___x_1312_);
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
v___x_1325_ = 3;
v___x_1326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*1, v___x_1325_);
v___x_1327_ = lean_array_get_size(v___y_1301_);
v___x_1328_ = lean_array_push(v___y_1301_, v___x_1326_);
v___x_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; 
lean_dec(v___x_1307_);
lean_inc(v___x_1304_);
lean_inc(v_name_1305_);
v___x_1330_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_name_1305_, v___x_1304_, v_b_1300_);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1298_, v___x_1331_);
v_i_1298_ = v___x_1332_;
v_b_1300_ = v___x_1330_;
goto _start;
}
}
else
{
lean_object* v___x_1334_; 
lean_dec_ref(v___x_1296_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_b_1300_);
lean_ctor_set(v___x_1334_, 1, v___y_1301_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object* v___x_1335_, lean_object* v_as_1336_, lean_object* v_i_1337_, lean_object* v_stop_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
size_t v_i_boxed_1342_; size_t v_stop_boxed_1343_; lean_object* v_res_1344_; 
v_i_boxed_1342_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_stop_boxed_1343_ = lean_unbox_usize(v_stop_1338_);
lean_dec(v_stop_1338_);
v_res_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1335_, v_as_1336_, v_i_boxed_1342_, v_stop_boxed_1343_, v_b_1339_, v___y_1340_);
lean_dec_ref(v_as_1336_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1351_, lean_object* v_opts_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_a_1356_; lean_object* v_a_1357_; lean_object* v_a_1360_; lean_object* v_a_1361_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v_env_1351_);
v___x_1363_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1351_, v_opts_1352_);
v___x_1364_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1352_);
lean_inc_ref_n(v_env_1351_, 2);
v___f_1367_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1367_, 0, v_env_1351_);
lean_closure_set(v___f_1367_, 1, v_opts_1352_);
lean_closure_set(v___f_1367_, 2, v___x_1366_);
v___x_1368_ = l_Lake_targetAttr;
v___x_1369_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1351_, v___x_1368_, v___f_1367_);
v___x_1370_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1369_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v_baseName_1372_; lean_object* v_keyName_1373_; lean_object* v_config_1374_; lean_object* v_toArray_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v_baseName_1372_ = lean_ctor_get(v_a_1365_, 0);
v_keyName_1373_ = lean_ctor_get(v_a_1365_, 1);
v_config_1374_ = lean_ctor_get(v_a_1365_, 3);
v_toArray_1375_ = lean_ctor_get(v_a_1371_, 1);
v_sz_1376_ = lean_array_size(v_toArray_1375_);
v___x_1377_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1375_);
lean_inc(v_keyName_1373_);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v_keyName_1373_, v_sz_1376_, v___x_1377_, v_toArray_1375_, v_a_1353_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1647_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_a_1380_ = lean_ctor_get(v___x_1378_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1382_ = v___x_1378_;
v_isShared_1383_ = v_isSharedCheck_1647_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1647_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v_a_1425_; lean_object* v_a_1426_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v___y_1489_; lean_object* v_a_1490_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___x_1618_; lean_object* v_a_1620_; lean_object* v_a_1621_; lean_object* v___y_1629_; uint8_t v___x_1641_; 
v___x_1410_ = l_Lake_instTypeNameScriptFn_unsafe__1;
v___x_1411_ = 0;
lean_inc(v_baseName_1372_);
v___x_1412_ = l_Lean_Name_toString(v_baseName_1372_, v___x_1411_);
v___x_1413_ = lean_box(v___x_1411_);
lean_inc_ref(v___x_1412_);
lean_inc_ref(v_opts_1352_);
lean_inc_ref(v_env_1351_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1414_, 0, v___x_1413_);
lean_closure_set(v___f_1414_, 1, v_env_1351_);
lean_closure_set(v___f_1414_, 2, v_opts_1352_);
lean_closure_set(v___f_1414_, 3, v___x_1410_);
lean_closure_set(v___f_1414_, 4, v___x_1412_);
v___x_1415_ = lean_box(1);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1618_ = lean_array_get_size(v_a_1379_);
v___x_1641_ = lean_nat_dec_lt(v___x_1416_, v___x_1618_);
if (v___x_1641_ == 0)
{
v_a_1620_ = v___x_1415_;
v_a_1621_ = v_a_1380_;
goto v___jp_1619_;
}
else
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_nat_dec_le(v___x_1618_, v___x_1618_);
if (v___x_1642_ == 0)
{
if (v___x_1641_ == 0)
{
v_a_1620_ = v___x_1415_;
v_a_1621_ = v_a_1380_;
goto v___jp_1619_;
}
else
{
size_t v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_usize_of_nat(v___x_1618_);
lean_inc_ref(v___x_1412_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1412_, v_a_1379_, v___x_1377_, v___x_1643_, v___x_1415_, v_a_1380_);
v___y_1629_ = v___x_1644_;
goto v___jp_1628_;
}
}
else
{
size_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_usize_of_nat(v___x_1618_);
lean_inc_ref(v___x_1412_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1412_, v_a_1379_, v___x_1377_, v___x_1645_, v___x_1415_, v_a_1380_);
v___y_1629_ = v___x_1646_;
goto v___jp_1628_;
}
}
v___jp_1384_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1365_);
lean_ctor_set(v___x_1397_, 1, v___y_1391_);
lean_ctor_set(v___x_1397_, 2, v_a_1396_);
lean_ctor_set(v___x_1397_, 3, v_a_1379_);
lean_ctor_set(v___x_1397_, 4, v___y_1386_);
lean_ctor_set(v___x_1397_, 5, v___y_1385_);
lean_ctor_set(v___x_1397_, 6, v___y_1388_);
lean_ctor_set(v___x_1397_, 7, v___y_1392_);
lean_ctor_set(v___x_1397_, 8, v___y_1393_);
lean_ctor_set(v___x_1397_, 9, v___y_1390_);
lean_ctor_set(v___x_1397_, 10, v___y_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___y_1389_);
lean_ctor_set(v___x_1382_, 0, v___x_1397_);
v___x_1399_ = v___x_1382_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___y_1389_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_dec_ref(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v_a_1379_);
lean_dec(v_a_1365_);
v_a_1401_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1402_ = lean_io_error_to_string(v_a_1401_);
v___x_1403_ = 3;
v___x_1404_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set_uint8(v___x_1404_, sizeof(void*)*1, v___x_1403_);
v___x_1405_ = lean_array_get_size(v___y_1389_);
v___x_1406_ = lean_array_push(v___y_1389_, v___x_1404_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 1);
lean_ctor_set(v___x_1382_, 1, v___x_1406_);
lean_ctor_set(v___x_1382_, 0, v___x_1405_);
v___x_1408_ = v___x_1382_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
v___jp_1417_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; size_t v_sz_1430_; lean_object* v___x_1431_; 
v___x_1427_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1428_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1351_, 2);
v___x_1429_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1428_, v_env_1351_);
v_sz_1430_ = lean_array_size(v___x_1429_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1351_, v_opts_1352_, v___x_1429_, v_sz_1430_, v___x_1377_, v___x_1427_);
lean_dec_ref(v___x_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v___y_1385_ = v___y_1419_;
v___y_1386_ = v___y_1418_;
v___y_1387_ = v_a_1425_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v_a_1426_;
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1423_;
v___y_1393_ = v___y_1424_;
v___y_1394_ = v___x_1431_;
goto v___jp_1384_;
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; size_t v_sz_1435_; lean_object* v___x_1436_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1351_, 2);
v___x_1434_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1433_, v_env_1351_);
v_sz_1435_ = lean_array_size(v___x_1434_);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1351_, v_opts_1352_, v___x_1434_, v_sz_1435_, v___x_1377_, v_a_1432_);
lean_dec_ref(v___x_1434_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v___y_1385_ = v___y_1419_;
v___y_1386_ = v___y_1418_;
v___y_1387_ = v_a_1425_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v_a_1426_;
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1423_;
v___y_1393_ = v___y_1424_;
v___y_1394_ = v___x_1436_;
goto v___jp_1384_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; size_t v_sz_1440_; lean_object* v___x_1441_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1351_);
v___x_1439_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1438_, v_env_1351_);
v_sz_1440_ = lean_array_size(v___x_1439_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1351_, v_opts_1352_, v___x_1439_, v_sz_1440_, v___x_1377_, v_a_1437_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v_opts_1352_);
v___y_1385_ = v___y_1419_;
v___y_1386_ = v___y_1418_;
v___y_1387_ = v_a_1425_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v_a_1426_;
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1423_;
v___y_1393_ = v___y_1424_;
v___y_1394_ = v___x_1441_;
goto v___jp_1384_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; size_t v_sz_1454_; lean_object* v___x_1455_; 
v___x_1452_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1351_);
v___x_1453_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1452_, v_env_1351_);
v_sz_1454_ = lean_array_size(v___x_1453_);
lean_inc_ref(v___x_1412_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1371_, v___y_1446_, v___x_1412_, v_sz_1454_, v___x_1377_, v___x_1453_, v_a_1451_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v_a_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
v_a_1457_ = lean_ctor_get(v___x_1455_, 1);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1455_, 2);
v___x_1458_ = lean_array_get_size(v_a_1456_);
v___x_1459_ = lean_nat_dec_lt(v___y_1443_, v___x_1458_);
if (v___x_1459_ == 0)
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_nat_dec_lt(v___x_1416_, v___x_1458_);
if (v___x_1460_ == 0)
{
lean_object* v_lintDriver_1461_; 
lean_dec(v_a_1456_);
lean_dec_ref(v___x_1412_);
v_lintDriver_1461_ = lean_ctor_get(v_config_1374_, 14);
lean_inc_ref(v_lintDriver_1461_);
v___y_1418_ = v___y_1445_;
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1446_;
v___y_1421_ = v_a_1450_;
v___y_1422_ = v___y_1447_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1449_;
v_a_1425_ = v_lintDriver_1461_;
v_a_1426_ = v_a_1457_;
goto v___jp_1417_;
}
else
{
lean_object* v_lintDriver_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_lintDriver_1462_ = lean_ctor_get(v_config_1374_, 14);
v___x_1463_ = lean_string_utf8_byte_size(v_lintDriver_1462_);
v___x_1464_ = lean_nat_dec_eq(v___x_1463_, v___x_1416_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v___x_1465_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1466_ = lean_string_append(v___x_1412_, v___x_1465_);
v___x_1467_ = 3;
v___x_1468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*1, v___x_1467_);
v___x_1469_ = lean_array_get_size(v_a_1457_);
v___x_1470_ = lean_array_push(v_a_1457_, v___x_1468_);
v_a_1360_ = v___x_1469_;
v_a_1361_ = v___x_1470_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v___x_1412_);
v___x_1471_ = lean_array_fget(v_a_1456_, v___x_1416_);
lean_dec(v_a_1456_);
v___x_1472_ = l_Lean_Name_toString(v___x_1471_, v___x_1464_);
v___y_1418_ = v___y_1445_;
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1446_;
v___y_1421_ = v_a_1450_;
v___y_1422_ = v___y_1447_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1449_;
v_a_1425_ = v___x_1472_;
v_a_1426_ = v_a_1457_;
goto v___jp_1417_;
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v___x_1473_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1474_ = lean_string_append(v___x_1412_, v___x_1473_);
v___x_1475_ = 3;
v___x_1476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set_uint8(v___x_1476_, sizeof(void*)*1, v___x_1475_);
v___x_1477_ = lean_array_get_size(v_a_1457_);
v___x_1478_ = lean_array_push(v_a_1457_, v___x_1476_);
v_a_1360_ = v___x_1477_;
v_a_1361_ = v___x_1478_;
goto v___jp_1359_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_a_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1479_ = lean_ctor_get(v___x_1455_, 0);
v_a_1480_ = lean_ctor_get(v___x_1455_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1455_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_inc(v_a_1479_);
lean_dec(v___x_1455_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1479_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
v___jp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; size_t v_sz_1493_; lean_object* v___x_1494_; 
v___x_1491_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1351_);
v___x_1492_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1491_, v_env_1351_);
v_sz_1493_ = lean_array_size(v___x_1492_);
lean_inc_ref(v___x_1412_);
lean_inc(v_a_1371_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1371_, v___x_1412_, v_sz_1493_, v___x_1377_, v___x_1492_, v_a_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
v_a_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1494_, 2);
v___x_1497_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1351_);
v___x_1498_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1351_, v___x_1497_, v___f_1414_, v_a_1496_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; size_t v_sz_1503_; lean_object* v___x_1504_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
v_a_1500_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1498_, 2);
v___x_1501_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1351_);
v___x_1502_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1501_, v_env_1351_);
v_sz_1503_ = lean_array_size(v___x_1502_);
lean_inc_ref(v___x_1412_);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1499_, v___x_1412_, v_sz_1503_, v___x_1377_, v___x_1502_, v_a_1500_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; size_t v_sz_1509_; lean_object* v___x_1510_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
v_a_1506_ = lean_ctor_get(v___x_1504_, 1);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1504_, 2);
v___x_1507_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1351_, 2);
v___x_1508_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1507_, v_env_1351_);
v_sz_1509_ = lean_array_size(v___x_1508_);
lean_inc(v_keyName_1373_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1351_, v_opts_1352_, v_keyName_1373_, v_sz_1509_, v___x_1377_, v___x_1508_, v_a_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1568_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_a_1512_ = lean_ctor_get(v___x_1510_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1514_ = v___x_1510_;
v_isShared_1515_ = v_isSharedCheck_1568_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1568_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; size_t v_sz_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1516_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1351_, 2);
v___x_1517_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1516_, v_env_1351_);
v_sz_1518_ = lean_array_size(v___x_1517_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1351_, v_opts_1352_, v_sz_1518_, v___x_1377_, v___x_1517_);
v___x_1520_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1519_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; size_t v_sz_1524_; lean_object* v___x_1525_; 
lean_del_object(v___x_1514_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1351_);
v___x_1523_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1522_, v_env_1351_);
v_sz_1524_ = lean_array_size(v___x_1523_);
lean_inc_ref(v___x_1412_);
lean_inc(v_a_1371_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1371_, v_a_1499_, v___x_1412_, v_sz_1524_, v___x_1377_, v___x_1523_, v_a_1512_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
v_a_1527_ = lean_ctor_get(v___x_1525_, 1);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1525_, 2);
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_array_get_size(v_a_1526_);
v___x_1530_ = lean_nat_dec_lt(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_nat_dec_lt(v___x_1416_, v___x_1529_);
if (v___x_1531_ == 0)
{
lean_object* v_testDriver_1532_; 
lean_dec(v_a_1526_);
v_testDriver_1532_ = lean_ctor_get(v_config_1374_, 12);
lean_inc_ref(v_testDriver_1532_);
v___y_1443_ = v___x_1528_;
v___y_1444_ = v_a_1495_;
v___y_1445_ = v___y_1489_;
v___y_1446_ = v_a_1499_;
v___y_1447_ = v_a_1521_;
v___y_1448_ = v_a_1505_;
v___y_1449_ = v_a_1511_;
v_a_1450_ = v_testDriver_1532_;
v_a_1451_ = v_a_1527_;
goto v___jp_1442_;
}
else
{
lean_object* v_testDriver_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_testDriver_1533_ = lean_ctor_get(v_config_1374_, 12);
v___x_1534_ = lean_string_utf8_byte_size(v_testDriver_1533_);
v___x_1535_ = lean_nat_dec_eq(v___x_1534_, v___x_1416_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_a_1526_);
lean_dec(v_a_1521_);
lean_dec(v_a_1511_);
lean_dec(v_a_1505_);
lean_dec(v_a_1499_);
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v___x_1536_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1537_ = lean_string_append(v___x_1412_, v___x_1536_);
v___x_1538_ = 3;
v___x_1539_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*1, v___x_1538_);
v___x_1540_ = lean_array_get_size(v_a_1527_);
v___x_1541_ = lean_array_push(v_a_1527_, v___x_1539_);
v_a_1356_ = v___x_1540_;
v_a_1357_ = v___x_1541_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_array_fget(v_a_1526_, v___x_1416_);
lean_dec(v_a_1526_);
v___x_1543_ = l_Lean_Name_toString(v___x_1542_, v___x_1535_);
v___y_1443_ = v___x_1528_;
v___y_1444_ = v_a_1495_;
v___y_1445_ = v___y_1489_;
v___y_1446_ = v_a_1499_;
v___y_1447_ = v_a_1521_;
v___y_1448_ = v_a_1505_;
v___y_1449_ = v_a_1511_;
v_a_1450_ = v___x_1543_;
v_a_1451_ = v_a_1527_;
goto v___jp_1442_;
}
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_a_1526_);
lean_dec(v_a_1521_);
lean_dec(v_a_1511_);
lean_dec(v_a_1505_);
lean_dec(v_a_1499_);
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v___x_1544_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1545_ = lean_string_append(v___x_1412_, v___x_1544_);
v___x_1546_ = 3;
v___x_1547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*1, v___x_1546_);
v___x_1548_ = lean_array_get_size(v_a_1527_);
v___x_1549_ = lean_array_push(v_a_1527_, v___x_1547_);
v_a_1356_ = v___x_1548_;
v_a_1357_ = v___x_1549_;
goto v___jp_1355_;
}
}
else
{
lean_object* v_a_1550_; lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_a_1521_);
lean_dec(v_a_1511_);
lean_dec(v_a_1505_);
lean_dec(v_a_1499_);
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1550_ = lean_ctor_get(v___x_1525_, 0);
v_a_1551_ = lean_ctor_get(v___x_1525_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1525_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_inc(v_a_1550_);
lean_dec(v___x_1525_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1550_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_dec(v_a_1511_);
lean_dec(v_a_1505_);
lean_dec(v_a_1499_);
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1559_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1560_ = lean_io_error_to_string(v_a_1559_);
v___x_1561_ = 3;
v___x_1562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*1, v___x_1561_);
v___x_1563_ = lean_array_get_size(v_a_1512_);
v___x_1564_ = lean_array_push(v_a_1512_, v___x_1562_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 1, v___x_1564_);
lean_ctor_set(v___x_1514_, 0, v___x_1563_);
v___x_1566_ = v___x_1514_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_a_1505_);
lean_dec(v_a_1499_);
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1569_ = lean_ctor_get(v___x_1510_, 0);
v_a_1570_ = lean_ctor_get(v___x_1510_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1510_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_inc(v_a_1569_);
lean_dec(v___x_1510_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1569_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1499_);
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1578_ = lean_ctor_get(v___x_1504_, 0);
v_a_1579_ = lean_ctor_get(v___x_1504_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1504_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_inc(v_a_1578_);
lean_dec(v___x_1504_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1578_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_a_1495_);
lean_dec(v___y_1489_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1587_ = lean_ctor_get(v___x_1498_, 0);
v_a_1588_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1498_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_inc(v_a_1587_);
lean_dec(v___x_1498_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1587_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v___y_1489_);
lean_dec_ref(v___f_1414_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1596_ = lean_ctor_get(v___x_1494_, 0);
v_a_1597_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1494_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_inc(v_a_1596_);
lean_dec(v___x_1494_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1596_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
v___jp_1605_:
{
if (lean_obj_tag(v___y_1607_) == 0)
{
lean_object* v_a_1608_; 
v_a_1608_ = lean_ctor_get(v___y_1607_, 1);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___y_1607_, 2);
v___y_1489_ = v___y_1606_;
v_a_1490_ = v_a_1608_;
goto v___jp_1488_;
}
else
{
lean_object* v_a_1609_; lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v___y_1606_);
lean_dec_ref(v___f_1414_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1609_ = lean_ctor_get(v___y_1607_, 0);
v_a_1610_ = lean_ctor_get(v___y_1607_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___y_1607_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___y_1607_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_inc(v_a_1609_);
lean_dec(v___y_1607_);
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
v___jp_1619_:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_nat_dec_lt(v___x_1416_, v___x_1618_);
if (v___x_1622_ == 0)
{
v___y_1489_ = v_a_1620_;
v_a_1490_ = v_a_1621_;
goto v___jp_1488_;
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_le(v___x_1618_, v___x_1618_);
if (v___x_1623_ == 0)
{
if (v___x_1622_ == 0)
{
v___y_1489_ = v_a_1620_;
v_a_1490_ = v_a_1621_;
goto v___jp_1488_;
}
else
{
size_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_usize_of_nat(v___x_1618_);
lean_inc_ref(v___x_1412_);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1412_, v_a_1379_, v___x_1377_, v___x_1624_, v___x_1415_, v_a_1621_);
v___y_1606_ = v_a_1620_;
v___y_1607_ = v___x_1625_;
goto v___jp_1605_;
}
}
else
{
size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_usize_of_nat(v___x_1618_);
lean_inc_ref(v___x_1412_);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1412_, v_a_1379_, v___x_1377_, v___x_1626_, v___x_1415_, v_a_1621_);
v___y_1606_ = v_a_1620_;
v___y_1607_ = v___x_1627_;
goto v___jp_1605_;
}
}
}
v___jp_1628_:
{
if (lean_obj_tag(v___y_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v_a_1631_; 
v_a_1630_ = lean_ctor_get(v___y_1629_, 0);
lean_inc(v_a_1630_);
v_a_1631_ = lean_ctor_get(v___y_1629_, 1);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___y_1629_, 2);
v_a_1620_ = v_a_1630_;
v_a_1621_ = v_a_1631_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1632_; lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v___f_1414_);
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1379_);
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1632_ = lean_ctor_get(v___y_1629_, 0);
v_a_1633_ = lean_ctor_get(v___y_1629_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___y_1629_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___y_1629_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_inc(v_a_1632_);
lean_dec(v___y_1629_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1632_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1371_);
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1648_ = lean_ctor_get(v___x_1378_, 0);
v_a_1649_ = lean_ctor_get(v___x_1378_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1378_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_inc(v_a_1648_);
lean_dec(v___x_1378_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1648_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v_a_1365_);
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1657_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1370_, 1);
v___x_1658_ = lean_io_error_to_string(v_a_1657_);
v___x_1659_ = 3;
v___x_1660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set_uint8(v___x_1660_, sizeof(void*)*1, v___x_1659_);
v___x_1661_ = lean_array_get_size(v_a_1353_);
v___x_1662_ = lean_array_push(v_a_1353_, v___x_1660_);
v___x_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
return v___x_1663_;
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v_opts_1352_);
lean_dec_ref(v_env_1351_);
v_a_1664_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1665_ = lean_io_error_to_string(v_a_1664_);
v___x_1666_ = 3;
v___x_1667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*1, v___x_1666_);
v___x_1668_ = lean_array_get_size(v_a_1353_);
v___x_1669_ = lean_array_push(v_a_1353_, v___x_1667_);
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
return v___x_1670_;
}
v___jp_1355_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1356_);
lean_ctor_set(v___x_1358_, 1, v_a_1357_);
return v___x_1358_;
}
v___jp_1359_:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1360_);
lean_ctor_set(v___x_1362_, 1, v_a_1361_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1671_, lean_object* v_opts_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1671_, v_opts_1672_, v_a_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1676_, lean_object* v_env_1677_, lean_object* v_attr_1678_, lean_object* v_f_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1677_, v_attr_1678_, v_f_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_env_1682_, lean_object* v_attr_1683_, lean_object* v_f_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1681_, v_env_1682_, v_attr_1683_, v_f_1684_);
lean_dec_ref(v_attr_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1686_, lean_object* v_inst_1687_, lean_object* v_t_1688_, lean_object* v_k_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_1688_, v_k_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1691_, lean_object* v_inst_1692_, lean_object* v_t_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1691_, v_inst_1692_, v_t_1693_, v_k_1694_);
lean_dec(v_k_1694_);
lean_dec(v_t_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v_00_u03b2_1696_, lean_object* v_k_1697_, lean_object* v_v_1698_, lean_object* v_t_1699_, lean_object* v_hl_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1697_, v_v_1698_, v_t_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1702_, lean_object* v_t_1703_, lean_object* v_k_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1703_, v_k_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1706_, lean_object* v_t_1707_, lean_object* v_k_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1706_, v_t_1707_, v_k_1708_);
lean_dec(v_k_1708_);
lean_dec(v_t_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1710_, lean_object* v_env_1711_, lean_object* v_attr_1712_, lean_object* v_f_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1711_, v_attr_1712_, v_f_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1717_, lean_object* v_env_1718_, lean_object* v_attr_1719_, lean_object* v_f_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1717_, v_env_1718_, v_attr_1719_, v_f_1720_, v___y_1721_);
lean_dec_ref(v_attr_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_1724_, lean_object* v___x_1725_, lean_object* v_as_1726_, size_t v_i_1727_, size_t v_stop_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1724_, v_as_1726_, v_i_1727_, v_stop_1728_, v_b_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v_as_1735_, lean_object* v_i_1736_, lean_object* v_stop_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
size_t v_i_boxed_1741_; size_t v_stop_boxed_1742_; lean_object* v_res_1743_; 
v_i_boxed_1741_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_stop_boxed_1742_ = lean_unbox_usize(v_stop_1737_);
lean_dec(v_stop_1737_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1733_, v___x_1734_, v_as_1735_, v_i_boxed_1741_, v_stop_boxed_1742_, v_b_1738_, v___y_1739_);
lean_dec_ref(v_as_1735_);
lean_dec(v___x_1734_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(lean_object* v_00_u03b2_1744_, lean_object* v_f_1745_, lean_object* v_as_1746_, size_t v_i_1747_, size_t v_stop_1748_, lean_object* v_b_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_1745_, v_as_1746_, v_i_1747_, v_stop_1748_, v_b_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1751_, lean_object* v_f_1752_, lean_object* v_as_1753_, lean_object* v_i_1754_, lean_object* v_stop_1755_, lean_object* v_b_1756_){
_start:
{
size_t v_i_boxed_1757_; size_t v_stop_boxed_1758_; lean_object* v_res_1759_; 
v_i_boxed_1757_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_stop_boxed_1758_ = lean_unbox_usize(v_stop_1755_);
lean_dec(v_stop_1755_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(v_00_u03b2_1751_, v_f_1752_, v_as_1753_, v_i_boxed_1757_, v_stop_boxed_1758_, v_b_1756_);
lean_dec_ref(v_as_1753_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1760_, lean_object* v_f_1761_, lean_object* v_as_1762_, size_t v_i_1763_, size_t v_stop_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1761_, v_as_1762_, v_i_1763_, v_stop_1764_, v_b_1765_, v___y_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1769_, lean_object* v_f_1770_, lean_object* v_as_1771_, lean_object* v_i_1772_, lean_object* v_stop_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
size_t v_i_boxed_1777_; size_t v_stop_boxed_1778_; lean_object* v_res_1779_; 
v_i_boxed_1777_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_stop_boxed_1778_ = lean_unbox_usize(v_stop_1773_);
lean_dec(v_stop_1773_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1769_, v_f_1770_, v_as_1771_, v_i_boxed_1777_, v_stop_boxed_1778_, v_b_1774_, v___y_1775_);
lean_dec_ref(v_as_1771_);
return v_res_1779_;
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
