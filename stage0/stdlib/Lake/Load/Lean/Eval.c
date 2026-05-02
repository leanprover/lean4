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
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
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
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
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
lean_dec_ref(v___x_28_);
v___x_37_ = l_Lean_ConstantInfo_type(v_val_36_);
lean_dec(v_val_36_);
if (lean_obj_tag(v___x_37_) == 4)
{
lean_object* v_declName_38_; uint8_t v___x_39_; 
v_declName_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_declName_38_);
lean_dec_ref(v___x_37_);
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
lean_dec_ref(v___x_238_);
v___x_242_ = l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
v___x_243_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_234_, v_opts_235_, v___x_242_, v_head_241_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
lean_dec(v_tail_240_);
lean_dec_ref(v___x_238_);
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
lean_object* v_a_300_; uint8_t v___x_301_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_299_);
v___x_301_ = 1;
v___x_302_ = l_Lean_findDocString_x3f(v_env_290_, v_scriptName_294_, v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref(v___x_302_);
v___x_304_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0));
v___x_305_ = lean_string_append(v___x_293_, v___x_304_);
v___x_306_ = lean_string_append(v___x_305_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_a_300_);
lean_ctor_set(v___x_307_, 2, v_a_303_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___y_295_);
return v___x_308_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_a_300_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_293_);
v_a_309_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_302_);
v___x_310_ = lean_io_error_to_string(v_a_309_);
v___x_311_ = 3;
v___x_312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_311_);
v___x_313_ = lean_array_get_size(v___y_295_);
v___x_314_ = lean_array_push(v___y_295_, v___x_312_);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v___x_297_);
lean_dec(v_scriptName_294_);
lean_dec_ref(v___x_293_);
lean_dec_ref(v_env_290_);
v_a_316_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_316_);
lean_dec_ref(v___x_299_);
v___x_317_ = lean_io_error_to_string(v_a_316_);
v___x_318_ = 3;
v___x_319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*1, v___x_318_);
v___x_320_ = lean_array_get_size(v___y_295_);
v___x_321_ = lean_array_push(v___y_295_, v___x_319_);
v___x_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object* v___x_323_, lean_object* v_env_324_, lean_object* v_opts_325_, lean_object* v___x_326_, lean_object* v___x_327_, lean_object* v_scriptName_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_50967__boxed_331_; lean_object* v_res_332_; 
v___x_50967__boxed_331_ = lean_unbox(v___x_323_);
v_res_332_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_50967__boxed_331_, v_env_324_, v_opts_325_, v___x_326_, v___x_327_, v_scriptName_328_, v___y_329_);
lean_dec_ref(v_opts_325_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object* v_env_335_, lean_object* v_opts_336_, lean_object* v___x_337_, size_t v_sz_338_, size_t v_i_339_, lean_object* v_bs_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_a_344_; lean_object* v_a_345_; uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec(v___x_337_);
lean_dec_ref(v_env_335_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_bs_340_);
lean_ctor_set(v___x_348_, 1, v___y_341_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v_v_350_; lean_object* v___x_351_; 
v___x_349_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_350_ = lean_array_uget_borrowed(v_bs_340_, v_i_339_);
lean_inc(v_v_350_);
lean_inc_ref(v_env_335_);
v___x_351_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_335_, v_opts_336_, v___x_349_, v_v_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec_ref(v_bs_340_);
lean_dec(v___x_337_);
lean_dec_ref(v_env_335_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = 3;
v___x_354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_354_, 0, v_a_352_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_353_);
v___x_355_ = lean_array_get_size(v___y_341_);
v___x_356_ = lean_array_push(v___y_341_, v___x_354_);
v_a_344_ = v___x_355_;
v_a_345_ = v___x_356_;
goto v___jp_343_;
}
else
{
lean_object* v_a_357_; lean_object* v_pkg_358_; lean_object* v_fn_359_; uint8_t v___x_360_; 
v_a_357_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_351_);
v_pkg_358_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_pkg_358_);
v_fn_359_ = lean_ctor_get(v_a_357_, 1);
lean_inc_ref(v_fn_359_);
lean_dec(v_a_357_);
v___x_360_ = lean_name_eq(v_pkg_358_, v___x_337_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v_fn_359_);
lean_dec_ref(v_bs_340_);
lean_dec_ref(v_env_335_);
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0));
v___x_362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_358_, v___x_347_);
v___x_363_ = lean_string_append(v___x_361_, v___x_362_);
lean_dec_ref(v___x_362_);
v___x_364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1));
v___x_365_ = lean_string_append(v___x_363_, v___x_364_);
v___x_366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_337_, v___x_347_);
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
lean_dec_ref(v___x_366_);
v___x_368_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
v___x_370_ = 3;
v___x_371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
v___x_372_ = lean_array_get_size(v___y_341_);
v___x_373_ = lean_array_push(v___y_341_, v___x_371_);
v_a_344_ = v___x_372_;
v_a_345_ = v___x_373_;
goto v___jp_343_;
}
else
{
lean_object* v___x_374_; lean_object* v_bs_x27_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
lean_dec(v_pkg_358_);
v___x_374_ = lean_unsigned_to_nat(0u);
v_bs_x27_375_ = lean_array_uset(v_bs_340_, v_i_339_, v___x_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_339_, v___x_376_);
v___x_378_ = lean_array_uset(v_bs_x27_375_, v_i_339_, v_fn_359_);
v_i_339_ = v___x_377_;
v_bs_340_ = v___x_378_;
goto _start;
}
}
}
v___jp_343_:
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v_a_344_);
lean_ctor_set(v___x_346_, 1, v_a_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object* v_env_380_, lean_object* v_opts_381_, lean_object* v___x_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_bs_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
size_t v_sz_boxed_388_; size_t v_i_boxed_389_; lean_object* v_res_390_; 
v_sz_boxed_388_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_389_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_380_, v_opts_381_, v___x_382_, v_sz_boxed_388_, v_i_boxed_389_, v_bs_385_, v___y_386_);
lean_dec_ref(v_opts_381_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object* v___x_394_, size_t v_sz_395_, size_t v_i_396_, lean_object* v_bs_397_, lean_object* v___y_398_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_lt(v_i_396_, v_sz_395_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec(v___x_394_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_bs_397_);
lean_ctor_set(v___x_401_, 1, v___y_398_);
return v___x_401_;
}
else
{
lean_object* v_v_402_; lean_object* v_pkg_403_; lean_object* v_name_404_; uint8_t v___x_405_; 
v_v_402_ = lean_array_uget(v_bs_397_, v_i_396_);
v_pkg_403_ = lean_ctor_get(v_v_402_, 0);
v_name_404_ = lean_ctor_get(v_v_402_, 1);
v___x_405_ = lean_name_eq(v_pkg_403_, v___x_394_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_inc(v_name_404_);
lean_inc(v_pkg_403_);
lean_dec(v_v_402_);
lean_dec_ref(v_bs_397_);
v___x_406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0));
v___x_407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_404_, v___x_400_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1));
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
v___x_411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_403_, v___x_400_);
v___x_412_ = lean_string_append(v___x_410_, v___x_411_);
lean_dec_ref(v___x_411_);
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2));
v___x_414_ = lean_string_append(v___x_412_, v___x_413_);
v___x_415_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_394_, v___x_400_);
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
lean_dec_ref(v___x_415_);
v___x_417_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_418_ = lean_string_append(v___x_416_, v___x_417_);
v___x_419_ = 3;
v___x_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
v___x_421_ = lean_array_get_size(v___y_398_);
v___x_422_ = lean_array_push(v___y_398_, v___x_420_);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v_bs_x27_425_; size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v_bs_x27_425_ = lean_array_uset(v_bs_397_, v_i_396_, v___x_424_);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_396_, v___x_426_);
v___x_428_ = lean_array_uset(v_bs_x27_425_, v_i_396_, v_v_402_);
v_i_396_ = v___x_427_;
v_bs_397_ = v___x_428_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___boxed(lean_object* v___x_430_, lean_object* v_sz_431_, lean_object* v_i_432_, lean_object* v_bs_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
size_t v_sz_boxed_436_; size_t v_i_boxed_437_; lean_object* v_res_438_; 
v_sz_boxed_436_ = lean_unbox_usize(v_sz_431_);
lean_dec(v_sz_431_);
v_i_boxed_437_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v___x_430_, v_sz_boxed_436_, v_i_boxed_437_, v_bs_433_, v___y_434_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object* v_t_439_, lean_object* v_k_440_){
_start:
{
if (lean_obj_tag(v_t_439_) == 0)
{
lean_object* v_k_441_; lean_object* v_v_442_; lean_object* v_l_443_; lean_object* v_r_444_; uint8_t v___x_445_; 
v_k_441_ = lean_ctor_get(v_t_439_, 1);
v_v_442_ = lean_ctor_get(v_t_439_, 2);
v_l_443_ = lean_ctor_get(v_t_439_, 3);
v_r_444_ = lean_ctor_get(v_t_439_, 4);
v___x_445_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_440_, v_k_441_);
switch(v___x_445_)
{
case 0:
{
v_t_439_ = v_l_443_;
goto _start;
}
case 1:
{
lean_object* v___x_447_; 
lean_inc(v_v_442_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_v_442_);
return v___x_447_;
}
default: 
{
v_t_439_ = v_r_444_;
goto _start;
}
}
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_box(0);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_450_, lean_object* v_k_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_450_, v_k_451_);
lean_dec(v_k_451_);
lean_dec(v_t_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object* v_a_455_, lean_object* v___x_456_, size_t v_sz_457_, size_t v_i_458_, lean_object* v_bs_459_, lean_object* v___y_460_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_usize_dec_lt(v_i_458_, v_sz_457_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec_ref(v___x_456_);
lean_dec_ref(v_a_455_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_bs_459_);
lean_ctor_set(v___x_463_, 1, v___y_460_);
return v___x_463_;
}
else
{
lean_object* v_toTreeMap_464_; lean_object* v_v_465_; lean_object* v___x_466_; 
v_toTreeMap_464_ = lean_ctor_get(v_a_455_, 0);
v_v_465_ = lean_array_uget_borrowed(v_bs_459_, v_i_458_);
v___x_466_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_464_, v_v_465_);
if (lean_obj_tag(v___x_466_) == 1)
{
lean_object* v_val_467_; lean_object* v_name_468_; lean_object* v___x_469_; lean_object* v_bs_x27_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v_val_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref(v___x_466_);
v_name_468_ = lean_ctor_get(v_val_467_, 1);
lean_inc(v_name_468_);
lean_dec(v_val_467_);
v___x_469_ = lean_unsigned_to_nat(0u);
v_bs_x27_470_ = lean_array_uset(v_bs_459_, v_i_458_, v___x_469_);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_458_, v___x_471_);
v___x_473_ = lean_array_uset(v_bs_x27_470_, v_i_458_, v_name_468_);
v_i_458_ = v___x_472_;
v_bs_459_ = v___x_473_;
goto _start;
}
else
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_491_; 
lean_inc(v_v_465_);
lean_dec(v___x_466_);
lean_dec_ref(v_bs_459_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_a_455_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_a_455_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_a_455_, 0);
lean_dec(v_unused_493_);
v___x_476_ = v_a_455_;
v_isShared_477_ = v_isSharedCheck_491_;
goto v_resetjp_475_;
}
else
{
lean_dec(v_a_455_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_491_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0));
v___x_479_ = lean_string_append(v___x_456_, v___x_478_);
v___x_480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_465_, v___x_462_);
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = 3;
v___x_485_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*1, v___x_484_);
v___x_486_ = lean_array_get_size(v___y_460_);
v___x_487_ = lean_array_push(v___y_460_, v___x_485_);
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 1);
lean_ctor_set(v___x_476_, 1, v___x_487_);
lean_ctor_set(v___x_476_, 0, v___x_486_);
v___x_489_ = v___x_476_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object* v_a_494_, lean_object* v___x_495_, lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_bs_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
size_t v_sz_boxed_501_; size_t v_i_boxed_502_; lean_object* v_res_503_; 
v_sz_boxed_501_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_502_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_494_, v___x_495_, v_sz_boxed_501_, v_i_boxed_502_, v_bs_498_, v___y_499_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(lean_object* v_f_504_, lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_, lean_object* v_b_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
lean_inc_ref(v_f_504_);
lean_inc(v___x_510_);
v___x_511_ = lean_apply_1(v_f_504_, v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_b_508_);
lean_dec_ref(v_f_504_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; size_t v___x_523_; size_t v___x_524_; 
v_a_520_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_511_);
v___x_521_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_510_);
v___x_522_ = l_Lake_RBArray_insert___redArg(v___x_521_, v_b_508_, v___x_510_, v_a_520_);
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_add(v_i_506_, v___x_523_);
v_i_506_ = v___x_524_;
v_b_508_ = v___x_522_;
goto _start;
}
}
else
{
lean_object* v___x_526_; 
lean_dec_ref(v_f_504_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_b_508_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_527_, lean_object* v_as_528_, lean_object* v_i_529_, lean_object* v_stop_530_, lean_object* v_b_531_){
_start:
{
size_t v_i_boxed_532_; size_t v_stop_boxed_533_; lean_object* v_res_534_; 
v_i_boxed_532_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_stop_boxed_533_ = lean_unbox_usize(v_stop_530_);
lean_dec(v_stop_530_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_527_, v_as_528_, v_i_boxed_532_, v_stop_boxed_533_, v_b_531_);
lean_dec_ref(v_as_528_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object* v_env_535_, lean_object* v_attr_536_, lean_object* v_f_537_){
_start:
{
lean_object* v_entries_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_entries_538_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_536_, v_env_535_);
v___x_539_ = lean_array_get_size(v_entries_538_);
v___x_540_ = l_Lake_RBArray_mkEmpty___redArg(v___x_539_);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_nat_dec_lt(v___x_541_, v___x_539_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_dec_ref(v_entries_538_);
lean_dec_ref(v_f_537_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_540_);
return v___x_543_;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_le(v___x_539_, v___x_539_);
if (v___x_544_ == 0)
{
if (v___x_542_ == 0)
{
lean_object* v___x_545_; 
lean_dec_ref(v_entries_538_);
lean_dec_ref(v_f_537_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_540_);
return v___x_545_;
}
else
{
size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v___x_546_ = ((size_t)0ULL);
v___x_547_ = lean_usize_of_nat(v___x_539_);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_537_, v_entries_538_, v___x_546_, v___x_547_, v___x_540_);
lean_dec_ref(v_entries_538_);
return v___x_548_;
}
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_539_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_537_, v_entries_538_, v___x_549_, v___x_550_, v___x_540_);
lean_dec_ref(v_entries_538_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_env_552_, lean_object* v_attr_553_, lean_object* v_f_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_552_, v_attr_553_, v_f_554_);
lean_dec_ref(v_attr_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_556_, lean_object* v_as_557_, size_t v_i_558_, size_t v_stop_559_, lean_object* v_b_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_eq(v_i_558_, v_stop_559_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_array_uget_borrowed(v_as_557_, v_i_558_);
lean_inc_ref(v_f_556_);
lean_inc(v___x_564_);
v___x_565_ = lean_apply_3(v_f_556_, v___x_564_, v___y_561_, lean_box(0));
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
v_a_567_ = lean_ctor_get(v___x_565_, 1);
lean_inc(v_a_567_);
lean_dec_ref(v___x_565_);
lean_inc(v___x_564_);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_564_, v_a_566_, v_b_560_);
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_558_, v___x_569_);
v_i_558_ = v___x_570_;
v_b_560_ = v___x_568_;
v___y_561_ = v_a_567_;
goto _start;
}
else
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_b_560_);
lean_dec_ref(v_f_556_);
v_a_572_ = lean_ctor_get(v___x_565_, 0);
v_a_573_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_565_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_inc(v_a_572_);
lean_dec(v___x_565_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_572_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v___x_581_; 
lean_dec_ref(v_f_556_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_b_560_);
lean_ctor_set(v___x_581_, 1, v___y_561_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_582_, lean_object* v_as_583_, lean_object* v_i_584_, lean_object* v_stop_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
size_t v_i_boxed_589_; size_t v_stop_boxed_590_; lean_object* v_res_591_; 
v_i_boxed_589_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_stop_boxed_590_ = lean_unbox_usize(v_stop_585_);
lean_dec(v_stop_585_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_582_, v_as_583_, v_i_boxed_589_, v_stop_boxed_590_, v_b_586_, v___y_587_);
lean_dec_ref(v_as_583_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_592_, lean_object* v_attr_593_, lean_object* v_f_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_entries_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_entries_597_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_593_, v_env_592_);
v___x_598_ = lean_box(1);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_get_size(v_entries_597_);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_entries_597_);
lean_dec_ref(v_f_594_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_598_);
lean_ctor_set(v___x_602_, 1, v___y_595_);
return v___x_602_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = lean_nat_dec_le(v___x_600_, v___x_600_);
if (v___x_603_ == 0)
{
if (v___x_601_ == 0)
{
lean_object* v___x_604_; 
lean_dec_ref(v_entries_597_);
lean_dec_ref(v_f_594_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_598_);
lean_ctor_set(v___x_604_, 1, v___y_595_);
return v___x_604_;
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((size_t)0ULL);
v___x_606_ = lean_usize_of_nat(v___x_600_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_594_, v_entries_597_, v___x_605_, v___x_606_, v___x_598_, v___y_595_);
lean_dec_ref(v_entries_597_);
return v___x_607_;
}
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_600_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_594_, v_entries_597_, v___x_608_, v___x_609_, v___x_598_, v___y_595_);
lean_dec_ref(v_entries_597_);
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_611_, lean_object* v_attr_612_, lean_object* v_f_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_611_, v_attr_612_, v_f_613_, v___y_614_);
lean_dec_ref(v_attr_612_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_617_, lean_object* v_opts_618_, lean_object* v_as_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_b_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
lean_dec_ref(v_env_617_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_b_622_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v_a_626_; lean_object* v___x_627_; 
v___x_625_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
v_a_626_ = lean_array_uget_borrowed(v_as_619_, v_i_621_);
lean_inc(v_a_626_);
lean_inc_ref(v_env_617_);
v___x_627_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_617_, v_opts_618_, v___x_625_, v_a_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_b_622_);
lean_dec_ref(v_env_617_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_a_636_; lean_object* v_name_637_; lean_object* v_config_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_649_; 
v_a_636_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_627_);
v_name_637_ = lean_ctor_get(v_a_636_, 0);
v_config_638_ = lean_ctor_get(v_a_636_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_636_);
if (v_isSharedCheck_649_ == 0)
{
v___x_640_ = v_a_636_;
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_config_638_);
lean_inc(v_name_637_);
lean_dec(v_a_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_name_637_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_config_638_);
v___x_643_ = v_reuseFailAlloc_648_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; 
v___x_644_ = lean_array_push(v_b_622_, v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_621_, v___x_645_);
v_i_621_ = v___x_646_;
v_b_622_ = v___x_644_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object* v_env_650_, lean_object* v_opts_651_, lean_object* v_as_652_, lean_object* v_sz_653_, lean_object* v_i_654_, lean_object* v_b_655_){
_start:
{
size_t v_sz_boxed_656_; size_t v_i_boxed_657_; lean_object* v_res_658_; 
v_sz_boxed_656_ = lean_unbox_usize(v_sz_653_);
lean_dec(v_sz_653_);
v_i_boxed_657_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_650_, v_opts_651_, v_as_652_, v_sz_boxed_656_, v_i_boxed_657_, v_b_655_);
lean_dec_ref(v_as_652_);
lean_dec_ref(v_opts_651_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v___x_662_, lean_object* v_as_663_, size_t v_i_664_, size_t v_stop_665_, lean_object* v_b_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_a_670_; lean_object* v_a_671_; uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_eq(v_i_664_, v_stop_665_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v_name_677_; lean_object* v_kind_678_; lean_object* v_config_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_676_ = lean_array_uget_borrowed(v_as_663_, v_i_664_);
v_name_677_ = lean_ctor_get(v___x_676_, 1);
v_kind_678_ = lean_ctor_get(v___x_676_, 2);
v_config_679_ = lean_ctor_get(v___x_676_, 3);
v___x_680_ = l_Lake_LeanExe_keyword;
v___x_681_ = lean_name_eq(v_kind_678_, v___x_680_);
if (v___x_681_ == 0)
{
v_a_670_ = v_b_666_;
v_a_671_ = v___y_667_;
goto v___jp_669_;
}
else
{
lean_object* v_root_682_; lean_object* v___x_683_; 
v_root_682_ = lean_ctor_get(v_config_679_, 2);
v___x_683_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_666_, v_root_682_);
if (lean_obj_tag(v___x_683_) == 1)
{
lean_object* v_val_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_b_666_);
v_val_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___x_683_);
v___x_685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0));
v___x_686_ = lean_string_append(v___x_662_, v___x_685_);
lean_inc(v_name_677_);
v___x_687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_677_, v___x_681_);
v___x_688_ = lean_string_append(v___x_686_, v___x_687_);
lean_dec_ref(v___x_687_);
v___x_689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1));
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
lean_inc(v_root_682_);
v___x_691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_682_, v___x_681_);
v___x_692_ = lean_string_append(v___x_690_, v___x_691_);
lean_dec_ref(v___x_691_);
v___x_693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2));
v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
v___x_695_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_684_, v___x_681_);
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
lean_dec_ref(v___x_695_);
v___x_697_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
v___x_699_ = 3;
v___x_700_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*1, v___x_699_);
v___x_701_ = lean_array_get_size(v___y_667_);
v___x_702_ = lean_array_push(v___y_667_, v___x_700_);
v___x_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec(v___x_683_);
lean_inc(v_name_677_);
lean_inc(v_root_682_);
v___x_704_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_682_, v_name_677_, v_b_666_);
v_a_670_ = v___x_704_;
v_a_671_ = v___y_667_;
goto v___jp_669_;
}
}
}
else
{
lean_object* v___x_705_; 
lean_dec_ref(v___x_662_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_b_666_);
lean_ctor_set(v___x_705_, 1, v___y_667_);
return v___x_705_;
}
v___jp_669_:
{
size_t v___x_672_; size_t v___x_673_; 
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_664_, v___x_672_);
v_i_664_ = v___x_673_;
v_b_666_ = v_a_670_;
v___y_667_ = v_a_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v___x_706_, lean_object* v_as_707_, lean_object* v_i_708_, lean_object* v_stop_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
size_t v_i_boxed_713_; size_t v_stop_boxed_714_; lean_object* v_res_715_; 
v_i_boxed_713_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_stop_boxed_714_ = lean_unbox_usize(v_stop_709_);
lean_dec(v_stop_709_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_706_, v_as_707_, v_i_boxed_713_, v_stop_boxed_714_, v_b_710_, v___y_711_);
lean_dec_ref(v_as_707_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v___x_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_bs_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v___x_720_);
lean_dec_ref(v_a_718_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_bs_723_);
lean_ctor_set(v___x_727_, 1, v___y_724_);
return v___x_727_;
}
else
{
lean_object* v_toTreeMap_728_; lean_object* v_v_729_; lean_object* v___x_730_; lean_object* v_bs_x27_731_; lean_object* v_a_733_; lean_object* v_a_734_; lean_object* v___x_739_; 
v_toTreeMap_728_ = lean_ctor_get(v_a_718_, 0);
v_v_729_ = lean_array_uget(v_bs_723_, v_i_722_);
v___x_730_ = lean_unsigned_to_nat(0u);
v_bs_x27_731_ = lean_array_uset(v_bs_723_, v_i_722_, v___x_730_);
v___x_739_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_728_, v_v_729_);
if (lean_obj_tag(v___x_739_) == 1)
{
lean_object* v_val_740_; lean_object* v_name_741_; 
lean_dec(v_v_729_);
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v___x_739_);
v_name_741_ = lean_ctor_get(v_val_740_, 1);
lean_inc(v_name_741_);
lean_dec(v_val_740_);
v_a_733_ = v_name_741_;
v_a_734_ = v___y_724_;
goto v___jp_732_;
}
else
{
uint8_t v___x_742_; 
lean_dec(v___x_739_);
v___x_742_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_729_, v_a_719_);
if (v___x_742_ == 0)
{
lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v_bs_x27_731_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_718_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_760_ = lean_ctor_get(v_a_718_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_a_718_, 0);
lean_dec(v_unused_761_);
v___x_744_ = v_a_718_;
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
else
{
lean_dec(v_a_718_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_747_ = lean_string_append(v___x_720_, v___x_746_);
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_729_, v___x_726_);
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
v___x_752_ = 3;
v___x_753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*1, v___x_752_);
v___x_754_ = lean_array_get_size(v___y_724_);
v___x_755_ = lean_array_push(v___y_724_, v___x_753_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 1);
lean_ctor_set(v___x_744_, 1, v___x_755_);
lean_ctor_set(v___x_744_, 0, v___x_754_);
v___x_757_ = v___x_744_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
v_a_733_ = v_v_729_;
v_a_734_ = v___y_724_;
goto v___jp_732_;
}
}
v___jp_732_:
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_722_, v___x_735_);
v___x_737_ = lean_array_uset(v_bs_x27_731_, v_i_722_, v_a_733_);
v_i_722_ = v___x_736_;
v_bs_723_ = v___x_737_;
v___y_724_ = v_a_734_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v___x_764_, lean_object* v_sz_765_, lean_object* v_i_766_, lean_object* v_bs_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_771_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_762_, v_a_763_, v___x_764_, v_sz_boxed_770_, v_i_boxed_771_, v_bs_767_, v___y_768_);
lean_dec(v_a_763_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v___x_776_, size_t v_sz_777_, size_t v_i_778_, lean_object* v_bs_779_, lean_object* v___y_780_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = lean_usize_dec_lt(v_i_778_, v_sz_777_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec_ref(v___x_776_);
lean_dec_ref(v_a_774_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_bs_779_);
lean_ctor_set(v___x_783_, 1, v___y_780_);
return v___x_783_;
}
else
{
lean_object* v_toTreeMap_784_; lean_object* v_v_785_; lean_object* v___x_786_; lean_object* v_bs_x27_787_; lean_object* v_a_789_; lean_object* v_a_790_; lean_object* v___x_795_; 
v_toTreeMap_784_ = lean_ctor_get(v_a_774_, 0);
v_v_785_ = lean_array_uget(v_bs_779_, v_i_778_);
v___x_786_ = lean_unsigned_to_nat(0u);
v_bs_x27_787_ = lean_array_uset(v_bs_779_, v_i_778_, v___x_786_);
v___x_795_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_784_, v_v_785_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_val_796_; lean_object* v_name_797_; 
lean_dec(v_v_785_);
v_val_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_796_);
lean_dec_ref(v___x_795_);
v_name_797_ = lean_ctor_get(v_val_796_, 1);
lean_inc(v_name_797_);
lean_dec(v_val_796_);
v_a_789_ = v_name_797_;
v_a_790_ = v___y_780_;
goto v___jp_788_;
}
else
{
uint8_t v___x_798_; 
lean_dec(v___x_795_);
v___x_798_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_785_, v_a_775_);
if (v___x_798_ == 0)
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_bs_x27_787_);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_774_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_816_ = lean_ctor_get(v_a_774_, 1);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_a_774_, 0);
lean_dec(v_unused_817_);
v___x_800_ = v_a_774_;
v_isShared_801_ = v_isSharedCheck_815_;
goto v_resetjp_799_;
}
else
{
lean_dec(v_a_774_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_815_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_803_ = lean_string_append(v___x_776_, v___x_802_);
v___x_804_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_785_, v___x_782_);
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
lean_dec_ref(v___x_804_);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___x_808_ = 3;
v___x_809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v___x_808_);
v___x_810_ = lean_array_get_size(v___y_780_);
v___x_811_ = lean_array_push(v___y_780_, v___x_809_);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 1, v___x_811_);
lean_ctor_set(v___x_800_, 0, v___x_810_);
v___x_813_ = v___x_800_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
v_a_789_ = v_v_785_;
v_a_790_ = v___y_780_;
goto v___jp_788_;
}
}
v___jp_788_:
{
size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_778_, v___x_791_);
v___x_793_ = lean_array_uset(v_bs_x27_787_, v_i_778_, v_a_789_);
v_i_778_ = v___x_792_;
v_bs_779_ = v___x_793_;
v___y_780_ = v_a_790_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v___x_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_bs_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_827_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_818_, v_a_819_, v___x_820_, v_sz_boxed_826_, v_i_boxed_827_, v_bs_823_, v___y_824_);
lean_dec(v_a_819_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_830_, lean_object* v___x_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_bs_834_, lean_object* v___y_835_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v___x_831_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_bs_834_);
lean_ctor_set(v___x_838_, 1, v___y_835_);
return v___x_838_;
}
else
{
lean_object* v_v_839_; lean_object* v___x_840_; 
v_v_839_ = lean_array_uget_borrowed(v_bs_834_, v_i_833_);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_830_, v_v_839_);
if (lean_obj_tag(v___x_840_) == 1)
{
lean_object* v_val_841_; lean_object* v___x_842_; lean_object* v_bs_x27_843_; size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v_val_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref(v___x_840_);
v___x_842_ = lean_unsigned_to_nat(0u);
v_bs_x27_843_ = lean_array_uset(v_bs_834_, v_i_833_, v___x_842_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_833_, v___x_844_);
v___x_846_ = lean_array_uset(v_bs_x27_843_, v_i_833_, v_val_841_);
v_i_833_ = v___x_845_;
v_bs_834_ = v___x_846_;
goto _start;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_inc(v_v_839_);
lean_dec(v___x_840_);
lean_dec_ref(v_bs_834_);
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_849_ = lean_string_append(v___x_831_, v___x_848_);
v___x_850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_839_, v___x_837_);
v___x_851_ = lean_string_append(v___x_849_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_853_ = lean_string_append(v___x_851_, v___x_852_);
v___x_854_ = 3;
v___x_855_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*1, v___x_854_);
v___x_856_ = lean_array_get_size(v___y_835_);
v___x_857_ = lean_array_push(v___y_835_, v___x_855_);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_859_, lean_object* v___x_860_, lean_object* v_sz_861_, lean_object* v_i_862_, lean_object* v_bs_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
size_t v_sz_boxed_866_; size_t v_i_boxed_867_; lean_object* v_res_868_; 
v_sz_boxed_866_ = lean_unbox_usize(v_sz_861_);
lean_dec(v_sz_861_);
v_i_boxed_867_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_859_, v___x_860_, v_sz_boxed_866_, v_i_boxed_867_, v_bs_863_, v___y_864_);
lean_dec(v_a_859_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_869_, lean_object* v_opts_870_, size_t v_sz_871_, size_t v_i_872_, lean_object* v_bs_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = lean_usize_dec_lt(v_i_872_, v_sz_871_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec_ref(v_env_869_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v_bs_873_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v_v_877_; lean_object* v___x_878_; 
v___x_876_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
v_v_877_ = lean_array_uget_borrowed(v_bs_873_, v_i_872_);
lean_inc(v_v_877_);
lean_inc_ref(v_env_869_);
v___x_878_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_869_, v_opts_870_, v___x_876_, v_v_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v_bs_873_);
lean_dec_ref(v_env_869_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v_bs_x27_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_878_);
v___x_888_ = lean_unsigned_to_nat(0u);
v_bs_x27_889_ = lean_array_uset(v_bs_873_, v_i_872_, v___x_888_);
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_add(v_i_872_, v___x_890_);
v___x_892_ = lean_array_uset(v_bs_x27_889_, v_i_872_, v_a_887_);
v_i_872_ = v___x_891_;
v_bs_873_ = v___x_892_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_894_, lean_object* v_opts_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_bs_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_900_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_894_, v_opts_895_, v_sz_boxed_899_, v_i_boxed_900_, v_bs_898_);
lean_dec_ref(v_opts_895_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_902_, lean_object* v_opts_903_, lean_object* v_as_904_, size_t v_sz_905_, size_t v_i_906_, lean_object* v_b_907_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_usize_dec_lt(v_i_906_, v_sz_905_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_env_902_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v_b_907_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; lean_object* v_a_911_; lean_object* v___x_912_; 
v___x_910_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
v_a_911_ = lean_array_uget_borrowed(v_as_904_, v_i_906_);
lean_inc(v_a_911_);
lean_inc_ref(v_env_902_);
v___x_912_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_902_, v_opts_903_, v___x_910_, v_a_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_b_907_);
lean_dec_ref(v_env_902_);
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v_name_922_; lean_object* v_config_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_934_; 
v_a_921_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_912_);
v_name_922_ = lean_ctor_get(v_a_921_, 0);
v_config_923_ = lean_ctor_get(v_a_921_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_921_);
if (v_isSharedCheck_934_ == 0)
{
v___x_925_ = v_a_921_;
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_config_923_);
lean_inc(v_name_922_);
lean_dec(v_a_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_name_922_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_config_923_);
v___x_928_ = v_reuseFailAlloc_933_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; size_t v___x_930_; size_t v___x_931_; 
v___x_929_ = lean_array_push(v_b_907_, v___x_928_);
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_906_, v___x_930_);
v_i_906_ = v___x_931_;
v_b_907_ = v___x_929_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_935_, lean_object* v_opts_936_, lean_object* v_as_937_, lean_object* v_sz_938_, lean_object* v_i_939_, lean_object* v_b_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_938_);
lean_dec(v_sz_938_);
v_i_boxed_942_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_935_, v_opts_936_, v_as_937_, v_sz_boxed_941_, v_i_boxed_942_, v_b_940_);
lean_dec_ref(v_as_937_);
lean_dec_ref(v_opts_936_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_944_, lean_object* v_opts_945_, lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v_env_944_);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_b_949_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v_a_953_; lean_object* v___x_954_; 
v___x_952_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
v_a_953_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
lean_inc(v_a_953_);
lean_inc_ref(v_env_944_);
v___x_954_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_944_, v_opts_945_, v___x_952_, v_a_953_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec_ref(v_b_949_);
lean_dec_ref(v_env_944_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v_name_964_; lean_object* v_config_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_976_; 
v_a_963_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_954_);
v_name_964_ = lean_ctor_get(v_a_963_, 0);
v_config_965_ = lean_ctor_get(v_a_963_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_963_);
if (v_isSharedCheck_976_ == 0)
{
v___x_967_ = v_a_963_;
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_config_965_);
lean_inc(v_name_964_);
lean_dec(v_a_963_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_name_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_config_965_);
v___x_970_ = v_reuseFailAlloc_975_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; size_t v___x_972_; size_t v___x_973_; 
v___x_971_ = lean_array_push(v_b_949_, v___x_970_);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_948_, v___x_972_);
v_i_948_ = v___x_973_;
v_b_949_ = v___x_971_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_977_, lean_object* v_opts_978_, lean_object* v_as_979_, lean_object* v_sz_980_, lean_object* v_i_981_, lean_object* v_b_982_){
_start:
{
size_t v_sz_boxed_983_; size_t v_i_boxed_984_; lean_object* v_res_985_; 
v_sz_boxed_983_ = lean_unbox_usize(v_sz_980_);
lean_dec(v_sz_980_);
v_i_boxed_984_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_977_, v_opts_978_, v_as_979_, v_sz_boxed_983_, v_i_boxed_984_, v_b_982_);
lean_dec_ref(v_as_979_);
lean_dec_ref(v_opts_978_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_t_986_, lean_object* v_k_987_){
_start:
{
if (lean_obj_tag(v_t_986_) == 0)
{
lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v_l_990_; lean_object* v_r_991_; uint8_t v___x_992_; 
v_k_988_ = lean_ctor_get(v_t_986_, 1);
v_v_989_ = lean_ctor_get(v_t_986_, 2);
v_l_990_ = lean_ctor_get(v_t_986_, 3);
v_r_991_ = lean_ctor_get(v_t_986_, 4);
v___x_992_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_987_, v_k_988_);
switch(v___x_992_)
{
case 0:
{
v_t_986_ = v_l_990_;
goto _start;
}
case 1:
{
lean_object* v___x_994_; 
lean_inc(v_v_989_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_v_989_);
return v___x_994_;
}
default: 
{
v_t_986_ = v_r_991_;
goto _start;
}
}
}
else
{
lean_object* v___x_996_; 
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_t_997_, lean_object* v_k_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_997_, v_k_998_);
lean_dec(v_k_998_);
lean_dec(v_t_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(lean_object* v_k_1000_, lean_object* v_v_1001_, lean_object* v_t_1002_){
_start:
{
if (lean_obj_tag(v_t_1002_) == 0)
{
lean_object* v_size_1003_; lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_l_1006_; lean_object* v_r_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1287_; 
v_size_1003_ = lean_ctor_get(v_t_1002_, 0);
v_k_1004_ = lean_ctor_get(v_t_1002_, 1);
v_v_1005_ = lean_ctor_get(v_t_1002_, 2);
v_l_1006_ = lean_ctor_get(v_t_1002_, 3);
v_r_1007_ = lean_ctor_get(v_t_1002_, 4);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_t_1002_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1009_ = v_t_1002_;
v_isShared_1010_ = v_isSharedCheck_1287_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_r_1007_);
lean_inc(v_l_1006_);
lean_inc(v_v_1005_);
lean_inc(v_k_1004_);
lean_inc(v_size_1003_);
lean_dec(v_t_1002_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1287_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1000_, v_k_1004_);
switch(v___x_1011_)
{
case 0:
{
lean_object* v_impl_1012_; lean_object* v___x_1013_; 
lean_dec(v_size_1003_);
v_impl_1012_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1000_, v_v_1001_, v_l_1006_);
v___x_1013_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1007_) == 0)
{
lean_object* v_size_1014_; lean_object* v_size_1015_; lean_object* v_k_1016_; lean_object* v_v_1017_; lean_object* v_l_1018_; lean_object* v_r_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_size_1014_ = lean_ctor_get(v_r_1007_, 0);
v_size_1015_ = lean_ctor_get(v_impl_1012_, 0);
lean_inc(v_size_1015_);
v_k_1016_ = lean_ctor_get(v_impl_1012_, 1);
lean_inc(v_k_1016_);
v_v_1017_ = lean_ctor_get(v_impl_1012_, 2);
lean_inc(v_v_1017_);
v_l_1018_ = lean_ctor_get(v_impl_1012_, 3);
lean_inc(v_l_1018_);
v_r_1019_ = lean_ctor_get(v_impl_1012_, 4);
lean_inc(v_r_1019_);
v___x_1020_ = lean_unsigned_to_nat(3u);
v___x_1021_ = lean_nat_mul(v___x_1020_, v_size_1014_);
v___x_1022_ = lean_nat_dec_lt(v___x_1021_, v_size_1015_);
lean_dec(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_dec(v_r_1019_);
lean_dec(v_l_1018_);
lean_dec(v_v_1017_);
lean_dec(v_k_1016_);
v___x_1023_ = lean_nat_add(v___x_1013_, v_size_1015_);
lean_dec(v_size_1015_);
v___x_1024_ = lean_nat_add(v___x_1023_, v_size_1014_);
lean_dec(v___x_1023_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 3, v_impl_1012_);
lean_ctor_set(v___x_1009_, 0, v___x_1024_);
v___x_1026_ = v___x_1009_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_impl_1012_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_r_1007_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
else
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v_impl_1012_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1094_ = lean_ctor_get(v_impl_1012_, 4);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_impl_1012_, 3);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_impl_1012_, 2);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_impl_1012_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_impl_1012_, 0);
lean_dec(v_unused_1098_);
v___x_1029_ = v_impl_1012_;
v_isShared_1030_ = v_isSharedCheck_1093_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v_impl_1012_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1093_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_size_1031_; lean_object* v_size_1032_; lean_object* v_k_1033_; lean_object* v_v_1034_; lean_object* v_l_1035_; lean_object* v_r_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_size_1031_ = lean_ctor_get(v_l_1018_, 0);
v_size_1032_ = lean_ctor_get(v_r_1019_, 0);
v_k_1033_ = lean_ctor_get(v_r_1019_, 1);
v_v_1034_ = lean_ctor_get(v_r_1019_, 2);
v_l_1035_ = lean_ctor_get(v_r_1019_, 3);
v_r_1036_ = lean_ctor_get(v_r_1019_, 4);
v___x_1037_ = lean_unsigned_to_nat(2u);
v___x_1038_ = lean_nat_mul(v___x_1037_, v_size_1031_);
v___x_1039_ = lean_nat_dec_lt(v_size_1032_, v___x_1038_);
lean_dec(v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1068_; 
lean_inc(v_r_1036_);
lean_inc(v_l_1035_);
lean_inc(v_v_1034_);
lean_inc(v_k_1033_);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_r_1019_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1069_ = lean_ctor_get(v_r_1019_, 4);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_r_1019_, 3);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_r_1019_, 2);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_r_1019_, 1);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_r_1019_, 0);
lean_dec(v_unused_1073_);
v___x_1041_ = v_r_1019_;
v_isShared_1042_ = v_isSharedCheck_1068_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v_r_1019_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1068_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___x_1056_; lean_object* v___y_1058_; 
v___x_1043_ = lean_nat_add(v___x_1013_, v_size_1015_);
lean_dec(v_size_1015_);
v___x_1044_ = lean_nat_add(v___x_1043_, v_size_1014_);
lean_dec(v___x_1043_);
v___x_1056_ = lean_nat_add(v___x_1013_, v_size_1031_);
if (lean_obj_tag(v_l_1035_) == 0)
{
lean_object* v_size_1066_; 
v_size_1066_ = lean_ctor_get(v_l_1035_, 0);
lean_inc(v_size_1066_);
v___y_1058_ = v_size_1066_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___y_1058_ = v___x_1067_;
goto v___jp_1057_;
}
v___jp_1045_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_nat_add(v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v_r_1007_);
lean_ctor_set(v___x_1041_, 3, v_r_1036_);
lean_ctor_set(v___x_1041_, 2, v_v_1005_);
lean_ctor_set(v___x_1041_, 1, v_k_1004_);
lean_ctor_set(v___x_1041_, 0, v___x_1049_);
v___x_1051_ = v___x_1041_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v_r_1036_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v_r_1007_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v___x_1051_);
lean_ctor_set(v___x_1029_, 3, v___y_1046_);
lean_ctor_set(v___x_1029_, 2, v_v_1034_);
lean_ctor_set(v___x_1029_, 1, v_k_1033_);
lean_ctor_set(v___x_1029_, 0, v___x_1044_);
v___x_1053_ = v___x_1029_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_k_1033_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_v_1034_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v___y_1046_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_nat_add(v___x_1056_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec(v___x_1056_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v_l_1035_);
lean_ctor_set(v___x_1009_, 3, v_l_1018_);
lean_ctor_set(v___x_1009_, 2, v_v_1017_);
lean_ctor_set(v___x_1009_, 1, v_k_1016_);
lean_ctor_set(v___x_1009_, 0, v___x_1059_);
v___x_1061_ = v___x_1009_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_k_1016_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_v_1017_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_l_1018_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_l_1035_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_nat_add(v___x_1013_, v_size_1014_);
if (lean_obj_tag(v_r_1036_) == 0)
{
lean_object* v_size_1063_; 
v_size_1063_ = lean_ctor_get(v_r_1036_, 0);
lean_inc(v_size_1063_);
v___y_1046_ = v___x_1061_;
v___y_1047_ = v___x_1062_;
v___y_1048_ = v_size_1063_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___y_1046_ = v___x_1061_;
v___y_1047_ = v___x_1062_;
v___y_1048_ = v___x_1064_;
goto v___jp_1045_;
}
}
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_del_object(v___x_1009_);
v___x_1074_ = lean_nat_add(v___x_1013_, v_size_1015_);
lean_dec(v_size_1015_);
v___x_1075_ = lean_nat_add(v___x_1074_, v_size_1014_);
lean_dec(v___x_1074_);
v___x_1076_ = lean_nat_add(v___x_1013_, v_size_1014_);
v___x_1077_ = lean_nat_add(v___x_1076_, v_size_1032_);
lean_dec(v___x_1076_);
lean_inc_ref(v_r_1007_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v_r_1007_);
lean_ctor_set(v___x_1029_, 3, v_r_1019_);
lean_ctor_set(v___x_1029_, 2, v_v_1005_);
lean_ctor_set(v___x_1029_, 1, v_k_1004_);
lean_ctor_set(v___x_1029_, 0, v___x_1077_);
v___x_1079_ = v___x_1029_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_r_1019_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_r_1007_);
v___x_1079_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_isSharedCheck_1086_ = !lean_is_exclusive(v_r_1007_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; lean_object* v_unused_1091_; 
v_unused_1087_ = lean_ctor_get(v_r_1007_, 4);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_r_1007_, 3);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_r_1007_, 2);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_r_1007_, 1);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_r_1007_, 0);
lean_dec(v_unused_1091_);
v___x_1081_ = v_r_1007_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_dec(v_r_1007_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 4, v___x_1079_);
lean_ctor_set(v___x_1081_, 3, v_l_1018_);
lean_ctor_set(v___x_1081_, 2, v_v_1017_);
lean_ctor_set(v___x_1081_, 1, v_k_1016_);
lean_ctor_set(v___x_1081_, 0, v___x_1075_);
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_k_1016_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_v_1017_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_l_1018_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v___x_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1099_; 
v_l_1099_ = lean_ctor_get(v_impl_1012_, 3);
lean_inc(v_l_1099_);
if (lean_obj_tag(v_l_1099_) == 0)
{
lean_object* v_r_1100_; lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1113_; 
v_r_1100_ = lean_ctor_get(v_impl_1012_, 4);
v_k_1101_ = lean_ctor_get(v_impl_1012_, 1);
v_v_1102_ = lean_ctor_get(v_impl_1012_, 2);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_impl_1012_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1114_ = lean_ctor_get(v_impl_1012_, 3);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_impl_1012_, 0);
lean_dec(v_unused_1115_);
v___x_1104_ = v_impl_1012_;
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_r_1100_);
lean_inc(v_v_1102_);
lean_inc(v_k_1101_);
lean_dec(v_impl_1012_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1100_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 3, v_r_1100_);
lean_ctor_set(v___x_1104_, 2, v_v_1005_);
lean_ctor_set(v___x_1104_, 1, v_k_1004_);
lean_ctor_set(v___x_1104_, 0, v___x_1013_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_r_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_1100_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___x_1108_);
lean_ctor_set(v___x_1009_, 3, v_l_1099_);
lean_ctor_set(v___x_1009_, 2, v_v_1102_);
lean_ctor_set(v___x_1009_, 1, v_k_1101_);
lean_ctor_set(v___x_1009_, 0, v___x_1106_);
v___x_1110_ = v___x_1009_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_r_1116_; 
v_r_1116_ = lean_ctor_get(v_impl_1012_, 4);
lean_inc(v_r_1116_);
if (lean_obj_tag(v_r_1116_) == 0)
{
lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1141_; 
v_k_1117_ = lean_ctor_get(v_impl_1012_, 1);
v_v_1118_ = lean_ctor_get(v_impl_1012_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_impl_1012_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1142_ = lean_ctor_get(v_impl_1012_, 4);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_impl_1012_, 3);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_impl_1012_, 0);
lean_dec(v_unused_1144_);
v___x_1120_ = v_impl_1012_;
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_v_1118_);
lean_inc(v_k_1117_);
lean_dec(v_impl_1012_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1137_; 
v_k_1122_ = lean_ctor_get(v_r_1116_, 1);
v_v_1123_ = lean_ctor_get(v_r_1116_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_r_1116_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1138_ = lean_ctor_get(v_r_1116_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_r_1116_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_r_1116_, 0);
lean_dec(v_unused_1140_);
v___x_1125_ = v_r_1116_;
v_isShared_1126_ = v_isSharedCheck_1137_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_r_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1137_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(3u);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_l_1099_);
lean_ctor_set(v___x_1125_, 3, v_l_1099_);
lean_ctor_set(v___x_1125_, 2, v_v_1118_);
lean_ctor_set(v___x_1125_, 1, v_k_1117_);
lean_ctor_set(v___x_1125_, 0, v___x_1013_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_l_1099_);
v___x_1129_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_l_1099_);
lean_ctor_set(v___x_1120_, 2, v_v_1005_);
lean_ctor_set(v___x_1120_, 1, v_k_1004_);
lean_ctor_set(v___x_1120_, 0, v___x_1013_);
v___x_1131_ = v___x_1120_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_l_1099_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___x_1131_);
lean_ctor_set(v___x_1009_, 3, v___x_1129_);
lean_ctor_set(v___x_1009_, 2, v_v_1123_);
lean_ctor_set(v___x_1009_, 1, v_k_1122_);
lean_ctor_set(v___x_1009_, 0, v___x_1127_);
v___x_1133_ = v___x_1009_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(2u);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v_r_1116_);
lean_ctor_set(v___x_1009_, 3, v_impl_1012_);
lean_ctor_set(v___x_1009_, 0, v___x_1145_);
v___x_1147_ = v___x_1009_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_impl_1012_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_r_1116_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1150_; 
lean_dec(v_v_1005_);
lean_dec(v_k_1004_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 2, v_v_1001_);
lean_ctor_set(v___x_1009_, 1, v_k_1000_);
v___x_1150_ = v___x_1009_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_size_1003_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_1000_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_1001_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_r_1007_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
default: 
{
lean_object* v_impl_1152_; lean_object* v___x_1153_; 
lean_dec(v_size_1003_);
v_impl_1152_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1000_, v_v_1001_, v_r_1007_);
v___x_1153_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1006_) == 0)
{
lean_object* v_size_1154_; lean_object* v_size_1155_; lean_object* v_k_1156_; lean_object* v_v_1157_; lean_object* v_l_1158_; lean_object* v_r_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_size_1154_ = lean_ctor_get(v_l_1006_, 0);
v_size_1155_ = lean_ctor_get(v_impl_1152_, 0);
lean_inc(v_size_1155_);
v_k_1156_ = lean_ctor_get(v_impl_1152_, 1);
lean_inc(v_k_1156_);
v_v_1157_ = lean_ctor_get(v_impl_1152_, 2);
lean_inc(v_v_1157_);
v_l_1158_ = lean_ctor_get(v_impl_1152_, 3);
lean_inc(v_l_1158_);
v_r_1159_ = lean_ctor_get(v_impl_1152_, 4);
lean_inc(v_r_1159_);
v___x_1160_ = lean_unsigned_to_nat(3u);
v___x_1161_ = lean_nat_mul(v___x_1160_, v_size_1154_);
v___x_1162_ = lean_nat_dec_lt(v___x_1161_, v_size_1155_);
lean_dec(v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v_r_1159_);
lean_dec(v_l_1158_);
lean_dec(v_v_1157_);
lean_dec(v_k_1156_);
v___x_1163_ = lean_nat_add(v___x_1153_, v_size_1154_);
v___x_1164_ = lean_nat_add(v___x_1163_, v_size_1155_);
lean_dec(v_size_1155_);
lean_dec(v___x_1163_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v_impl_1152_);
lean_ctor_set(v___x_1009_, 0, v___x_1164_);
v___x_1166_ = v___x_1009_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_impl_1152_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v_impl_1152_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; 
v_unused_1232_ = lean_ctor_get(v_impl_1152_, 4);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_impl_1152_, 3);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_impl_1152_, 2);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_impl_1152_, 1);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_impl_1152_, 0);
lean_dec(v_unused_1236_);
v___x_1169_ = v_impl_1152_;
v_isShared_1170_ = v_isSharedCheck_1231_;
goto v_resetjp_1168_;
}
else
{
lean_dec(v_impl_1152_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1231_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_size_1171_; lean_object* v_k_1172_; lean_object* v_v_1173_; lean_object* v_l_1174_; lean_object* v_r_1175_; lean_object* v_size_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_size_1171_ = lean_ctor_get(v_l_1158_, 0);
v_k_1172_ = lean_ctor_get(v_l_1158_, 1);
v_v_1173_ = lean_ctor_get(v_l_1158_, 2);
v_l_1174_ = lean_ctor_get(v_l_1158_, 3);
v_r_1175_ = lean_ctor_get(v_l_1158_, 4);
v_size_1176_ = lean_ctor_get(v_r_1159_, 0);
v___x_1177_ = lean_unsigned_to_nat(2u);
v___x_1178_ = lean_nat_mul(v___x_1177_, v_size_1176_);
v___x_1179_ = lean_nat_dec_lt(v_size_1171_, v___x_1178_);
lean_dec(v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1207_; 
lean_inc(v_r_1175_);
lean_inc(v_l_1174_);
lean_inc(v_v_1173_);
lean_inc(v_k_1172_);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_l_1158_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1208_ = lean_ctor_get(v_l_1158_, 4);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_l_1158_, 3);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_l_1158_, 2);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_l_1158_, 1);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_l_1158_, 0);
lean_dec(v_unused_1212_);
v___x_1181_ = v_l_1158_;
v_isShared_1182_ = v_isSharedCheck_1207_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_l_1158_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1207_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1197_; 
v___x_1183_ = lean_nat_add(v___x_1153_, v_size_1154_);
v___x_1184_ = lean_nat_add(v___x_1183_, v_size_1155_);
lean_dec(v_size_1155_);
if (lean_obj_tag(v_l_1174_) == 0)
{
lean_object* v_size_1205_; 
v_size_1205_ = lean_ctor_get(v_l_1174_, 0);
lean_inc(v_size_1205_);
v___y_1197_ = v_size_1205_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___y_1197_ = v___x_1206_;
goto v___jp_1196_;
}
v___jp_1185_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_nat_add(v___y_1186_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec(v___y_1186_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 4, v_r_1159_);
lean_ctor_set(v___x_1181_, 3, v_r_1175_);
lean_ctor_set(v___x_1181_, 2, v_v_1157_);
lean_ctor_set(v___x_1181_, 1, v_k_1156_);
lean_ctor_set(v___x_1181_, 0, v___x_1189_);
v___x_1191_ = v___x_1181_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_1156_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_1157_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_r_1175_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_r_1159_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 4, v___x_1191_);
lean_ctor_set(v___x_1169_, 3, v___y_1187_);
lean_ctor_set(v___x_1169_, 2, v_v_1173_);
lean_ctor_set(v___x_1169_, 1, v_k_1172_);
lean_ctor_set(v___x_1169_, 0, v___x_1184_);
v___x_1193_ = v___x_1169_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_k_1172_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_v_1173_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v___y_1187_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
v___jp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_nat_add(v___x_1183_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec(v___x_1183_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v_l_1174_);
lean_ctor_set(v___x_1009_, 0, v___x_1198_);
v___x_1200_ = v___x_1009_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_l_1174_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_nat_add(v___x_1153_, v_size_1176_);
if (lean_obj_tag(v_r_1175_) == 0)
{
lean_object* v_size_1202_; 
v_size_1202_ = lean_ctor_get(v_r_1175_, 0);
lean_inc(v_size_1202_);
v___y_1186_ = v___x_1201_;
v___y_1187_ = v___x_1200_;
v___y_1188_ = v_size_1202_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_unsigned_to_nat(0u);
v___y_1186_ = v___x_1201_;
v___y_1187_ = v___x_1200_;
v___y_1188_ = v___x_1203_;
goto v___jp_1185_;
}
}
}
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_del_object(v___x_1009_);
v___x_1213_ = lean_nat_add(v___x_1153_, v_size_1154_);
v___x_1214_ = lean_nat_add(v___x_1213_, v_size_1155_);
lean_dec(v_size_1155_);
v___x_1215_ = lean_nat_add(v___x_1213_, v_size_1171_);
lean_dec(v___x_1213_);
lean_inc_ref(v_l_1006_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 4, v_l_1158_);
lean_ctor_set(v___x_1169_, 3, v_l_1006_);
lean_ctor_set(v___x_1169_, 2, v_v_1005_);
lean_ctor_set(v___x_1169_, 1, v_k_1004_);
lean_ctor_set(v___x_1169_, 0, v___x_1215_);
v___x_1217_ = v___x_1169_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_l_1158_);
v___x_1217_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_isSharedCheck_1224_ = !lean_is_exclusive(v_l_1006_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1225_ = lean_ctor_get(v_l_1006_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_l_1006_, 3);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_l_1006_, 2);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_l_1006_, 1);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_l_1006_, 0);
lean_dec(v_unused_1229_);
v___x_1219_ = v_l_1006_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_l_1006_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 4, v_r_1159_);
lean_ctor_set(v___x_1219_, 3, v___x_1217_);
lean_ctor_set(v___x_1219_, 2, v_v_1157_);
lean_ctor_set(v___x_1219_, 1, v_k_1156_);
lean_ctor_set(v___x_1219_, 0, v___x_1214_);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1156_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1157_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_r_1159_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1237_; 
v_l_1237_ = lean_ctor_get(v_impl_1152_, 3);
lean_inc(v_l_1237_);
if (lean_obj_tag(v_l_1237_) == 0)
{
lean_object* v_r_1238_; lean_object* v_k_1239_; lean_object* v_v_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1263_; 
v_r_1238_ = lean_ctor_get(v_impl_1152_, 4);
v_k_1239_ = lean_ctor_get(v_impl_1152_, 1);
v_v_1240_ = lean_ctor_get(v_impl_1152_, 2);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_impl_1152_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; lean_object* v_unused_1265_; 
v_unused_1264_ = lean_ctor_get(v_impl_1152_, 3);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_impl_1152_, 0);
lean_dec(v_unused_1265_);
v___x_1242_ = v_impl_1152_;
v_isShared_1243_ = v_isSharedCheck_1263_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_r_1238_);
lean_inc(v_v_1240_);
lean_inc(v_k_1239_);
lean_dec(v_impl_1152_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1263_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_k_1244_; lean_object* v_v_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1259_; 
v_k_1244_ = lean_ctor_get(v_l_1237_, 1);
v_v_1245_ = lean_ctor_get(v_l_1237_, 2);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_l_1237_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; lean_object* v_unused_1261_; lean_object* v_unused_1262_; 
v_unused_1260_ = lean_ctor_get(v_l_1237_, 4);
lean_dec(v_unused_1260_);
v_unused_1261_ = lean_ctor_get(v_l_1237_, 3);
lean_dec(v_unused_1261_);
v_unused_1262_ = lean_ctor_get(v_l_1237_, 0);
lean_dec(v_unused_1262_);
v___x_1247_ = v_l_1237_;
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_v_1245_);
lean_inc(v_k_1244_);
lean_dec(v_l_1237_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1238_, 2);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 4, v_r_1238_);
lean_ctor_set(v___x_1247_, 3, v_r_1238_);
lean_ctor_set(v___x_1247_, 2, v_v_1005_);
lean_ctor_set(v___x_1247_, 1, v_k_1004_);
lean_ctor_set(v___x_1247_, 0, v___x_1153_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_r_1238_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_r_1238_);
v___x_1251_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
lean_inc(v_r_1238_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 3, v_r_1238_);
lean_ctor_set(v___x_1242_, 0, v___x_1153_);
v___x_1253_ = v___x_1242_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_r_1238_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_r_1238_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___x_1253_);
lean_ctor_set(v___x_1009_, 3, v___x_1251_);
lean_ctor_set(v___x_1009_, 2, v_v_1245_);
lean_ctor_set(v___x_1009_, 1, v_k_1244_);
lean_ctor_set(v___x_1009_, 0, v___x_1249_);
v___x_1255_ = v___x_1009_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_1244_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_1245_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
else
{
lean_object* v_r_1266_; 
v_r_1266_ = lean_ctor_get(v_impl_1152_, 4);
lean_inc(v_r_1266_);
if (lean_obj_tag(v_r_1266_) == 0)
{
lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1279_; 
v_k_1267_ = lean_ctor_get(v_impl_1152_, 1);
v_v_1268_ = lean_ctor_get(v_impl_1152_, 2);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_impl_1152_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; lean_object* v_unused_1281_; lean_object* v_unused_1282_; 
v_unused_1280_ = lean_ctor_get(v_impl_1152_, 4);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v_impl_1152_, 3);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_impl_1152_, 0);
lean_dec(v_unused_1282_);
v___x_1270_ = v_impl_1152_;
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
lean_dec(v_impl_1152_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_unsigned_to_nat(3u);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 4, v_l_1237_);
lean_ctor_set(v___x_1270_, 2, v_v_1005_);
lean_ctor_set(v___x_1270_, 1, v_k_1004_);
lean_ctor_set(v___x_1270_, 0, v___x_1153_);
v___x_1274_ = v___x_1270_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_l_1237_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_l_1237_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v_r_1266_);
lean_ctor_set(v___x_1009_, 3, v___x_1274_);
lean_ctor_set(v___x_1009_, 2, v_v_1268_);
lean_ctor_set(v___x_1009_, 1, v_k_1267_);
lean_ctor_set(v___x_1009_, 0, v___x_1272_);
v___x_1276_ = v___x_1009_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_r_1266_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_unsigned_to_nat(2u);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v_impl_1152_);
lean_ctor_set(v___x_1009_, 3, v_r_1266_);
lean_ctor_set(v___x_1009_, 0, v___x_1283_);
v___x_1285_ = v___x_1009_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_r_1266_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_impl_1152_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
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
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_k_1000_);
lean_ctor_set(v___x_1289_, 2, v_v_1001_);
lean_ctor_set(v___x_1289_, 3, v_t_1002_);
lean_ctor_set(v___x_1289_, 4, v_t_1002_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object* v___x_1293_, lean_object* v_as_1294_, size_t v_i_1295_, size_t v_stop_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_usize_dec_eq(v_i_1295_, v_stop_1296_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v_name_1302_; lean_object* v_kind_1303_; lean_object* v___x_1304_; 
v___x_1301_ = lean_array_uget_borrowed(v_as_1294_, v_i_1295_);
v_name_1302_ = lean_ctor_get(v___x_1301_, 1);
v_kind_1303_ = lean_ctor_get(v___x_1301_, 2);
v___x_1304_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_b_1297_, v_name_1302_);
if (lean_obj_tag(v___x_1304_) == 1)
{
lean_object* v_val_1305_; lean_object* v_kind_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v_b_1297_);
v_val_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_val_1305_);
lean_dec_ref(v___x_1304_);
v_kind_1306_ = lean_ctor_get(v_val_1305_, 2);
lean_inc(v_kind_1306_);
lean_dec(v_val_1305_);
v___x_1307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0));
v___x_1308_ = lean_string_append(v___x_1293_, v___x_1307_);
v___x_1309_ = 1;
lean_inc(v_name_1302_);
v___x_1310_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1302_, v___x_1309_);
v___x_1311_ = lean_string_append(v___x_1308_, v___x_1310_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1));
v___x_1313_ = lean_string_append(v___x_1311_, v___x_1312_);
v___x_1314_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1306_, v___x_1309_);
v___x_1315_ = lean_string_append(v___x_1313_, v___x_1314_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2));
v___x_1317_ = lean_string_append(v___x_1315_, v___x_1316_);
lean_inc(v_kind_1303_);
v___x_1318_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1303_, v___x_1309_);
v___x_1319_ = lean_string_append(v___x_1317_, v___x_1318_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
v___x_1322_ = 3;
v___x_1323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*1, v___x_1322_);
v___x_1324_ = lean_array_get_size(v___y_1298_);
v___x_1325_ = lean_array_push(v___y_1298_, v___x_1323_);
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; 
lean_dec(v___x_1304_);
lean_inc(v___x_1301_);
lean_inc(v_name_1302_);
v___x_1327_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_name_1302_, v___x_1301_, v_b_1297_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_i_1295_, v___x_1328_);
v_i_1295_ = v___x_1329_;
v_b_1297_ = v___x_1327_;
goto _start;
}
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v___x_1293_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_b_1297_);
lean_ctor_set(v___x_1331_, 1, v___y_1298_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object* v___x_1332_, lean_object* v_as_1333_, lean_object* v_i_1334_, lean_object* v_stop_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_i_boxed_1339_; size_t v_stop_boxed_1340_; lean_object* v_res_1341_; 
v_i_boxed_1339_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_stop_boxed_1340_ = lean_unbox_usize(v_stop_1335_);
lean_dec(v_stop_1335_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1332_, v_as_1333_, v_i_boxed_1339_, v_stop_boxed_1340_, v_b_1336_, v___y_1337_);
lean_dec_ref(v_as_1333_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1348_, lean_object* v_opts_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_a_1353_; lean_object* v_a_1354_; lean_object* v_a_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_inc_ref(v_env_1348_);
v___x_1360_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1348_, v_opts_1349_);
v___x_1361_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1349_);
lean_inc_ref_n(v_env_1348_, 2);
v___f_1364_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1364_, 0, v_env_1348_);
lean_closure_set(v___f_1364_, 1, v_opts_1349_);
lean_closure_set(v___f_1364_, 2, v___x_1363_);
v___x_1365_ = l_Lake_targetAttr;
v___x_1366_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1348_, v___x_1365_, v___f_1364_);
v___x_1367_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v_baseName_1369_; lean_object* v_keyName_1370_; lean_object* v_config_1371_; lean_object* v_toArray_1372_; size_t v_sz_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1367_);
v_baseName_1369_ = lean_ctor_get(v_a_1362_, 0);
v_keyName_1370_ = lean_ctor_get(v_a_1362_, 1);
v_config_1371_ = lean_ctor_get(v_a_1362_, 3);
v_toArray_1372_ = lean_ctor_get(v_a_1368_, 1);
v_sz_1373_ = lean_array_size(v_toArray_1372_);
v___x_1374_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1372_);
lean_inc(v_keyName_1370_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v_keyName_1370_, v_sz_1373_, v___x_1374_, v_toArray_1372_, v_a_1350_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1644_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_a_1377_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1644_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1644_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v_a_1447_; lean_object* v_a_1448_; lean_object* v___y_1486_; lean_object* v_a_1487_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___x_1615_; lean_object* v_a_1617_; lean_object* v_a_1618_; lean_object* v___y_1626_; uint8_t v___x_1638_; 
v___x_1407_ = l_Lake_instTypeNameScriptFn_unsafe__1;
v___x_1408_ = 0;
lean_inc(v_baseName_1369_);
v___x_1409_ = l_Lean_Name_toString(v_baseName_1369_, v___x_1408_);
v___x_1410_ = lean_box(v___x_1408_);
lean_inc_ref(v___x_1409_);
lean_inc_ref(v_opts_1349_);
lean_inc_ref(v_env_1348_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1411_, 0, v___x_1410_);
lean_closure_set(v___f_1411_, 1, v_env_1348_);
lean_closure_set(v___f_1411_, 2, v_opts_1349_);
lean_closure_set(v___f_1411_, 3, v___x_1407_);
lean_closure_set(v___f_1411_, 4, v___x_1409_);
v___x_1412_ = lean_box(1);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_array_get_size(v_a_1376_);
v___x_1638_ = lean_nat_dec_lt(v___x_1413_, v___x_1615_);
if (v___x_1638_ == 0)
{
v_a_1617_ = v___x_1412_;
v_a_1618_ = v_a_1377_;
goto v___jp_1616_;
}
else
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_le(v___x_1615_, v___x_1615_);
if (v___x_1639_ == 0)
{
if (v___x_1638_ == 0)
{
v_a_1617_ = v___x_1412_;
v_a_1618_ = v_a_1377_;
goto v___jp_1616_;
}
else
{
size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_usize_of_nat(v___x_1615_);
lean_inc_ref(v___x_1409_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1409_, v_a_1376_, v___x_1374_, v___x_1640_, v___x_1412_, v_a_1377_);
v___y_1626_ = v___x_1641_;
goto v___jp_1625_;
}
}
else
{
size_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_usize_of_nat(v___x_1615_);
lean_inc_ref(v___x_1409_);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1409_, v_a_1376_, v___x_1374_, v___x_1642_, v___x_1412_, v_a_1377_);
v___y_1626_ = v___x_1643_;
goto v___jp_1625_;
}
}
v___jp_1381_:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1394_, 0, v_a_1362_);
lean_ctor_set(v___x_1394_, 1, v___y_1382_);
lean_ctor_set(v___x_1394_, 2, v_a_1393_);
lean_ctor_set(v___x_1394_, 3, v_a_1376_);
lean_ctor_set(v___x_1394_, 4, v___y_1386_);
lean_ctor_set(v___x_1394_, 5, v___y_1388_);
lean_ctor_set(v___x_1394_, 6, v___y_1385_);
lean_ctor_set(v___x_1394_, 7, v___y_1390_);
lean_ctor_set(v___x_1394_, 8, v___y_1389_);
lean_ctor_set(v___x_1394_, 9, v___y_1387_);
lean_ctor_set(v___x_1394_, 10, v___y_1384_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___y_1383_);
lean_ctor_set(v___x_1379_, 0, v___x_1394_);
v___x_1396_ = v___x_1379_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___y_1383_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_dec_ref(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1382_);
lean_dec(v_a_1376_);
lean_dec(v_a_1362_);
v_a_1398_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1392_);
v___x_1399_ = lean_io_error_to_string(v_a_1398_);
v___x_1400_ = 3;
v___x_1401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*1, v___x_1400_);
v___x_1402_ = lean_array_get_size(v___y_1383_);
v___x_1403_ = lean_array_push(v___y_1383_, v___x_1401_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 1);
lean_ctor_set(v___x_1379_, 1, v___x_1403_);
lean_ctor_set(v___x_1379_, 0, v___x_1402_);
v___x_1405_ = v___x_1379_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
v___jp_1414_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; size_t v_sz_1427_; lean_object* v___x_1428_; 
v___x_1424_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1425_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1348_, 2);
v___x_1426_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1425_, v_env_1348_);
v_sz_1427_ = lean_array_size(v___x_1426_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1348_, v_opts_1349_, v___x_1426_, v_sz_1427_, v___x_1374_, v___x_1424_);
lean_dec_ref(v___x_1426_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v___y_1382_ = v___y_1415_;
v___y_1383_ = v_a_1423_;
v___y_1384_ = v_a_1422_;
v___y_1385_ = v___y_1416_;
v___y_1386_ = v___y_1417_;
v___y_1387_ = v___y_1419_;
v___y_1388_ = v___y_1418_;
v___y_1389_ = v___y_1420_;
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___x_1428_;
goto v___jp_1381_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; size_t v_sz_1432_; lean_object* v___x_1433_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v___x_1430_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1348_, 2);
v___x_1431_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1430_, v_env_1348_);
v_sz_1432_ = lean_array_size(v___x_1431_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1348_, v_opts_1349_, v___x_1431_, v_sz_1432_, v___x_1374_, v_a_1429_);
lean_dec_ref(v___x_1431_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v___y_1382_ = v___y_1415_;
v___y_1383_ = v_a_1423_;
v___y_1384_ = v_a_1422_;
v___y_1385_ = v___y_1416_;
v___y_1386_ = v___y_1417_;
v___y_1387_ = v___y_1419_;
v___y_1388_ = v___y_1418_;
v___y_1389_ = v___y_1420_;
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___x_1433_;
goto v___jp_1381_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; size_t v_sz_1437_; lean_object* v___x_1438_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1348_);
v___x_1436_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1435_, v_env_1348_);
v_sz_1437_ = lean_array_size(v___x_1436_);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1348_, v_opts_1349_, v___x_1436_, v_sz_1437_, v___x_1374_, v_a_1434_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_opts_1349_);
v___y_1382_ = v___y_1415_;
v___y_1383_ = v_a_1423_;
v___y_1384_ = v_a_1422_;
v___y_1385_ = v___y_1416_;
v___y_1386_ = v___y_1417_;
v___y_1387_ = v___y_1419_;
v___y_1388_ = v___y_1418_;
v___y_1389_ = v___y_1420_;
v___y_1390_ = v___y_1421_;
v___y_1391_ = v___x_1438_;
goto v___jp_1381_;
}
}
}
v___jp_1439_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; size_t v_sz_1451_; lean_object* v___x_1452_; 
v___x_1449_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1348_);
v___x_1450_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1449_, v_env_1348_);
v_sz_1451_ = lean_array_size(v___x_1450_);
lean_inc_ref(v___x_1409_);
v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1368_, v___y_1442_, v___x_1409_, v_sz_1451_, v___x_1374_, v___x_1450_, v_a_1448_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v_a_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
v_a_1454_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1452_);
v___x_1455_ = lean_array_get_size(v_a_1453_);
v___x_1456_ = lean_nat_dec_lt(v___y_1441_, v___x_1455_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_nat_dec_lt(v___x_1413_, v___x_1455_);
if (v___x_1457_ == 0)
{
lean_object* v_lintDriver_1458_; 
lean_dec(v_a_1453_);
lean_dec_ref(v___x_1409_);
v_lintDriver_1458_ = lean_ctor_get(v_config_1371_, 14);
lean_inc_ref(v_lintDriver_1458_);
v___y_1415_ = v___y_1440_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___y_1443_;
v___y_1418_ = v___y_1444_;
v___y_1419_ = v_a_1447_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1446_;
v_a_1422_ = v_lintDriver_1458_;
v_a_1423_ = v_a_1454_;
goto v___jp_1414_;
}
else
{
lean_object* v_lintDriver_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_lintDriver_1459_ = lean_ctor_get(v_config_1371_, 14);
v___x_1460_ = lean_string_utf8_byte_size(v_lintDriver_1459_);
v___x_1461_ = lean_nat_dec_eq(v___x_1460_, v___x_1413_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1440_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v___x_1462_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1463_ = lean_string_append(v___x_1409_, v___x_1462_);
v___x_1464_ = 3;
v___x_1465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*1, v___x_1464_);
v___x_1466_ = lean_array_get_size(v_a_1454_);
v___x_1467_ = lean_array_push(v_a_1454_, v___x_1465_);
v_a_1357_ = v___x_1466_;
v_a_1358_ = v___x_1467_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v___x_1409_);
v___x_1468_ = lean_array_fget(v_a_1453_, v___x_1413_);
lean_dec(v_a_1453_);
v___x_1469_ = l_Lean_Name_toString(v___x_1468_, v___x_1461_);
v___y_1415_ = v___y_1440_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___y_1443_;
v___y_1418_ = v___y_1444_;
v___y_1419_ = v_a_1447_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1446_;
v_a_1422_ = v___x_1469_;
v_a_1423_ = v_a_1454_;
goto v___jp_1414_;
}
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1440_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v___x_1470_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1471_ = lean_string_append(v___x_1409_, v___x_1470_);
v___x_1472_ = 3;
v___x_1473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set_uint8(v___x_1473_, sizeof(void*)*1, v___x_1472_);
v___x_1474_ = lean_array_get_size(v_a_1454_);
v___x_1475_ = lean_array_push(v_a_1454_, v___x_1473_);
v_a_1357_ = v___x_1474_;
v_a_1358_ = v___x_1475_;
goto v___jp_1356_;
}
}
else
{
lean_object* v_a_1476_; lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_a_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1440_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1476_ = lean_ctor_get(v___x_1452_, 0);
v_a_1477_ = lean_ctor_get(v___x_1452_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1452_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_inc(v_a_1476_);
lean_dec(v___x_1452_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1476_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
v___jp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; size_t v_sz_1490_; lean_object* v___x_1491_; 
v___x_1488_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1348_);
v___x_1489_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1488_, v_env_1348_);
v_sz_1490_ = lean_array_size(v___x_1489_);
lean_inc_ref(v___x_1409_);
lean_inc(v_a_1368_);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1368_, v___x_1409_, v_sz_1490_, v___x_1374_, v___x_1489_, v_a_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
v_a_1493_ = lean_ctor_get(v___x_1491_, 1);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1491_);
v___x_1494_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1348_);
v___x_1495_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1348_, v___x_1494_, v___f_1411_, v_a_1493_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; size_t v_sz_1500_; lean_object* v___x_1501_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
v_a_1497_ = lean_ctor_get(v___x_1495_, 1);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1495_);
v___x_1498_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1348_);
v___x_1499_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1498_, v_env_1348_);
v_sz_1500_ = lean_array_size(v___x_1499_);
lean_inc_ref(v___x_1409_);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1496_, v___x_1409_, v_sz_1500_, v___x_1374_, v___x_1499_, v_a_1497_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; size_t v_sz_1506_; lean_object* v___x_1507_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
v_a_1503_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1501_);
v___x_1504_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1348_, 2);
v___x_1505_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1504_, v_env_1348_);
v_sz_1506_ = lean_array_size(v___x_1505_);
lean_inc(v_keyName_1370_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1348_, v_opts_1349_, v_keyName_1370_, v_sz_1506_, v___x_1374_, v___x_1505_, v_a_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1565_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_a_1509_ = lean_ctor_get(v___x_1507_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1511_ = v___x_1507_;
v_isShared_1512_ = v_isSharedCheck_1565_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1565_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; size_t v_sz_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1513_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1348_, 2);
v___x_1514_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1513_, v_env_1348_);
v_sz_1515_ = lean_array_size(v___x_1514_);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1348_, v_opts_1349_, v_sz_1515_, v___x_1374_, v___x_1514_);
v___x_1517_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; size_t v_sz_1521_; lean_object* v___x_1522_; 
lean_del_object(v___x_1511_);
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1348_);
v___x_1520_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1519_, v_env_1348_);
v_sz_1521_ = lean_array_size(v___x_1520_);
lean_inc_ref(v___x_1409_);
lean_inc(v_a_1368_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1368_, v_a_1496_, v___x_1409_, v_sz_1521_, v___x_1374_, v___x_1520_, v_a_1509_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
v_a_1524_ = lean_ctor_get(v___x_1522_, 1);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1522_);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_array_get_size(v_a_1523_);
v___x_1527_ = lean_nat_dec_lt(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v___x_1413_, v___x_1526_);
if (v___x_1528_ == 0)
{
lean_object* v_testDriver_1529_; 
lean_dec(v_a_1523_);
v_testDriver_1529_ = lean_ctor_get(v_config_1371_, 12);
lean_inc_ref(v_testDriver_1529_);
v___y_1440_ = v_a_1518_;
v___y_1441_ = v___x_1525_;
v___y_1442_ = v_a_1496_;
v___y_1443_ = v___y_1486_;
v___y_1444_ = v_a_1492_;
v___y_1445_ = v_a_1508_;
v___y_1446_ = v_a_1502_;
v_a_1447_ = v_testDriver_1529_;
v_a_1448_ = v_a_1524_;
goto v___jp_1439_;
}
else
{
lean_object* v_testDriver_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_testDriver_1530_ = lean_ctor_get(v_config_1371_, 12);
v___x_1531_ = lean_string_utf8_byte_size(v_testDriver_1530_);
v___x_1532_ = lean_nat_dec_eq(v___x_1531_, v___x_1413_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_a_1523_);
lean_dec(v_a_1518_);
lean_dec(v_a_1508_);
lean_dec(v_a_1502_);
lean_dec(v_a_1496_);
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v___x_1533_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1534_ = lean_string_append(v___x_1409_, v___x_1533_);
v___x_1535_ = 3;
v___x_1536_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*1, v___x_1535_);
v___x_1537_ = lean_array_get_size(v_a_1524_);
v___x_1538_ = lean_array_push(v_a_1524_, v___x_1536_);
v_a_1353_ = v___x_1537_;
v_a_1354_ = v___x_1538_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_array_fget(v_a_1523_, v___x_1413_);
lean_dec(v_a_1523_);
v___x_1540_ = l_Lean_Name_toString(v___x_1539_, v___x_1532_);
v___y_1440_ = v_a_1518_;
v___y_1441_ = v___x_1525_;
v___y_1442_ = v_a_1496_;
v___y_1443_ = v___y_1486_;
v___y_1444_ = v_a_1492_;
v___y_1445_ = v_a_1508_;
v___y_1446_ = v_a_1502_;
v_a_1447_ = v___x_1540_;
v_a_1448_ = v_a_1524_;
goto v___jp_1439_;
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec(v_a_1523_);
lean_dec(v_a_1518_);
lean_dec(v_a_1508_);
lean_dec(v_a_1502_);
lean_dec(v_a_1496_);
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v___x_1541_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1542_ = lean_string_append(v___x_1409_, v___x_1541_);
v___x_1543_ = 3;
v___x_1544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*1, v___x_1543_);
v___x_1545_ = lean_array_get_size(v_a_1524_);
v___x_1546_ = lean_array_push(v_a_1524_, v___x_1544_);
v_a_1353_ = v___x_1545_;
v_a_1354_ = v___x_1546_;
goto v___jp_1352_;
}
}
else
{
lean_object* v_a_1547_; lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1518_);
lean_dec(v_a_1508_);
lean_dec(v_a_1502_);
lean_dec(v_a_1496_);
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1547_ = lean_ctor_get(v___x_1522_, 0);
v_a_1548_ = lean_ctor_get(v___x_1522_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1522_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_inc(v_a_1547_);
lean_dec(v___x_1522_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1547_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
lean_dec(v_a_1508_);
lean_dec(v_a_1502_);
lean_dec(v_a_1496_);
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1556_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1517_);
v___x_1557_ = lean_io_error_to_string(v_a_1556_);
v___x_1558_ = 3;
v___x_1559_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*1, v___x_1558_);
v___x_1560_ = lean_array_get_size(v_a_1509_);
v___x_1561_ = lean_array_push(v_a_1509_, v___x_1559_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 1);
lean_ctor_set(v___x_1511_, 1, v___x_1561_);
lean_ctor_set(v___x_1511_, 0, v___x_1560_);
v___x_1563_ = v___x_1511_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1502_);
lean_dec(v_a_1496_);
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1566_ = lean_ctor_get(v___x_1507_, 0);
v_a_1567_ = lean_ctor_get(v___x_1507_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1507_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_inc(v_a_1566_);
lean_dec(v___x_1507_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1566_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_a_1496_);
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1575_ = lean_ctor_get(v___x_1501_, 0);
v_a_1576_ = lean_ctor_get(v___x_1501_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1501_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_dec(v___x_1501_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_a_1492_);
lean_dec(v___y_1486_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1584_ = lean_ctor_get(v___x_1495_, 0);
v_a_1585_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1495_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_inc(v_a_1584_);
lean_dec(v___x_1495_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1584_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v___y_1486_);
lean_dec_ref(v___f_1411_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1593_ = lean_ctor_get(v___x_1491_, 0);
v_a_1594_ = lean_ctor_get(v___x_1491_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1491_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_inc(v_a_1593_);
lean_dec(v___x_1491_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1593_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
v___jp_1602_:
{
if (lean_obj_tag(v___y_1604_) == 0)
{
lean_object* v_a_1605_; 
v_a_1605_ = lean_ctor_get(v___y_1604_, 1);
lean_inc(v_a_1605_);
lean_dec_ref(v___y_1604_);
v___y_1486_ = v___y_1603_;
v_a_1487_ = v_a_1605_;
goto v___jp_1485_;
}
else
{
lean_object* v_a_1606_; lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v___y_1603_);
lean_dec_ref(v___f_1411_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1606_ = lean_ctor_get(v___y_1604_, 0);
v_a_1607_ = lean_ctor_get(v___y_1604_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___y_1604_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___y_1604_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_inc(v_a_1606_);
lean_dec(v___y_1604_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1606_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
v___jp_1616_:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_nat_dec_lt(v___x_1413_, v___x_1615_);
if (v___x_1619_ == 0)
{
v___y_1486_ = v_a_1617_;
v_a_1487_ = v_a_1618_;
goto v___jp_1485_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_nat_dec_le(v___x_1615_, v___x_1615_);
if (v___x_1620_ == 0)
{
if (v___x_1619_ == 0)
{
v___y_1486_ = v_a_1617_;
v_a_1487_ = v_a_1618_;
goto v___jp_1485_;
}
else
{
size_t v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_usize_of_nat(v___x_1615_);
lean_inc_ref(v___x_1409_);
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1409_, v_a_1376_, v___x_1374_, v___x_1621_, v___x_1412_, v_a_1618_);
v___y_1603_ = v_a_1617_;
v___y_1604_ = v___x_1622_;
goto v___jp_1602_;
}
}
else
{
size_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_usize_of_nat(v___x_1615_);
lean_inc_ref(v___x_1409_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1409_, v_a_1376_, v___x_1374_, v___x_1623_, v___x_1412_, v_a_1618_);
v___y_1603_ = v_a_1617_;
v___y_1604_ = v___x_1624_;
goto v___jp_1602_;
}
}
}
v___jp_1625_:
{
if (lean_obj_tag(v___y_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_a_1628_; 
v_a_1627_ = lean_ctor_get(v___y_1626_, 0);
lean_inc(v_a_1627_);
v_a_1628_ = lean_ctor_get(v___y_1626_, 1);
lean_inc(v_a_1628_);
lean_dec_ref(v___y_1626_);
v_a_1617_ = v_a_1627_;
v_a_1618_ = v_a_1628_;
goto v___jp_1616_;
}
else
{
lean_object* v_a_1629_; lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___f_1411_);
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1379_);
lean_dec(v_a_1376_);
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1629_ = lean_ctor_get(v___y_1626_, 0);
v_a_1630_ = lean_ctor_get(v___y_1626_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___y_1626_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___y_1626_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_inc(v_a_1629_);
lean_dec(v___y_1626_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1629_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1368_);
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1645_ = lean_ctor_get(v___x_1375_, 0);
v_a_1646_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1375_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_inc(v_a_1645_);
lean_dec(v___x_1375_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1645_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1654_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1367_);
v___x_1655_ = lean_io_error_to_string(v_a_1654_);
v___x_1656_ = 3;
v___x_1657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set_uint8(v___x_1657_, sizeof(void*)*1, v___x_1656_);
v___x_1658_ = lean_array_get_size(v_a_1350_);
v___x_1659_ = lean_array_push(v_a_1350_, v___x_1657_);
v___x_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
return v___x_1660_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v_opts_1349_);
lean_dec_ref(v_env_1348_);
v_a_1661_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1361_);
v___x_1662_ = lean_io_error_to_string(v_a_1661_);
v___x_1663_ = 3;
v___x_1664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set_uint8(v___x_1664_, sizeof(void*)*1, v___x_1663_);
v___x_1665_ = lean_array_get_size(v_a_1350_);
v___x_1666_ = lean_array_push(v_a_1350_, v___x_1664_);
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
return v___x_1667_;
}
v___jp_1352_:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1353_);
lean_ctor_set(v___x_1355_, 1, v_a_1354_);
return v___x_1355_;
}
v___jp_1356_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_a_1357_);
lean_ctor_set(v___x_1359_, 1, v_a_1358_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1668_, lean_object* v_opts_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1668_, v_opts_1669_, v_a_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1673_, lean_object* v_env_1674_, lean_object* v_attr_1675_, lean_object* v_f_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1674_, v_attr_1675_, v_f_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1678_, lean_object* v_env_1679_, lean_object* v_attr_1680_, lean_object* v_f_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1678_, v_env_1679_, v_attr_1680_, v_f_1681_);
lean_dec_ref(v_attr_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1683_, lean_object* v_inst_1684_, lean_object* v_t_1685_, lean_object* v_k_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_1685_, v_k_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1688_, lean_object* v_inst_1689_, lean_object* v_t_1690_, lean_object* v_k_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1688_, v_inst_1689_, v_t_1690_, v_k_1691_);
lean_dec(v_k_1691_);
lean_dec(v_t_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v_00_u03b2_1693_, lean_object* v_k_1694_, lean_object* v_v_1695_, lean_object* v_t_1696_, lean_object* v_hl_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1694_, v_v_1695_, v_t_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1699_, lean_object* v_t_1700_, lean_object* v_k_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1700_, v_k_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1703_, lean_object* v_t_1704_, lean_object* v_k_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1703_, v_t_1704_, v_k_1705_);
lean_dec(v_k_1705_);
lean_dec(v_t_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1707_, lean_object* v_env_1708_, lean_object* v_attr_1709_, lean_object* v_f_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1708_, v_attr_1709_, v_f_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1714_, lean_object* v_env_1715_, lean_object* v_attr_1716_, lean_object* v_f_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1714_, v_env_1715_, v_attr_1716_, v_f_1717_, v___y_1718_);
lean_dec_ref(v_attr_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_as_1723_, size_t v_i_1724_, size_t v_stop_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1721_, v_as_1723_, v_i_1724_, v_stop_1725_, v_b_1726_, v___y_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_stop_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
size_t v_i_boxed_1738_; size_t v_stop_boxed_1739_; lean_object* v_res_1740_; 
v_i_boxed_1738_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_stop_boxed_1739_ = lean_unbox_usize(v_stop_1734_);
lean_dec(v_stop_1734_);
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1730_, v___x_1731_, v_as_1732_, v_i_boxed_1738_, v_stop_boxed_1739_, v_b_1735_, v___y_1736_);
lean_dec_ref(v_as_1732_);
lean_dec(v___x_1731_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(lean_object* v_00_u03b2_1741_, lean_object* v_f_1742_, lean_object* v_as_1743_, size_t v_i_1744_, size_t v_stop_1745_, lean_object* v_b_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_1742_, v_as_1743_, v_i_1744_, v_stop_1745_, v_b_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1748_, lean_object* v_f_1749_, lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v_stop_1752_, lean_object* v_b_1753_){
_start:
{
size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; lean_object* v_res_1756_; 
v_i_boxed_1754_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1752_);
lean_dec(v_stop_1752_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(v_00_u03b2_1748_, v_f_1749_, v_as_1750_, v_i_boxed_1754_, v_stop_boxed_1755_, v_b_1753_);
lean_dec_ref(v_as_1750_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1757_, lean_object* v_f_1758_, lean_object* v_as_1759_, size_t v_i_1760_, size_t v_stop_1761_, lean_object* v_b_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1758_, v_as_1759_, v_i_1760_, v_stop_1761_, v_b_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1766_, lean_object* v_f_1767_, lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
size_t v_i_boxed_1774_; size_t v_stop_boxed_1775_; lean_object* v_res_1776_; 
v_i_boxed_1774_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1775_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1766_, v_f_1767_, v_as_1768_, v_i_boxed_1774_, v_stop_boxed_1775_, v_b_1771_, v___y_1772_);
lean_dec_ref(v_as_1768_);
return v_res_1776_;
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
