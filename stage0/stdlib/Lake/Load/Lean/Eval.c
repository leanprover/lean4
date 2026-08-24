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
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instTypeNamePackageFacetDecl;
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
extern lean_object* l_Lake_instTypeNameScriptFn;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_tail_240_);
lean_dec_ref_known(v___x_238_, 2);
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
uint8_t v___x_49089__boxed_334_; lean_object* v_res_335_; 
v___x_49089__boxed_334_ = lean_unbox(v___x_326_);
v_res_335_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_49089__boxed_334_, v_env_327_, v_opts_328_, v___x_329_, v___x_330_, v_scriptName_331_, v___y_332_);
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
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_542_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_540_, v_entries_541_, v___x_547_, v___x_548_, v___x_543_);
lean_dec_ref(v_entries_541_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_env_550_, lean_object* v_attr_551_, lean_object* v_f_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_550_, v_attr_551_, v_f_552_);
lean_dec_ref(v_attr_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_554_, lean_object* v_as_555_, size_t v_i_556_, size_t v_stop_557_, lean_object* v_b_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_eq(v_i_556_, v_stop_557_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_array_uget_borrowed(v_as_555_, v_i_556_);
lean_inc_ref(v_f_554_);
lean_inc(v___x_562_);
v___x_563_ = lean_apply_3(v_f_554_, v___x_562_, v___y_559_, lean_box(0));
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v_a_565_; lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
v_a_565_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_563_, 2);
lean_inc(v___x_562_);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_562_, v_a_564_, v_b_558_);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_556_, v___x_567_);
v_i_556_ = v___x_568_;
v_b_558_ = v___x_566_;
v___y_559_ = v_a_565_;
goto _start;
}
else
{
lean_object* v_a_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_b_558_);
lean_dec_ref(v_f_554_);
v_a_570_ = lean_ctor_get(v___x_563_, 0);
v_a_571_ = lean_ctor_get(v___x_563_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_563_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_inc(v_a_570_);
lean_dec(v___x_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec_ref(v_f_554_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_b_558_);
lean_ctor_set(v___x_579_, 1, v___y_559_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_580_, lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
size_t v_i_boxed_587_; size_t v_stop_boxed_588_; lean_object* v_res_589_; 
v_i_boxed_587_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_588_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_580_, v_as_581_, v_i_boxed_587_, v_stop_boxed_588_, v_b_584_, v___y_585_);
lean_dec_ref(v_as_581_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_590_, lean_object* v_attr_591_, lean_object* v_f_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_entries_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_entries_595_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_591_, v_env_590_);
v___x_596_ = lean_box(1);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v_entries_595_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
lean_dec_ref(v_entries_595_);
lean_dec_ref(v_f_592_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_596_);
lean_ctor_set(v___x_600_, 1, v___y_593_);
return v___x_600_;
}
else
{
size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_598_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_592_, v_entries_595_, v___x_601_, v___x_602_, v___x_596_, v___y_593_);
lean_dec_ref(v_entries_595_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_604_, lean_object* v_attr_605_, lean_object* v_f_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_604_, v_attr_605_, v_f_606_, v___y_607_);
lean_dec_ref(v_attr_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_610_, lean_object* v_opts_611_, lean_object* v_as_612_, size_t v_sz_613_, size_t v_i_614_, lean_object* v_b_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_env_610_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_b_615_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v_a_619_; lean_object* v___x_620_; 
v___x_618_ = l_Lake_instTypeNameModuleFacetDecl;
v_a_619_ = lean_array_uget_borrowed(v_as_612_, v_i_614_);
lean_inc(v_a_619_);
lean_inc_ref(v_env_610_);
v___x_620_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_610_, v_opts_611_, v___x_618_, v_a_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_b_615_);
lean_dec_ref(v_env_610_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v_name_630_; lean_object* v_config_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_642_; 
v_a_629_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_620_, 1);
v_name_630_ = lean_ctor_get(v_a_629_, 0);
v_config_631_ = lean_ctor_get(v_a_629_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_a_629_);
if (v_isSharedCheck_642_ == 0)
{
v___x_633_ = v_a_629_;
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_config_631_);
lean_inc(v_name_630_);
lean_dec(v_a_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_642_;
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
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_name_630_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_config_631_);
v___x_636_ = v_reuseFailAlloc_641_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; 
v___x_637_ = lean_array_push(v_b_615_, v___x_636_);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_614_, v___x_638_);
v_i_614_ = v___x_639_;
v_b_615_ = v___x_637_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(lean_object* v_env_643_, lean_object* v_opts_644_, lean_object* v_as_645_, lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_b_648_){
_start:
{
size_t v_sz_boxed_649_; size_t v_i_boxed_650_; lean_object* v_res_651_; 
v_sz_boxed_649_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_650_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_643_, v_opts_644_, v_as_645_, v_sz_boxed_649_, v_i_boxed_650_, v_b_648_);
lean_dec_ref(v_as_645_);
lean_dec_ref(v_opts_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v___x_655_, lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_, lean_object* v_b_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_a_663_; lean_object* v_a_664_; uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v_name_670_; lean_object* v_kind_671_; lean_object* v_config_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_669_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
v_name_670_ = lean_ctor_get(v___x_669_, 1);
v_kind_671_ = lean_ctor_get(v___x_669_, 2);
v_config_672_ = lean_ctor_get(v___x_669_, 3);
v___x_673_ = l_Lake_LeanExe_keyword;
v___x_674_ = lean_name_eq(v_kind_671_, v___x_673_);
if (v___x_674_ == 0)
{
v_a_663_ = v_b_659_;
v_a_664_ = v___y_660_;
goto v___jp_662_;
}
else
{
lean_object* v_root_675_; lean_object* v___x_676_; 
v_root_675_ = lean_ctor_get(v_config_672_, 2);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_659_, v_root_675_);
if (lean_obj_tag(v___x_676_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_b_659_);
v_val_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0));
v___x_679_ = lean_string_append(v___x_655_, v___x_678_);
lean_inc(v_name_670_);
v___x_680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_670_, v___x_674_);
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
lean_dec_ref(v___x_680_);
v___x_682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1));
v___x_683_ = lean_string_append(v___x_681_, v___x_682_);
lean_inc(v_root_675_);
v___x_684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_675_, v___x_674_);
v___x_685_ = lean_string_append(v___x_683_, v___x_684_);
lean_dec_ref(v___x_684_);
v___x_686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2));
v___x_687_ = lean_string_append(v___x_685_, v___x_686_);
v___x_688_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_677_, v___x_674_);
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
lean_dec_ref(v___x_688_);
v___x_690_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
v___x_692_ = 3;
v___x_693_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*1, v___x_692_);
v___x_694_ = lean_array_get_size(v___y_660_);
v___x_695_ = lean_array_push(v___y_660_, v___x_693_);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v___x_676_);
lean_inc(v_name_670_);
lean_inc(v_root_675_);
v___x_697_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_675_, v_name_670_, v_b_659_);
v_a_663_ = v___x_697_;
v_a_664_ = v___y_660_;
goto v___jp_662_;
}
}
}
else
{
lean_object* v___x_698_; 
lean_dec_ref(v___x_655_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_b_659_);
lean_ctor_set(v___x_698_, 1, v___y_660_);
return v___x_698_;
}
v___jp_662_:
{
size_t v___x_665_; size_t v___x_666_; 
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_657_, v___x_665_);
v_i_657_ = v___x_666_;
v_b_659_ = v_a_663_;
v___y_660_ = v_a_664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v___x_699_, lean_object* v_as_700_, lean_object* v_i_701_, lean_object* v_stop_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
size_t v_i_boxed_706_; size_t v_stop_boxed_707_; lean_object* v_res_708_; 
v_i_boxed_706_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_stop_boxed_707_ = lean_unbox_usize(v_stop_702_);
lean_dec(v_stop_702_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_699_, v_as_700_, v_i_boxed_706_, v_stop_boxed_707_, v_b_703_, v___y_704_);
lean_dec_ref(v_as_700_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v___x_713_, size_t v_sz_714_, size_t v_i_715_, lean_object* v_bs_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_lt(v_i_715_, v_sz_714_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v___x_713_);
lean_dec_ref(v_a_711_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_bs_716_);
lean_ctor_set(v___x_720_, 1, v___y_717_);
return v___x_720_;
}
else
{
lean_object* v_toTreeMap_721_; lean_object* v_v_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; lean_object* v_a_726_; lean_object* v_a_727_; lean_object* v___x_732_; 
v_toTreeMap_721_ = lean_ctor_get(v_a_711_, 0);
v_v_722_ = lean_array_uget(v_bs_716_, v_i_715_);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_716_, v_i_715_, v___x_723_);
v___x_732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_721_, v_v_722_);
if (lean_obj_tag(v___x_732_) == 1)
{
lean_object* v_val_733_; lean_object* v_name_734_; 
lean_dec(v_v_722_);
v_val_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v___x_732_, 1);
v_name_734_ = lean_ctor_get(v_val_733_, 1);
lean_inc(v_name_734_);
lean_dec(v_val_733_);
v_a_726_ = v_name_734_;
v_a_727_ = v___y_717_;
goto v___jp_725_;
}
else
{
uint8_t v___x_735_; 
lean_dec(v___x_732_);
v___x_735_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_722_, v_a_712_);
if (v___x_735_ == 0)
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_bs_x27_724_);
v_isSharedCheck_752_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_753_ = lean_ctor_get(v_a_711_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_a_711_, 0);
lean_dec(v_unused_754_);
v___x_737_ = v_a_711_;
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
else
{
lean_dec(v_a_711_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_740_ = lean_string_append(v___x_713_, v___x_739_);
v___x_741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_722_, v___x_719_);
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_744_ = lean_string_append(v___x_742_, v___x_743_);
v___x_745_ = 3;
v___x_746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*1, v___x_745_);
v___x_747_ = lean_array_get_size(v___y_717_);
v___x_748_ = lean_array_push(v___y_717_, v___x_746_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 1, v___x_748_);
lean_ctor_set(v___x_737_, 0, v___x_747_);
v___x_750_ = v___x_737_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
v_a_726_ = v_v_722_;
v_a_727_ = v___y_717_;
goto v___jp_725_;
}
}
v___jp_725_:
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_715_, v___x_728_);
v___x_730_ = lean_array_uset(v_bs_x27_724_, v_i_715_, v_a_726_);
v_i_715_ = v___x_729_;
v_bs_716_ = v___x_730_;
v___y_717_ = v_a_727_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v___x_757_, lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_bs_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_764_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_755_, v_a_756_, v___x_757_, v_sz_boxed_763_, v_i_boxed_764_, v_bs_760_, v___y_761_);
lean_dec(v_a_756_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v___x_769_, size_t v_sz_770_, size_t v_i_771_, lean_object* v_bs_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_lt(v_i_771_, v_sz_770_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v___x_769_);
lean_dec_ref(v_a_767_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_bs_772_);
lean_ctor_set(v___x_776_, 1, v___y_773_);
return v___x_776_;
}
else
{
lean_object* v_toTreeMap_777_; lean_object* v_v_778_; lean_object* v___x_779_; lean_object* v_bs_x27_780_; lean_object* v_a_782_; lean_object* v_a_783_; lean_object* v___x_788_; 
v_toTreeMap_777_ = lean_ctor_get(v_a_767_, 0);
v_v_778_ = lean_array_uget(v_bs_772_, v_i_771_);
v___x_779_ = lean_unsigned_to_nat(0u);
v_bs_x27_780_ = lean_array_uset(v_bs_772_, v_i_771_, v___x_779_);
v___x_788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_777_, v_v_778_);
if (lean_obj_tag(v___x_788_) == 1)
{
lean_object* v_val_789_; lean_object* v_name_790_; 
lean_dec(v_v_778_);
v_val_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v___x_788_, 1);
v_name_790_ = lean_ctor_get(v_val_789_, 1);
lean_inc(v_name_790_);
lean_dec(v_val_789_);
v_a_782_ = v_name_790_;
v_a_783_ = v___y_773_;
goto v___jp_781_;
}
else
{
uint8_t v___x_791_; 
lean_dec(v___x_788_);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_778_, v_a_768_);
if (v___x_791_ == 0)
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_bs_x27_780_);
v_isSharedCheck_808_ = !lean_is_exclusive(v_a_767_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_809_ = lean_ctor_get(v_a_767_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_a_767_, 0);
lean_dec(v_unused_810_);
v___x_793_ = v_a_767_;
v_isShared_794_ = v_isSharedCheck_808_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_a_767_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_808_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_796_ = lean_string_append(v___x_769_, v___x_795_);
v___x_797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_778_, v___x_775_);
v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
lean_dec_ref(v___x_797_);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0));
v___x_800_ = lean_string_append(v___x_798_, v___x_799_);
v___x_801_ = 3;
v___x_802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1, v___x_801_);
v___x_803_ = lean_array_get_size(v___y_773_);
v___x_804_ = lean_array_push(v___y_773_, v___x_802_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 1);
lean_ctor_set(v___x_793_, 1, v___x_804_);
lean_ctor_set(v___x_793_, 0, v___x_803_);
v___x_806_ = v___x_793_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
v_a_782_ = v_v_778_;
v_a_783_ = v___y_773_;
goto v___jp_781_;
}
}
v___jp_781_:
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_771_, v___x_784_);
v___x_786_ = lean_array_uset(v_bs_x27_780_, v_i_771_, v_a_782_);
v_i_771_ = v___x_785_;
v_bs_772_ = v___x_786_;
v___y_773_ = v_a_783_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v___x_813_, lean_object* v_sz_814_, lean_object* v_i_815_, lean_object* v_bs_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v_sz_boxed_819_ = lean_unbox_usize(v_sz_814_);
lean_dec(v_sz_814_);
v_i_boxed_820_ = lean_unbox_usize(v_i_815_);
lean_dec(v_i_815_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_811_, v_a_812_, v___x_813_, v_sz_boxed_819_, v_i_boxed_820_, v_bs_816_, v___y_817_);
lean_dec(v_a_812_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_823_, lean_object* v___x_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_bs_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec_ref(v___x_824_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_bs_827_);
lean_ctor_set(v___x_831_, 1, v___y_828_);
return v___x_831_;
}
else
{
lean_object* v_v_832_; lean_object* v___x_833_; 
v_v_832_ = lean_array_uget_borrowed(v_bs_827_, v_i_826_);
v___x_833_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_823_, v_v_832_);
if (lean_obj_tag(v___x_833_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_835_; lean_object* v_bs_x27_836_; size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_val_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = lean_unsigned_to_nat(0u);
v_bs_x27_836_ = lean_array_uset(v_bs_827_, v_i_826_, v___x_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_826_, v___x_837_);
v___x_839_ = lean_array_uset(v_bs_x27_836_, v_i_826_, v_val_834_);
v_i_826_ = v___x_838_;
v_bs_827_ = v___x_839_;
goto _start;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc(v_v_832_);
lean_dec(v___x_833_);
lean_dec_ref(v_bs_827_);
v___x_841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_842_ = lean_string_append(v___x_824_, v___x_841_);
v___x_843_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_832_, v___x_830_);
v___x_844_ = lean_string_append(v___x_842_, v___x_843_);
lean_dec_ref(v___x_843_);
v___x_845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_846_ = lean_string_append(v___x_844_, v___x_845_);
v___x_847_ = 3;
v___x_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*1, v___x_847_);
v___x_849_ = lean_array_get_size(v___y_828_);
v___x_850_ = lean_array_push(v___y_828_, v___x_848_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_852_, lean_object* v___x_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_bs_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
size_t v_sz_boxed_859_; size_t v_i_boxed_860_; lean_object* v_res_861_; 
v_sz_boxed_859_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_860_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_852_, v___x_853_, v_sz_boxed_859_, v_i_boxed_860_, v_bs_856_, v___y_857_);
lean_dec(v_a_852_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_862_, lean_object* v_opts_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_bs_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec_ref(v_env_862_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v_bs_866_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v_v_870_; lean_object* v___x_871_; 
v___x_869_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
v_v_870_ = lean_array_uget_borrowed(v_bs_866_, v_i_865_);
lean_inc(v_v_870_);
lean_inc_ref(v_env_862_);
v___x_871_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_862_, v_opts_863_, v___x_869_, v_v_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_bs_866_);
lean_dec_ref(v_env_862_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v_bs_x27_882_; size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_871_, 1);
v___x_881_ = lean_unsigned_to_nat(0u);
v_bs_x27_882_ = lean_array_uset(v_bs_866_, v_i_865_, v___x_881_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_add(v_i_865_, v___x_883_);
v___x_885_ = lean_array_uset(v_bs_x27_882_, v_i_865_, v_a_880_);
v_i_865_ = v___x_884_;
v_bs_866_ = v___x_885_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_887_, lean_object* v_opts_888_, lean_object* v_sz_889_, lean_object* v_i_890_, lean_object* v_bs_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v_i_boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_889_);
lean_dec(v_sz_889_);
v_i_boxed_893_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_887_, v_opts_888_, v_sz_boxed_892_, v_i_boxed_893_, v_bs_891_);
lean_dec_ref(v_opts_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_895_, lean_object* v_opts_896_, lean_object* v_as_897_, size_t v_sz_898_, size_t v_i_899_, lean_object* v_b_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_899_, v_sz_898_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v_env_895_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v_b_900_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_905_; 
v___x_903_ = l_Lake_instTypeNamePackageFacetDecl;
v_a_904_ = lean_array_uget_borrowed(v_as_897_, v_i_899_);
lean_inc(v_a_904_);
lean_inc_ref(v_env_895_);
v___x_905_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_895_, v_opts_896_, v___x_903_, v_a_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_b_900_);
lean_dec_ref(v_env_895_);
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v_name_915_; lean_object* v_config_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_927_; 
v_a_914_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_905_, 1);
v_name_915_ = lean_ctor_get(v_a_914_, 0);
v_config_916_ = lean_ctor_get(v_a_914_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_927_ == 0)
{
v___x_918_ = v_a_914_;
v_isShared_919_ = v_isSharedCheck_927_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_config_916_);
lean_inc(v_name_915_);
lean_dec(v_a_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_927_;
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
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_name_915_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_config_916_);
v___x_921_ = v_reuseFailAlloc_926_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; 
v___x_922_ = lean_array_push(v_b_900_, v___x_921_);
v___x_923_ = ((size_t)1ULL);
v___x_924_ = lean_usize_add(v_i_899_, v___x_923_);
v_i_899_ = v___x_924_;
v_b_900_ = v___x_922_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_928_, lean_object* v_opts_929_, lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_935_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_928_, v_opts_929_, v_as_930_, v_sz_boxed_934_, v_i_boxed_935_, v_b_933_);
lean_dec_ref(v_as_930_);
lean_dec_ref(v_opts_929_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_937_, lean_object* v_opts_938_, lean_object* v_as_939_, size_t v_sz_940_, size_t v_i_941_, lean_object* v_b_942_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = lean_usize_dec_lt(v_i_941_, v_sz_940_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_dec_ref(v_env_937_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_942_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v_a_946_; lean_object* v___x_947_; 
v___x_945_ = l_Lake_instTypeNameLibraryFacetDecl;
v_a_946_ = lean_array_uget_borrowed(v_as_939_, v_i_941_);
lean_inc(v_a_946_);
lean_inc_ref(v_env_937_);
v___x_947_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_937_, v_opts_938_, v___x_945_, v_a_946_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_b_942_);
lean_dec_ref(v_env_937_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_a_956_; lean_object* v_name_957_; lean_object* v_config_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_969_; 
v_a_956_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_947_, 1);
v_name_957_ = lean_ctor_get(v_a_956_, 0);
v_config_958_ = lean_ctor_get(v_a_956_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_969_ == 0)
{
v___x_960_ = v_a_956_;
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_config_958_);
lean_inc(v_name_957_);
lean_dec(v_a_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_969_;
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
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_name_957_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_config_958_);
v___x_963_ = v_reuseFailAlloc_968_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; size_t v___x_965_; size_t v___x_966_; 
v___x_964_ = lean_array_push(v_b_942_, v___x_963_);
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_941_, v___x_965_);
v_i_941_ = v___x_966_;
v_b_942_ = v___x_964_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_970_, lean_object* v_opts_971_, lean_object* v_as_972_, lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_b_975_){
_start:
{
size_t v_sz_boxed_976_; size_t v_i_boxed_977_; lean_object* v_res_978_; 
v_sz_boxed_976_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_977_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_970_, v_opts_971_, v_as_972_, v_sz_boxed_976_, v_i_boxed_977_, v_b_975_);
lean_dec_ref(v_as_972_);
lean_dec_ref(v_opts_971_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_t_979_, lean_object* v_k_980_){
_start:
{
if (lean_obj_tag(v_t_979_) == 0)
{
lean_object* v_k_981_; lean_object* v_v_982_; lean_object* v_l_983_; lean_object* v_r_984_; uint8_t v___x_985_; 
v_k_981_ = lean_ctor_get(v_t_979_, 1);
v_v_982_ = lean_ctor_get(v_t_979_, 2);
v_l_983_ = lean_ctor_get(v_t_979_, 3);
v_r_984_ = lean_ctor_get(v_t_979_, 4);
v___x_985_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_980_, v_k_981_);
switch(v___x_985_)
{
case 0:
{
v_t_979_ = v_l_983_;
goto _start;
}
case 1:
{
lean_object* v___x_987_; 
lean_inc(v_v_982_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v_v_982_);
return v___x_987_;
}
default: 
{
v_t_979_ = v_r_984_;
goto _start;
}
}
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_box(0);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_t_990_, lean_object* v_k_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_990_, v_k_991_);
lean_dec(v_k_991_);
lean_dec(v_t_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(lean_object* v_k_993_, lean_object* v_v_994_, lean_object* v_t_995_){
_start:
{
if (lean_obj_tag(v_t_995_) == 0)
{
lean_object* v_size_996_; lean_object* v_k_997_; lean_object* v_v_998_; lean_object* v_l_999_; lean_object* v_r_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1280_; 
v_size_996_ = lean_ctor_get(v_t_995_, 0);
v_k_997_ = lean_ctor_get(v_t_995_, 1);
v_v_998_ = lean_ctor_get(v_t_995_, 2);
v_l_999_ = lean_ctor_get(v_t_995_, 3);
v_r_1000_ = lean_ctor_get(v_t_995_, 4);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_t_995_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1002_ = v_t_995_;
v_isShared_1003_ = v_isSharedCheck_1280_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_r_1000_);
lean_inc(v_l_999_);
lean_inc(v_v_998_);
lean_inc(v_k_997_);
lean_inc(v_size_996_);
lean_dec(v_t_995_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1280_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v___x_1004_; 
v___x_1004_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_993_, v_k_997_);
switch(v___x_1004_)
{
case 0:
{
lean_object* v_impl_1005_; lean_object* v___x_1006_; 
lean_dec(v_size_996_);
v_impl_1005_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_993_, v_v_994_, v_l_999_);
v___x_1006_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1000_) == 0)
{
lean_object* v_size_1007_; lean_object* v_size_1008_; lean_object* v_k_1009_; lean_object* v_v_1010_; lean_object* v_l_1011_; lean_object* v_r_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_size_1007_ = lean_ctor_get(v_r_1000_, 0);
v_size_1008_ = lean_ctor_get(v_impl_1005_, 0);
lean_inc(v_size_1008_);
v_k_1009_ = lean_ctor_get(v_impl_1005_, 1);
lean_inc(v_k_1009_);
v_v_1010_ = lean_ctor_get(v_impl_1005_, 2);
lean_inc(v_v_1010_);
v_l_1011_ = lean_ctor_get(v_impl_1005_, 3);
lean_inc(v_l_1011_);
v_r_1012_ = lean_ctor_get(v_impl_1005_, 4);
lean_inc(v_r_1012_);
v___x_1013_ = lean_unsigned_to_nat(3u);
v___x_1014_ = lean_nat_mul(v___x_1013_, v_size_1007_);
v___x_1015_ = lean_nat_dec_lt(v___x_1014_, v_size_1008_);
lean_dec(v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_dec(v_r_1012_);
lean_dec(v_l_1011_);
lean_dec(v_v_1010_);
lean_dec(v_k_1009_);
v___x_1016_ = lean_nat_add(v___x_1006_, v_size_1008_);
lean_dec(v_size_1008_);
v___x_1017_ = lean_nat_add(v___x_1016_, v_size_1007_);
lean_dec(v___x_1016_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 3, v_impl_1005_);
lean_ctor_set(v___x_1002_, 0, v___x_1017_);
v___x_1019_ = v___x_1002_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_impl_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_r_1000_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1086_; 
v_isSharedCheck_1086_ = !lean_is_exclusive(v_impl_1005_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; lean_object* v_unused_1091_; 
v_unused_1087_ = lean_ctor_get(v_impl_1005_, 4);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_impl_1005_, 3);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_impl_1005_, 2);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_impl_1005_, 1);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_impl_1005_, 0);
lean_dec(v_unused_1091_);
v___x_1022_ = v_impl_1005_;
v_isShared_1023_ = v_isSharedCheck_1086_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v_impl_1005_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1086_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_size_1024_; lean_object* v_size_1025_; lean_object* v_k_1026_; lean_object* v_v_1027_; lean_object* v_l_1028_; lean_object* v_r_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_size_1024_ = lean_ctor_get(v_l_1011_, 0);
v_size_1025_ = lean_ctor_get(v_r_1012_, 0);
v_k_1026_ = lean_ctor_get(v_r_1012_, 1);
v_v_1027_ = lean_ctor_get(v_r_1012_, 2);
v_l_1028_ = lean_ctor_get(v_r_1012_, 3);
v_r_1029_ = lean_ctor_get(v_r_1012_, 4);
v___x_1030_ = lean_unsigned_to_nat(2u);
v___x_1031_ = lean_nat_mul(v___x_1030_, v_size_1024_);
v___x_1032_ = lean_nat_dec_lt(v_size_1025_, v___x_1031_);
lean_dec(v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1061_; 
lean_inc(v_r_1029_);
lean_inc(v_l_1028_);
lean_inc(v_v_1027_);
lean_inc(v_k_1026_);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_r_1012_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; lean_object* v_unused_1064_; lean_object* v_unused_1065_; lean_object* v_unused_1066_; 
v_unused_1062_ = lean_ctor_get(v_r_1012_, 4);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_r_1012_, 3);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_r_1012_, 2);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_r_1012_, 1);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_r_1012_, 0);
lean_dec(v_unused_1066_);
v___x_1034_ = v_r_1012_;
v_isShared_1035_ = v_isSharedCheck_1061_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_r_1012_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1061_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___x_1049_; lean_object* v___y_1051_; 
v___x_1036_ = lean_nat_add(v___x_1006_, v_size_1008_);
lean_dec(v_size_1008_);
v___x_1037_ = lean_nat_add(v___x_1036_, v_size_1007_);
lean_dec(v___x_1036_);
v___x_1049_ = lean_nat_add(v___x_1006_, v_size_1024_);
if (lean_obj_tag(v_l_1028_) == 0)
{
lean_object* v_size_1059_; 
v_size_1059_ = lean_ctor_get(v_l_1028_, 0);
lean_inc(v_size_1059_);
v___y_1051_ = v_size_1059_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___y_1051_ = v___x_1060_;
goto v___jp_1050_;
}
v___jp_1038_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_nat_add(v___y_1039_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec(v___y_1039_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v_r_1000_);
lean_ctor_set(v___x_1034_, 3, v_r_1029_);
lean_ctor_set(v___x_1034_, 2, v_v_998_);
lean_ctor_set(v___x_1034_, 1, v_k_997_);
lean_ctor_set(v___x_1034_, 0, v___x_1042_);
v___x_1044_ = v___x_1034_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_r_1029_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_r_1000_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 4, v___x_1044_);
lean_ctor_set(v___x_1022_, 3, v___y_1040_);
lean_ctor_set(v___x_1022_, 2, v_v_1027_);
lean_ctor_set(v___x_1022_, 1, v_k_1026_);
lean_ctor_set(v___x_1022_, 0, v___x_1037_);
v___x_1046_ = v___x_1022_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_1026_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_1027_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v___y_1040_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
v___jp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_nat_add(v___x_1049_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec(v___x_1049_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_l_1028_);
lean_ctor_set(v___x_1002_, 3, v_l_1011_);
lean_ctor_set(v___x_1002_, 2, v_v_1010_);
lean_ctor_set(v___x_1002_, 1, v_k_1009_);
lean_ctor_set(v___x_1002_, 0, v___x_1052_);
v___x_1054_ = v___x_1002_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_l_1011_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_l_1028_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_nat_add(v___x_1006_, v_size_1007_);
if (lean_obj_tag(v_r_1029_) == 0)
{
lean_object* v_size_1056_; 
v_size_1056_ = lean_ctor_get(v_r_1029_, 0);
lean_inc(v_size_1056_);
v___y_1039_ = v___x_1055_;
v___y_1040_ = v___x_1054_;
v___y_1041_ = v_size_1056_;
goto v___jp_1038_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___y_1039_ = v___x_1055_;
v___y_1040_ = v___x_1054_;
v___y_1041_ = v___x_1057_;
goto v___jp_1038_;
}
}
}
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_del_object(v___x_1002_);
v___x_1067_ = lean_nat_add(v___x_1006_, v_size_1008_);
lean_dec(v_size_1008_);
v___x_1068_ = lean_nat_add(v___x_1067_, v_size_1007_);
lean_dec(v___x_1067_);
v___x_1069_ = lean_nat_add(v___x_1006_, v_size_1007_);
v___x_1070_ = lean_nat_add(v___x_1069_, v_size_1025_);
lean_dec(v___x_1069_);
lean_inc_ref(v_r_1000_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 4, v_r_1000_);
lean_ctor_set(v___x_1022_, 3, v_r_1012_);
lean_ctor_set(v___x_1022_, 2, v_v_998_);
lean_ctor_set(v___x_1022_, 1, v_k_997_);
lean_ctor_set(v___x_1022_, 0, v___x_1070_);
v___x_1072_ = v___x_1022_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_r_1012_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_r_1000_);
v___x_1072_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_isSharedCheck_1079_ = !lean_is_exclusive(v_r_1000_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; lean_object* v_unused_1081_; lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; 
v_unused_1080_ = lean_ctor_get(v_r_1000_, 4);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_r_1000_, 3);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_r_1000_, 2);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_r_1000_, 1);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_r_1000_, 0);
lean_dec(v_unused_1084_);
v___x_1074_ = v_r_1000_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v_r_1000_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 4, v___x_1072_);
lean_ctor_set(v___x_1074_, 3, v_l_1011_);
lean_ctor_set(v___x_1074_, 2, v_v_1010_);
lean_ctor_set(v___x_1074_, 1, v_k_1009_);
lean_ctor_set(v___x_1074_, 0, v___x_1068_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_l_1011_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___x_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1092_; 
v_l_1092_ = lean_ctor_get(v_impl_1005_, 3);
lean_inc(v_l_1092_);
if (lean_obj_tag(v_l_1092_) == 0)
{
lean_object* v_r_1093_; lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1106_; 
v_r_1093_ = lean_ctor_get(v_impl_1005_, 4);
v_k_1094_ = lean_ctor_get(v_impl_1005_, 1);
v_v_1095_ = lean_ctor_get(v_impl_1005_, 2);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_impl_1005_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; 
v_unused_1107_ = lean_ctor_get(v_impl_1005_, 3);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_impl_1005_, 0);
lean_dec(v_unused_1108_);
v___x_1097_ = v_impl_1005_;
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_r_1093_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
lean_dec(v_impl_1005_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1093_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 3, v_r_1093_);
lean_ctor_set(v___x_1097_, 2, v_v_998_);
lean_ctor_set(v___x_1097_, 1, v_k_997_);
lean_ctor_set(v___x_1097_, 0, v___x_1006_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_r_1093_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v___x_1101_);
lean_ctor_set(v___x_1002_, 3, v_l_1092_);
lean_ctor_set(v___x_1002_, 2, v_v_1095_);
lean_ctor_set(v___x_1002_, 1, v_k_1094_);
lean_ctor_set(v___x_1002_, 0, v___x_1099_);
v___x_1103_ = v___x_1002_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v___x_1101_);
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
else
{
lean_object* v_r_1109_; 
v_r_1109_ = lean_ctor_get(v_impl_1005_, 4);
lean_inc(v_r_1109_);
if (lean_obj_tag(v_r_1109_) == 0)
{
lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1134_; 
v_k_1110_ = lean_ctor_get(v_impl_1005_, 1);
v_v_1111_ = lean_ctor_get(v_impl_1005_, 2);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_impl_1005_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1135_ = lean_ctor_get(v_impl_1005_, 4);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_impl_1005_, 3);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_impl_1005_, 0);
lean_dec(v_unused_1137_);
v___x_1113_ = v_impl_1005_;
v_isShared_1114_ = v_isSharedCheck_1134_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_v_1111_);
lean_inc(v_k_1110_);
lean_dec(v_impl_1005_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1134_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_k_1115_; lean_object* v_v_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1130_; 
v_k_1115_ = lean_ctor_get(v_r_1109_, 1);
v_v_1116_ = lean_ctor_get(v_r_1109_, 2);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_r_1109_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; lean_object* v_unused_1132_; lean_object* v_unused_1133_; 
v_unused_1131_ = lean_ctor_get(v_r_1109_, 4);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_r_1109_, 3);
lean_dec(v_unused_1132_);
v_unused_1133_ = lean_ctor_get(v_r_1109_, 0);
lean_dec(v_unused_1133_);
v___x_1118_ = v_r_1109_;
v_isShared_1119_ = v_isSharedCheck_1130_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_v_1116_);
lean_inc(v_k_1115_);
lean_dec(v_r_1109_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1130_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_unsigned_to_nat(3u);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 4, v_l_1092_);
lean_ctor_set(v___x_1118_, 3, v_l_1092_);
lean_ctor_set(v___x_1118_, 2, v_v_1111_);
lean_ctor_set(v___x_1118_, 1, v_k_1110_);
lean_ctor_set(v___x_1118_, 0, v___x_1006_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v_l_1092_);
v___x_1122_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 4, v_l_1092_);
lean_ctor_set(v___x_1113_, 2, v_v_998_);
lean_ctor_set(v___x_1113_, 1, v_k_997_);
lean_ctor_set(v___x_1113_, 0, v___x_1006_);
v___x_1124_ = v___x_1113_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_l_1092_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v___x_1124_);
lean_ctor_set(v___x_1002_, 3, v___x_1122_);
lean_ctor_set(v___x_1002_, 2, v_v_1116_);
lean_ctor_set(v___x_1002_, 1, v_k_1115_);
lean_ctor_set(v___x_1002_, 0, v___x_1120_);
v___x_1126_ = v___x_1002_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(2u);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_r_1109_);
lean_ctor_set(v___x_1002_, 3, v_impl_1005_);
lean_ctor_set(v___x_1002_, 0, v___x_1138_);
v___x_1140_ = v___x_1002_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_impl_1005_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_r_1109_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1143_; 
lean_dec(v_v_998_);
lean_dec(v_k_997_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 2, v_v_994_);
lean_ctor_set(v___x_1002_, 1, v_k_993_);
v___x_1143_ = v___x_1002_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_size_996_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_993_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_994_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_l_999_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1000_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
default: 
{
lean_object* v_impl_1145_; lean_object* v___x_1146_; 
lean_dec(v_size_996_);
v_impl_1145_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_993_, v_v_994_, v_r_1000_);
v___x_1146_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_999_) == 0)
{
lean_object* v_size_1147_; lean_object* v_size_1148_; lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v_l_1151_; lean_object* v_r_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v_size_1147_ = lean_ctor_get(v_l_999_, 0);
v_size_1148_ = lean_ctor_get(v_impl_1145_, 0);
lean_inc(v_size_1148_);
v_k_1149_ = lean_ctor_get(v_impl_1145_, 1);
lean_inc(v_k_1149_);
v_v_1150_ = lean_ctor_get(v_impl_1145_, 2);
lean_inc(v_v_1150_);
v_l_1151_ = lean_ctor_get(v_impl_1145_, 3);
lean_inc(v_l_1151_);
v_r_1152_ = lean_ctor_get(v_impl_1145_, 4);
lean_inc(v_r_1152_);
v___x_1153_ = lean_unsigned_to_nat(3u);
v___x_1154_ = lean_nat_mul(v___x_1153_, v_size_1147_);
v___x_1155_ = lean_nat_dec_lt(v___x_1154_, v_size_1148_);
lean_dec(v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_dec(v_r_1152_);
lean_dec(v_l_1151_);
lean_dec(v_v_1150_);
lean_dec(v_k_1149_);
v___x_1156_ = lean_nat_add(v___x_1146_, v_size_1147_);
v___x_1157_ = lean_nat_add(v___x_1156_, v_size_1148_);
lean_dec(v_size_1148_);
lean_dec(v___x_1156_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_impl_1145_);
lean_ctor_set(v___x_1002_, 0, v___x_1157_);
v___x_1159_ = v___x_1002_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_999_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_impl_1145_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1224_; 
v_isSharedCheck_1224_ = !lean_is_exclusive(v_impl_1145_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1225_ = lean_ctor_get(v_impl_1145_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_impl_1145_, 3);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_impl_1145_, 2);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_impl_1145_, 1);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_impl_1145_, 0);
lean_dec(v_unused_1229_);
v___x_1162_ = v_impl_1145_;
v_isShared_1163_ = v_isSharedCheck_1224_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v_impl_1145_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1224_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_size_1164_; lean_object* v_k_1165_; lean_object* v_v_1166_; lean_object* v_l_1167_; lean_object* v_r_1168_; lean_object* v_size_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_size_1164_ = lean_ctor_get(v_l_1151_, 0);
v_k_1165_ = lean_ctor_get(v_l_1151_, 1);
v_v_1166_ = lean_ctor_get(v_l_1151_, 2);
v_l_1167_ = lean_ctor_get(v_l_1151_, 3);
v_r_1168_ = lean_ctor_get(v_l_1151_, 4);
v_size_1169_ = lean_ctor_get(v_r_1152_, 0);
v___x_1170_ = lean_unsigned_to_nat(2u);
v___x_1171_ = lean_nat_mul(v___x_1170_, v_size_1169_);
v___x_1172_ = lean_nat_dec_lt(v_size_1164_, v___x_1171_);
lean_dec(v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1200_; 
lean_inc(v_r_1168_);
lean_inc(v_l_1167_);
lean_inc(v_v_1166_);
lean_inc(v_k_1165_);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_l_1151_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; lean_object* v_unused_1202_; lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; 
v_unused_1201_ = lean_ctor_get(v_l_1151_, 4);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_l_1151_, 3);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_l_1151_, 2);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_l_1151_, 1);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_l_1151_, 0);
lean_dec(v_unused_1205_);
v___x_1174_ = v_l_1151_;
v_isShared_1175_ = v_isSharedCheck_1200_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_l_1151_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1200_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1190_; 
v___x_1176_ = lean_nat_add(v___x_1146_, v_size_1147_);
v___x_1177_ = lean_nat_add(v___x_1176_, v_size_1148_);
lean_dec(v_size_1148_);
if (lean_obj_tag(v_l_1167_) == 0)
{
lean_object* v_size_1198_; 
v_size_1198_ = lean_ctor_get(v_l_1167_, 0);
lean_inc(v_size_1198_);
v___y_1190_ = v_size_1198_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
v___y_1190_ = v___x_1199_;
goto v___jp_1189_;
}
v___jp_1178_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_nat_add(v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v_r_1152_);
lean_ctor_set(v___x_1174_, 3, v_r_1168_);
lean_ctor_set(v___x_1174_, 2, v_v_1150_);
lean_ctor_set(v___x_1174_, 1, v_k_1149_);
lean_ctor_set(v___x_1174_, 0, v___x_1182_);
v___x_1184_ = v___x_1174_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_r_1168_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_r_1152_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 4, v___x_1184_);
lean_ctor_set(v___x_1162_, 3, v___y_1179_);
lean_ctor_set(v___x_1162_, 2, v_v_1166_);
lean_ctor_set(v___x_1162_, 1, v_k_1165_);
lean_ctor_set(v___x_1162_, 0, v___x_1177_);
v___x_1186_ = v___x_1162_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_k_1165_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_v_1166_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v___y_1179_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_nat_add(v___x_1176_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec(v___x_1176_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_l_1167_);
lean_ctor_set(v___x_1002_, 0, v___x_1191_);
v___x_1193_ = v___x_1002_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_l_999_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_l_1167_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_nat_add(v___x_1146_, v_size_1169_);
if (lean_obj_tag(v_r_1168_) == 0)
{
lean_object* v_size_1195_; 
v_size_1195_ = lean_ctor_get(v_r_1168_, 0);
lean_inc(v_size_1195_);
v___y_1179_ = v___x_1193_;
v___y_1180_ = v___x_1194_;
v___y_1181_ = v_size_1195_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___y_1179_ = v___x_1193_;
v___y_1180_ = v___x_1194_;
v___y_1181_ = v___x_1196_;
goto v___jp_1178_;
}
}
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_del_object(v___x_1002_);
v___x_1206_ = lean_nat_add(v___x_1146_, v_size_1147_);
v___x_1207_ = lean_nat_add(v___x_1206_, v_size_1148_);
lean_dec(v_size_1148_);
v___x_1208_ = lean_nat_add(v___x_1206_, v_size_1164_);
lean_dec(v___x_1206_);
lean_inc_ref(v_l_999_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 4, v_l_1151_);
lean_ctor_set(v___x_1162_, 3, v_l_999_);
lean_ctor_set(v___x_1162_, 2, v_v_998_);
lean_ctor_set(v___x_1162_, 1, v_k_997_);
lean_ctor_set(v___x_1162_, 0, v___x_1208_);
v___x_1210_ = v___x_1162_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_l_999_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_l_1151_);
v___x_1210_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
v_isSharedCheck_1217_ = !lean_is_exclusive(v_l_999_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; 
v_unused_1218_ = lean_ctor_get(v_l_999_, 4);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_l_999_, 3);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_l_999_, 2);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_l_999_, 1);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_l_999_, 0);
lean_dec(v_unused_1222_);
v___x_1212_ = v_l_999_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v_l_999_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 4, v_r_1152_);
lean_ctor_set(v___x_1212_, 3, v___x_1210_);
lean_ctor_set(v___x_1212_, 2, v_v_1150_);
lean_ctor_set(v___x_1212_, 1, v_k_1149_);
lean_ctor_set(v___x_1212_, 0, v___x_1207_);
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_r_1152_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1230_; 
v_l_1230_ = lean_ctor_get(v_impl_1145_, 3);
lean_inc(v_l_1230_);
if (lean_obj_tag(v_l_1230_) == 0)
{
lean_object* v_r_1231_; lean_object* v_k_1232_; lean_object* v_v_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1256_; 
v_r_1231_ = lean_ctor_get(v_impl_1145_, 4);
v_k_1232_ = lean_ctor_get(v_impl_1145_, 1);
v_v_1233_ = lean_ctor_get(v_impl_1145_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_impl_1145_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; lean_object* v_unused_1258_; 
v_unused_1257_ = lean_ctor_get(v_impl_1145_, 3);
lean_dec(v_unused_1257_);
v_unused_1258_ = lean_ctor_get(v_impl_1145_, 0);
lean_dec(v_unused_1258_);
v___x_1235_ = v_impl_1145_;
v_isShared_1236_ = v_isSharedCheck_1256_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_r_1231_);
lean_inc(v_v_1233_);
lean_inc(v_k_1232_);
lean_dec(v_impl_1145_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1256_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1252_; 
v_k_1237_ = lean_ctor_get(v_l_1230_, 1);
v_v_1238_ = lean_ctor_get(v_l_1230_, 2);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_l_1230_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; lean_object* v_unused_1254_; lean_object* v_unused_1255_; 
v_unused_1253_ = lean_ctor_get(v_l_1230_, 4);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_l_1230_, 3);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_l_1230_, 0);
lean_dec(v_unused_1255_);
v___x_1240_ = v_l_1230_;
v_isShared_1241_ = v_isSharedCheck_1252_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_v_1238_);
lean_inc(v_k_1237_);
lean_dec(v_l_1230_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1252_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1231_, 2);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 4, v_r_1231_);
lean_ctor_set(v___x_1240_, 3, v_r_1231_);
lean_ctor_set(v___x_1240_, 2, v_v_998_);
lean_ctor_set(v___x_1240_, 1, v_k_997_);
lean_ctor_set(v___x_1240_, 0, v___x_1146_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_r_1231_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_r_1231_);
v___x_1244_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
lean_inc(v_r_1231_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 3, v_r_1231_);
lean_ctor_set(v___x_1235_, 0, v___x_1146_);
v___x_1246_ = v___x_1235_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_k_1232_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_v_1233_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_r_1231_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_r_1231_);
v___x_1246_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1248_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v___x_1246_);
lean_ctor_set(v___x_1002_, 3, v___x_1244_);
lean_ctor_set(v___x_1002_, 2, v_v_1238_);
lean_ctor_set(v___x_1002_, 1, v_k_1237_);
lean_ctor_set(v___x_1002_, 0, v___x_1242_);
v___x_1248_ = v___x_1002_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
else
{
lean_object* v_r_1259_; 
v_r_1259_ = lean_ctor_get(v_impl_1145_, 4);
lean_inc(v_r_1259_);
if (lean_obj_tag(v_r_1259_) == 0)
{
lean_object* v_k_1260_; lean_object* v_v_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
v_k_1260_ = lean_ctor_get(v_impl_1145_, 1);
v_v_1261_ = lean_ctor_get(v_impl_1145_, 2);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_impl_1145_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; lean_object* v_unused_1274_; lean_object* v_unused_1275_; 
v_unused_1273_ = lean_ctor_get(v_impl_1145_, 4);
lean_dec(v_unused_1273_);
v_unused_1274_ = lean_ctor_get(v_impl_1145_, 3);
lean_dec(v_unused_1274_);
v_unused_1275_ = lean_ctor_get(v_impl_1145_, 0);
lean_dec(v_unused_1275_);
v___x_1263_ = v_impl_1145_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_v_1261_);
lean_inc(v_k_1260_);
lean_dec(v_impl_1145_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_unsigned_to_nat(3u);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v_l_1230_);
lean_ctor_set(v___x_1263_, 2, v_v_998_);
lean_ctor_set(v___x_1263_, 1, v_k_997_);
lean_ctor_set(v___x_1263_, 0, v___x_1146_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_l_1230_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_l_1230_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_r_1259_);
lean_ctor_set(v___x_1002_, 3, v___x_1267_);
lean_ctor_set(v___x_1002_, 2, v_v_1261_);
lean_ctor_set(v___x_1002_, 1, v_k_1260_);
lean_ctor_set(v___x_1002_, 0, v___x_1265_);
v___x_1269_ = v___x_1002_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_k_1260_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_v_1261_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_r_1259_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_unsigned_to_nat(2u);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_impl_1145_);
lean_ctor_set(v___x_1002_, 3, v_r_1259_);
lean_ctor_set(v___x_1002_, 0, v___x_1276_);
v___x_1278_ = v___x_1002_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_r_1259_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_impl_1145_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
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
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_k_993_);
lean_ctor_set(v___x_1282_, 2, v_v_994_);
lean_ctor_set(v___x_1282_, 3, v_t_995_);
lean_ctor_set(v___x_1282_, 4, v_t_995_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object* v___x_1286_, lean_object* v_as_1287_, size_t v_i_1288_, size_t v_stop_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_usize_dec_eq(v_i_1288_, v_stop_1289_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v_name_1295_; lean_object* v_kind_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_array_uget_borrowed(v_as_1287_, v_i_1288_);
v_name_1295_ = lean_ctor_get(v___x_1294_, 1);
v_kind_1296_ = lean_ctor_get(v___x_1294_, 2);
v___x_1297_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_b_1290_, v_name_1295_);
if (lean_obj_tag(v___x_1297_) == 1)
{
lean_object* v_val_1298_; lean_object* v_kind_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_b_1290_);
v_val_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v_kind_1299_ = lean_ctor_get(v_val_1298_, 2);
lean_inc(v_kind_1299_);
lean_dec(v_val_1298_);
v___x_1300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0));
v___x_1301_ = lean_string_append(v___x_1286_, v___x_1300_);
v___x_1302_ = 1;
lean_inc(v_name_1295_);
v___x_1303_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1295_, v___x_1302_);
v___x_1304_ = lean_string_append(v___x_1301_, v___x_1303_);
lean_dec_ref(v___x_1303_);
v___x_1305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1));
v___x_1306_ = lean_string_append(v___x_1304_, v___x_1305_);
v___x_1307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1299_, v___x_1302_);
v___x_1308_ = lean_string_append(v___x_1306_, v___x_1307_);
lean_dec_ref(v___x_1307_);
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2));
v___x_1310_ = lean_string_append(v___x_1308_, v___x_1309_);
lean_inc(v_kind_1296_);
v___x_1311_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1296_, v___x_1302_);
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1314_ = lean_string_append(v___x_1312_, v___x_1313_);
v___x_1315_ = 3;
v___x_1316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*1, v___x_1315_);
v___x_1317_ = lean_array_get_size(v___y_1291_);
v___x_1318_ = lean_array_push(v___y_1291_, v___x_1316_);
v___x_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; 
lean_dec(v___x_1297_);
lean_inc(v___x_1294_);
lean_inc(v_name_1295_);
v___x_1320_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_name_1295_, v___x_1294_, v_b_1290_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_add(v_i_1288_, v___x_1321_);
v_i_1288_ = v___x_1322_;
v_b_1290_ = v___x_1320_;
goto _start;
}
}
else
{
lean_object* v___x_1324_; 
lean_dec_ref(v___x_1286_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_b_1290_);
lean_ctor_set(v___x_1324_, 1, v___y_1291_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object* v___x_1325_, lean_object* v_as_1326_, lean_object* v_i_1327_, lean_object* v_stop_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_i_boxed_1332_; size_t v_stop_boxed_1333_; lean_object* v_res_1334_; 
v_i_boxed_1332_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_stop_boxed_1333_ = lean_unbox_usize(v_stop_1328_);
lean_dec(v_stop_1328_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1325_, v_as_1326_, v_i_boxed_1332_, v_stop_boxed_1333_, v_b_1329_, v___y_1330_);
lean_dec_ref(v_as_1326_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1341_, lean_object* v_opts_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_a_1346_; lean_object* v_a_1347_; lean_object* v_a_1350_; lean_object* v_a_1351_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_inc_ref(v_env_1341_);
v___x_1353_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1341_, v_opts_1342_);
v___x_1354_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1342_);
lean_inc_ref_n(v_env_1341_, 2);
v___f_1357_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1357_, 0, v_env_1341_);
lean_closure_set(v___f_1357_, 1, v_opts_1342_);
lean_closure_set(v___f_1357_, 2, v___x_1356_);
v___x_1358_ = l_Lake_targetAttr;
v___x_1359_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1341_, v___x_1358_, v___f_1357_);
v___x_1360_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_baseName_1362_; lean_object* v_keyName_1363_; lean_object* v_config_1364_; lean_object* v_toArray_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_baseName_1362_ = lean_ctor_get(v_a_1355_, 0);
v_keyName_1363_ = lean_ctor_get(v_a_1355_, 1);
v_config_1364_ = lean_ctor_get(v_a_1355_, 3);
v_toArray_1365_ = lean_ctor_get(v_a_1361_, 1);
v_sz_1366_ = lean_array_size(v_toArray_1365_);
v___x_1367_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1365_);
lean_inc(v_keyName_1363_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v_keyName_1363_, v_sz_1366_, v___x_1367_, v_toArray_1365_, v_a_1343_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1637_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_a_1370_ = lean_ctor_get(v___x_1368_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1372_ = v___x_1368_;
v_isShared_1373_ = v_isSharedCheck_1637_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1637_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v_a_1415_; lean_object* v_a_1416_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v_a_1440_; lean_object* v_a_1441_; lean_object* v___y_1479_; lean_object* v_a_1480_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___x_1608_; lean_object* v_a_1610_; lean_object* v_a_1611_; lean_object* v___y_1619_; uint8_t v___x_1631_; 
v___x_1400_ = l_Lake_instTypeNameScriptFn;
v___x_1401_ = 0;
lean_inc(v_baseName_1362_);
v___x_1402_ = l_Lean_Name_toString(v_baseName_1362_, v___x_1401_);
v___x_1403_ = lean_box(v___x_1401_);
lean_inc_ref(v___x_1402_);
lean_inc_ref(v_opts_1342_);
lean_inc_ref(v_env_1341_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1404_, 0, v___x_1403_);
lean_closure_set(v___f_1404_, 1, v_env_1341_);
lean_closure_set(v___f_1404_, 2, v_opts_1342_);
lean_closure_set(v___f_1404_, 3, v___x_1400_);
lean_closure_set(v___f_1404_, 4, v___x_1402_);
v___x_1405_ = lean_box(1);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1608_ = lean_array_get_size(v_a_1369_);
v___x_1631_ = lean_nat_dec_lt(v___x_1406_, v___x_1608_);
if (v___x_1631_ == 0)
{
v_a_1610_ = v___x_1405_;
v_a_1611_ = v_a_1370_;
goto v___jp_1609_;
}
else
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_le(v___x_1608_, v___x_1608_);
if (v___x_1632_ == 0)
{
if (v___x_1631_ == 0)
{
v_a_1610_ = v___x_1405_;
v_a_1611_ = v_a_1370_;
goto v___jp_1609_;
}
else
{
size_t v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_usize_of_nat(v___x_1608_);
lean_inc_ref(v___x_1402_);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1402_, v_a_1369_, v___x_1367_, v___x_1633_, v___x_1405_, v_a_1370_);
v___y_1619_ = v___x_1634_;
goto v___jp_1618_;
}
}
else
{
size_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_usize_of_nat(v___x_1608_);
lean_inc_ref(v___x_1402_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1402_, v_a_1369_, v___x_1367_, v___x_1635_, v___x_1405_, v_a_1370_);
v___y_1619_ = v___x_1636_;
goto v___jp_1618_;
}
}
v___jp_1374_:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1355_);
lean_ctor_set(v___x_1387_, 1, v___y_1379_);
lean_ctor_set(v___x_1387_, 2, v_a_1386_);
lean_ctor_set(v___x_1387_, 3, v_a_1369_);
lean_ctor_set(v___x_1387_, 4, v___y_1383_);
lean_ctor_set(v___x_1387_, 5, v___y_1382_);
lean_ctor_set(v___x_1387_, 6, v___y_1377_);
lean_ctor_set(v___x_1387_, 7, v___y_1378_);
lean_ctor_set(v___x_1387_, 8, v___y_1376_);
lean_ctor_set(v___x_1387_, 9, v___y_1381_);
lean_ctor_set(v___x_1387_, 10, v___y_1375_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___y_1380_);
lean_ctor_set(v___x_1372_, 0, v___x_1387_);
v___x_1389_ = v___x_1372_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___y_1380_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1355_);
v_a_1391_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1392_ = lean_io_error_to_string(v_a_1391_);
v___x_1393_ = 3;
v___x_1394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*1, v___x_1393_);
v___x_1395_ = lean_array_get_size(v___y_1380_);
v___x_1396_ = lean_array_push(v___y_1380_, v___x_1394_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 1);
lean_ctor_set(v___x_1372_, 1, v___x_1396_);
lean_ctor_set(v___x_1372_, 0, v___x_1395_);
v___x_1398_ = v___x_1372_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; lean_object* v___x_1421_; 
v___x_1417_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1418_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1341_, 2);
v___x_1419_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1418_, v_env_1341_);
v_sz_1420_ = lean_array_size(v___x_1419_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1341_, v_opts_1342_, v___x_1419_, v_sz_1420_, v___x_1367_, v___x_1417_);
lean_dec_ref(v___x_1419_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v___y_1375_ = v_a_1415_;
v___y_1376_ = v___y_1409_;
v___y_1377_ = v___y_1408_;
v___y_1378_ = v___y_1411_;
v___y_1379_ = v___y_1410_;
v___y_1380_ = v_a_1416_;
v___y_1381_ = v___y_1412_;
v___y_1382_ = v___y_1414_;
v___y_1383_ = v___y_1413_;
v___y_1384_ = v___x_1421_;
goto v___jp_1374_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; lean_object* v___x_1426_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1341_, 2);
v___x_1424_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1423_, v_env_1341_);
v_sz_1425_ = lean_array_size(v___x_1424_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1341_, v_opts_1342_, v___x_1424_, v_sz_1425_, v___x_1367_, v_a_1422_);
lean_dec_ref(v___x_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v___y_1375_ = v_a_1415_;
v___y_1376_ = v___y_1409_;
v___y_1377_ = v___y_1408_;
v___y_1378_ = v___y_1411_;
v___y_1379_ = v___y_1410_;
v___y_1380_ = v_a_1416_;
v___y_1381_ = v___y_1412_;
v___y_1382_ = v___y_1414_;
v___y_1383_ = v___y_1413_;
v___y_1384_ = v___x_1426_;
goto v___jp_1374_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; size_t v_sz_1430_; lean_object* v___x_1431_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1341_);
v___x_1429_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1428_, v_env_1341_);
v_sz_1430_ = lean_array_size(v___x_1429_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1341_, v_opts_1342_, v___x_1429_, v_sz_1430_, v___x_1367_, v_a_1427_);
lean_dec_ref(v___x_1429_);
lean_dec_ref(v_opts_1342_);
v___y_1375_ = v_a_1415_;
v___y_1376_ = v___y_1409_;
v___y_1377_ = v___y_1408_;
v___y_1378_ = v___y_1411_;
v___y_1379_ = v___y_1410_;
v___y_1380_ = v_a_1416_;
v___y_1381_ = v___y_1412_;
v___y_1382_ = v___y_1414_;
v___y_1383_ = v___y_1413_;
v___y_1384_ = v___x_1431_;
goto v___jp_1374_;
}
}
}
v___jp_1432_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; size_t v_sz_1444_; lean_object* v___x_1445_; 
v___x_1442_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1341_);
v___x_1443_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1442_, v_env_1341_);
v_sz_1444_ = lean_array_size(v___x_1443_);
lean_inc_ref(v___x_1402_);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1361_, v___y_1434_, v___x_1402_, v_sz_1444_, v___x_1367_, v___x_1443_, v_a_1441_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1445_, 2);
v___x_1448_ = lean_array_get_size(v_a_1446_);
v___x_1449_ = lean_nat_dec_lt(v___y_1435_, v___x_1448_);
if (v___x_1449_ == 0)
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_nat_dec_lt(v___x_1406_, v___x_1448_);
if (v___x_1450_ == 0)
{
lean_object* v_lintDriver_1451_; 
lean_dec(v_a_1446_);
lean_dec_ref(v___x_1402_);
v_lintDriver_1451_ = lean_ctor_get(v_config_1364_, 14);
lean_inc_ref(v_lintDriver_1451_);
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1437_;
v___y_1411_ = v___y_1436_;
v___y_1412_ = v_a_1440_;
v___y_1413_ = v___y_1439_;
v___y_1414_ = v___y_1438_;
v_a_1415_ = v_lintDriver_1451_;
v_a_1416_ = v_a_1447_;
goto v___jp_1407_;
}
else
{
lean_object* v_lintDriver_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_lintDriver_1452_ = lean_ctor_get(v_config_1364_, 14);
v___x_1453_ = lean_string_utf8_byte_size(v_lintDriver_1452_);
v___x_1454_ = lean_nat_dec_eq(v___x_1453_, v___x_1406_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v___x_1455_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1456_ = lean_string_append(v___x_1402_, v___x_1455_);
v___x_1457_ = 3;
v___x_1458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*1, v___x_1457_);
v___x_1459_ = lean_array_get_size(v_a_1447_);
v___x_1460_ = lean_array_push(v_a_1447_, v___x_1458_);
v_a_1350_ = v___x_1459_;
v_a_1351_ = v___x_1460_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v___x_1402_);
v___x_1461_ = lean_array_fget(v_a_1446_, v___x_1406_);
lean_dec(v_a_1446_);
v___x_1462_ = l_Lean_Name_toString(v___x_1461_, v___x_1450_);
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1437_;
v___y_1411_ = v___y_1436_;
v___y_1412_ = v_a_1440_;
v___y_1413_ = v___y_1439_;
v___y_1414_ = v___y_1438_;
v_a_1415_ = v___x_1462_;
v_a_1416_ = v_a_1447_;
goto v___jp_1407_;
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v___x_1463_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1464_ = lean_string_append(v___x_1402_, v___x_1463_);
v___x_1465_ = 3;
v___x_1466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set_uint8(v___x_1466_, sizeof(void*)*1, v___x_1465_);
v___x_1467_ = lean_array_get_size(v_a_1447_);
v___x_1468_ = lean_array_push(v_a_1447_, v___x_1466_);
v_a_1350_ = v___x_1467_;
v_a_1351_ = v___x_1468_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1469_; lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_a_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1469_ = lean_ctor_get(v___x_1445_, 0);
v_a_1470_ = lean_ctor_get(v___x_1445_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1445_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_inc(v_a_1469_);
lean_dec(v___x_1445_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1469_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
v___jp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; lean_object* v___x_1484_; 
v___x_1481_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1341_);
v___x_1482_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1481_, v_env_1341_);
v_sz_1483_ = lean_array_size(v___x_1482_);
lean_inc_ref(v___x_1402_);
lean_inc(v_a_1361_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1361_, v___x_1402_, v_sz_1483_, v___x_1367_, v___x_1482_, v_a_1480_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
v_a_1486_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1484_, 2);
v___x_1487_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1341_);
v___x_1488_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1341_, v___x_1487_, v___f_1404_, v_a_1486_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v_a_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; size_t v_sz_1493_; lean_object* v___x_1494_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
v_a_1490_ = lean_ctor_get(v___x_1488_, 1);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1488_, 2);
v___x_1491_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1341_);
v___x_1492_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1491_, v_env_1341_);
v_sz_1493_ = lean_array_size(v___x_1492_);
lean_inc_ref(v___x_1402_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1489_, v___x_1402_, v_sz_1493_, v___x_1367_, v___x_1492_, v_a_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; size_t v_sz_1499_; lean_object* v___x_1500_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
v_a_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1494_, 2);
v___x_1497_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1341_, 2);
v___x_1498_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1497_, v_env_1341_);
v_sz_1499_ = lean_array_size(v___x_1498_);
lean_inc(v_keyName_1363_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1341_, v_opts_1342_, v_keyName_1363_, v_sz_1499_, v___x_1367_, v___x_1498_, v_a_1496_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1558_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1504_ = v___x_1500_;
v_isShared_1505_ = v_isSharedCheck_1558_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1558_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; size_t v_sz_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1506_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1341_, 2);
v___x_1507_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1506_, v_env_1341_);
v_sz_1508_ = lean_array_size(v___x_1507_);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1341_, v_opts_1342_, v_sz_1508_, v___x_1367_, v___x_1507_);
v___x_1510_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1509_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; size_t v_sz_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1504_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1341_);
v___x_1513_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1512_, v_env_1341_);
v_sz_1514_ = lean_array_size(v___x_1513_);
lean_inc_ref(v___x_1402_);
lean_inc(v_a_1361_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1361_, v_a_1489_, v___x_1402_, v_sz_1514_, v___x_1367_, v___x_1513_, v_a_1502_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
v_a_1517_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1515_, 2);
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_array_get_size(v_a_1516_);
v___x_1520_ = lean_nat_dec_lt(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_nat_dec_lt(v___x_1406_, v___x_1519_);
if (v___x_1521_ == 0)
{
lean_object* v_testDriver_1522_; 
lean_dec(v_a_1516_);
v_testDriver_1522_ = lean_ctor_get(v_config_1364_, 12);
lean_inc_ref(v_testDriver_1522_);
v___y_1433_ = v_a_1501_;
v___y_1434_ = v_a_1489_;
v___y_1435_ = v___x_1518_;
v___y_1436_ = v_a_1495_;
v___y_1437_ = v_a_1511_;
v___y_1438_ = v_a_1485_;
v___y_1439_ = v___y_1479_;
v_a_1440_ = v_testDriver_1522_;
v_a_1441_ = v_a_1517_;
goto v___jp_1432_;
}
else
{
lean_object* v_testDriver_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_testDriver_1523_ = lean_ctor_get(v_config_1364_, 12);
v___x_1524_ = lean_string_utf8_byte_size(v_testDriver_1523_);
v___x_1525_ = lean_nat_dec_eq(v___x_1524_, v___x_1406_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_a_1516_);
lean_dec(v_a_1511_);
lean_dec(v_a_1501_);
lean_dec(v_a_1495_);
lean_dec(v_a_1489_);
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v___x_1526_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1527_ = lean_string_append(v___x_1402_, v___x_1526_);
v___x_1528_ = 3;
v___x_1529_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*1, v___x_1528_);
v___x_1530_ = lean_array_get_size(v_a_1517_);
v___x_1531_ = lean_array_push(v_a_1517_, v___x_1529_);
v_a_1346_ = v___x_1530_;
v_a_1347_ = v___x_1531_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_array_fget(v_a_1516_, v___x_1406_);
lean_dec(v_a_1516_);
v___x_1533_ = l_Lean_Name_toString(v___x_1532_, v___x_1521_);
v___y_1433_ = v_a_1501_;
v___y_1434_ = v_a_1489_;
v___y_1435_ = v___x_1518_;
v___y_1436_ = v_a_1495_;
v___y_1437_ = v_a_1511_;
v___y_1438_ = v_a_1485_;
v___y_1439_ = v___y_1479_;
v_a_1440_ = v___x_1533_;
v_a_1441_ = v_a_1517_;
goto v___jp_1432_;
}
}
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_a_1516_);
lean_dec(v_a_1511_);
lean_dec(v_a_1501_);
lean_dec(v_a_1495_);
lean_dec(v_a_1489_);
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v___x_1534_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1535_ = lean_string_append(v___x_1402_, v___x_1534_);
v___x_1536_ = 3;
v___x_1537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*1, v___x_1536_);
v___x_1538_ = lean_array_get_size(v_a_1517_);
v___x_1539_ = lean_array_push(v_a_1517_, v___x_1537_);
v_a_1346_ = v___x_1538_;
v_a_1347_ = v___x_1539_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1540_; lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1511_);
lean_dec(v_a_1501_);
lean_dec(v_a_1495_);
lean_dec(v_a_1489_);
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1540_ = lean_ctor_get(v___x_1515_, 0);
v_a_1541_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1515_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_inc(v_a_1540_);
lean_dec(v___x_1515_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1540_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_dec(v_a_1501_);
lean_dec(v_a_1495_);
lean_dec(v_a_1489_);
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1549_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1550_ = lean_io_error_to_string(v_a_1549_);
v___x_1551_ = 3;
v___x_1552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*1, v___x_1551_);
v___x_1553_ = lean_array_get_size(v_a_1502_);
v___x_1554_ = lean_array_push(v_a_1502_, v___x_1552_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 1);
lean_ctor_set(v___x_1504_, 1, v___x_1554_);
lean_ctor_set(v___x_1504_, 0, v___x_1553_);
v___x_1556_ = v___x_1504_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1554_);
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
lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_a_1495_);
lean_dec(v_a_1489_);
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1559_ = lean_ctor_get(v___x_1500_, 0);
v_a_1560_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1500_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_inc(v_a_1559_);
lean_dec(v___x_1500_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1559_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1489_);
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1568_ = lean_ctor_get(v___x_1494_, 0);
v_a_1569_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1494_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_inc(v_a_1568_);
lean_dec(v___x_1494_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1568_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1485_);
lean_dec(v___y_1479_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1577_ = lean_ctor_get(v___x_1488_, 0);
v_a_1578_ = lean_ctor_get(v___x_1488_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1488_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_inc(v_a_1577_);
lean_dec(v___x_1488_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v___y_1479_);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1586_ = lean_ctor_get(v___x_1484_, 0);
v_a_1587_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1484_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1484_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
v___jp_1595_:
{
if (lean_obj_tag(v___y_1597_) == 0)
{
lean_object* v_a_1598_; 
v_a_1598_ = lean_ctor_get(v___y_1597_, 1);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___y_1597_, 2);
v___y_1479_ = v___y_1596_;
v_a_1480_ = v_a_1598_;
goto v___jp_1478_;
}
else
{
lean_object* v_a_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v___y_1596_);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1599_ = lean_ctor_get(v___y_1597_, 0);
v_a_1600_ = lean_ctor_get(v___y_1597_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___y_1597_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___y_1597_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_inc(v_a_1599_);
lean_dec(v___y_1597_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1599_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
v___jp_1609_:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_nat_dec_lt(v___x_1406_, v___x_1608_);
if (v___x_1612_ == 0)
{
v___y_1479_ = v_a_1610_;
v_a_1480_ = v_a_1611_;
goto v___jp_1478_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_le(v___x_1608_, v___x_1608_);
if (v___x_1613_ == 0)
{
if (v___x_1612_ == 0)
{
v___y_1479_ = v_a_1610_;
v_a_1480_ = v_a_1611_;
goto v___jp_1478_;
}
else
{
size_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_usize_of_nat(v___x_1608_);
lean_inc_ref(v___x_1402_);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1402_, v_a_1369_, v___x_1367_, v___x_1614_, v___x_1405_, v_a_1611_);
v___y_1596_ = v_a_1610_;
v___y_1597_ = v___x_1615_;
goto v___jp_1595_;
}
}
else
{
size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_usize_of_nat(v___x_1608_);
lean_inc_ref(v___x_1402_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1402_, v_a_1369_, v___x_1367_, v___x_1616_, v___x_1405_, v_a_1611_);
v___y_1596_ = v_a_1610_;
v___y_1597_ = v___x_1617_;
goto v___jp_1595_;
}
}
}
v___jp_1618_:
{
if (lean_obj_tag(v___y_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_a_1621_; 
v_a_1620_ = lean_ctor_get(v___y_1619_, 0);
lean_inc(v_a_1620_);
v_a_1621_ = lean_ctor_get(v___y_1619_, 1);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___y_1619_, 2);
v_a_1610_ = v_a_1620_;
v_a_1611_ = v_a_1621_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1372_);
lean_dec(v_a_1369_);
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1622_ = lean_ctor_get(v___y_1619_, 0);
v_a_1623_ = lean_ctor_get(v___y_1619_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___y_1619_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___y_1619_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_inc(v_a_1622_);
lean_dec(v___y_1619_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1622_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_a_1361_);
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1638_ = lean_ctor_get(v___x_1368_, 0);
v_a_1639_ = lean_ctor_get(v___x_1368_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1368_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_inc(v_a_1638_);
lean_dec(v___x_1368_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1638_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec(v_a_1355_);
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1647_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1648_ = lean_io_error_to_string(v_a_1647_);
v___x_1649_ = 3;
v___x_1650_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set_uint8(v___x_1650_, sizeof(void*)*1, v___x_1649_);
v___x_1651_ = lean_array_get_size(v_a_1343_);
v___x_1652_ = lean_array_push(v_a_1343_, v___x_1650_);
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
return v___x_1653_;
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec_ref(v_opts_1342_);
lean_dec_ref(v_env_1341_);
v_a_1654_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1655_ = lean_io_error_to_string(v_a_1654_);
v___x_1656_ = 3;
v___x_1657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set_uint8(v___x_1657_, sizeof(void*)*1, v___x_1656_);
v___x_1658_ = lean_array_get_size(v_a_1343_);
v___x_1659_ = lean_array_push(v_a_1343_, v___x_1657_);
v___x_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
return v___x_1660_;
}
v___jp_1345_:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1346_);
lean_ctor_set(v___x_1348_, 1, v_a_1347_);
return v___x_1348_;
}
v___jp_1349_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1350_);
lean_ctor_set(v___x_1352_, 1, v_a_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1661_, lean_object* v_opts_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1661_, v_opts_1662_, v_a_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1666_, lean_object* v_env_1667_, lean_object* v_attr_1668_, lean_object* v_f_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_1667_, v_attr_1668_, v_f_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1671_, lean_object* v_env_1672_, lean_object* v_attr_1673_, lean_object* v_f_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1671_, v_env_1672_, v_attr_1673_, v_f_1674_);
lean_dec_ref(v_attr_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1676_, lean_object* v_inst_1677_, lean_object* v_t_1678_, lean_object* v_k_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_1678_, v_k_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_inst_1682_, lean_object* v_t_1683_, lean_object* v_k_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1681_, v_inst_1682_, v_t_1683_, v_k_1684_);
lean_dec(v_k_1684_);
lean_dec(v_t_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v_00_u03b2_1686_, lean_object* v_k_1687_, lean_object* v_v_1688_, lean_object* v_t_1689_, lean_object* v_hl_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_1687_, v_v_1688_, v_t_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1692_, lean_object* v_t_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1693_, v_k_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1696_, lean_object* v_t_1697_, lean_object* v_k_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1696_, v_t_1697_, v_k_1698_);
lean_dec(v_k_1698_);
lean_dec(v_t_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1700_, lean_object* v_env_1701_, lean_object* v_attr_1702_, lean_object* v_f_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1701_, v_attr_1702_, v_f_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1707_, lean_object* v_env_1708_, lean_object* v_attr_1709_, lean_object* v_f_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1707_, v_env_1708_, v_attr_1709_, v_f_1710_, v___y_1711_);
lean_dec_ref(v_attr_1709_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_1714_, lean_object* v___x_1715_, lean_object* v_as_1716_, size_t v_i_1717_, size_t v_stop_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1714_, v_as_1716_, v_i_1717_, v_stop_1718_, v_b_1719_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_1723_, lean_object* v___x_1724_, lean_object* v_as_1725_, lean_object* v_i_1726_, lean_object* v_stop_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
size_t v_i_boxed_1731_; size_t v_stop_boxed_1732_; lean_object* v_res_1733_; 
v_i_boxed_1731_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_stop_boxed_1732_ = lean_unbox_usize(v_stop_1727_);
lean_dec(v_stop_1727_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1723_, v___x_1724_, v_as_1725_, v_i_boxed_1731_, v_stop_boxed_1732_, v_b_1728_, v___y_1729_);
lean_dec_ref(v_as_1725_);
lean_dec(v___x_1724_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(lean_object* v_00_u03b2_1734_, lean_object* v_f_1735_, lean_object* v_as_1736_, size_t v_i_1737_, size_t v_stop_1738_, lean_object* v_b_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_1735_, v_as_1736_, v_i_1737_, v_stop_1738_, v_b_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1741_, lean_object* v_f_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_stop_1745_, lean_object* v_b_1746_){
_start:
{
size_t v_i_boxed_1747_; size_t v_stop_boxed_1748_; lean_object* v_res_1749_; 
v_i_boxed_1747_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_stop_boxed_1748_ = lean_unbox_usize(v_stop_1745_);
lean_dec(v_stop_1745_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(v_00_u03b2_1741_, v_f_1742_, v_as_1743_, v_i_boxed_1747_, v_stop_boxed_1748_, v_b_1746_);
lean_dec_ref(v_as_1743_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1750_, lean_object* v_f_1751_, lean_object* v_as_1752_, size_t v_i_1753_, size_t v_stop_1754_, lean_object* v_b_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1751_, v_as_1752_, v_i_1753_, v_stop_1754_, v_b_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1759_, lean_object* v_f_1760_, lean_object* v_as_1761_, lean_object* v_i_1762_, lean_object* v_stop_1763_, lean_object* v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_i_boxed_1767_; size_t v_stop_boxed_1768_; lean_object* v_res_1769_; 
v_i_boxed_1767_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_stop_boxed_1768_ = lean_unbox_usize(v_stop_1763_);
lean_dec(v_stop_1763_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1759_, v_f_1760_, v_as_1761_, v_i_boxed_1767_, v_stop_boxed_1768_, v_b_1764_, v___y_1765_);
lean_dec_ref(v_as_1761_);
return v_res_1769_;
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
